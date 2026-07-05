/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.RungeKutta

/-!
# The substitution law and backward error analysis

The **substitution law** of B-series (Chartier–Hairer–Vilmart): a
coefficient system `b` on trees (a "vector field series") substitutes
into a B-series `a` by summing over all **partitions** of each tree
into subtree blocks — `b` evaluated on the blocks, `a` on the tree
obtained by contracting each block to a vertex:

`(b ⋆ a)(τ) = ∑_{p ∈ partitions τ} b(root block)·∏ b(blocks)·a(τ/p)`.

Partitions of a planar tree correspond to subsets of its edges (the
kept edges span the blocks); `partitionTriples` enumerates them
recursively as triples `(root block, other blocks, skeleton)`, choosing
for each edge whether to *keep* it (child block merges into the parent
block) or *cut* it (child block separates, contributing a vertex to the
skeleton).

**Backward error analysis** is the inversion of substitution along a
fixed unital series `e` (in applications, the exact flow): every
consistent `a` is `b ⋆ e` for a unique modified series `b`
(`modifiedCoeff`, `substCoeff_modifiedCoeff`, `modifiedCoeff_unique`) —
the numerical method `a` is the `e`-flow of the modified vector field
`b`. The inversion is by strong induction on the tree order, using
that every non-trivial partition has all blocks of strictly smaller
order (`partitionTriples_tail_order_lt`).
-/

namespace BSeries

open HopfAlgebras

universe v

variable {R : Type v}

/-! ### Partitions of a planar tree -/

mutual

/-- All edge-subset partitions of a tree, as triples
`(root block, other blocks, skeleton)`. The first triple is always the
trivial partition (no edge cut). -/
def partitionTriples : PTree → List (PTree × List PTree × PTree)
  | .node ts =>
      (partitionCombine ts).map fun rbs =>
        (.node rbs.1, rbs.2.1, .node rbs.2.2)

/-- Process the children of a vertex: for each child and each partition
of it, either **keep** the connecting edge (the child's root block
becomes a branch of the parent's block, the child's skeleton root merges
into the parent's skeleton vertex) or **cut** it (the child's root block
becomes a separate block, its skeleton hangs off the parent's skeleton
vertex). Returns `(root-block branches, other blocks, skeleton
branches)`. -/
def partitionCombine : List PTree → List (List PTree × List PTree × List PTree)
  | [] => [([], [], [])]
  | c :: cs =>
      (partitionTriples c).flatMap fun t =>
        (partitionCombine cs).flatMap fun rest =>
          [(t.1 :: rest.1, t.2.1 ++ rest.2.1, t.2.2.children ++ rest.2.2),
           (rest.1, t.1 :: (t.2.1 ++ rest.2.1), t.2.2 :: rest.2.2)]

end

@[simp]
theorem partitionTriples_node (ts : List PTree) :
    partitionTriples (.node ts) =
      (partitionCombine ts).map fun rbs =>
        (.node rbs.1, rbs.2.1, .node rbs.2.2) :=
  rfl

@[simp]
theorem partitionCombine_nil :
    partitionCombine ([] : List PTree) = [([], [], [])] :=
  rfl

theorem partitionCombine_cons (c : PTree) (cs : List PTree) :
    partitionCombine (c :: cs) =
      (partitionTriples c).flatMap fun t =>
        (partitionCombine cs).flatMap fun rest =>
          [(t.1 :: rest.1, t.2.1 ++ rest.2.1, t.2.2.children ++ rest.2.2),
           (rest.1, t.1 :: (t.2.1 ++ rest.2.1), t.2.2 :: rest.2.2)] :=
  rfl

/-! ### Structural lemmas -/

mutual

/-- The head of the partition list is the trivial partition. -/
theorem partitionTriples_head :
    ∀ t : PTree, (partitionTriples t).head? = some (t, [], .node [])
  | .node ts => by
      rw [partitionTriples_node]
      rcases hcomb : partitionCombine ts with _ | ⟨head, tail⟩
      · have := partitionCombine_head ts
        rw [hcomb] at this
        cases this
      · have := partitionCombine_head ts
        rw [hcomb] at this
        simp only [List.head?_cons, Option.some.injEq] at this
        simp [this]

theorem partitionCombine_head :
    ∀ ts : List PTree,
      (partitionCombine ts).head? = some (ts, [], [])
  | [] => rfl
  | c :: cs => by
      rw [partitionCombine_cons]
      have hc := partitionTriples_head c
      have hcs := partitionCombine_head cs
      rcases hpt : partitionTriples c with _ | ⟨tc, _⟩
      · rw [hpt] at hc; cases hc
      · rw [hpt] at hc
        simp only [List.head?_cons, Option.some.injEq] at hc
        rcases hpc : partitionCombine cs with _ | ⟨rc, _⟩
        · rw [hpc] at hcs; cases hcs
        · rw [hpc] at hcs
          simp only [List.head?_cons, Option.some.injEq] at hcs
          subst hc
          subst hcs
          simp

end

/-- Every tree's partition list is nonempty, headed by the trivial
partition. -/
theorem partitionTriples_eq_cons (t : PTree) :
    partitionTriples t = (t, [], .node []) :: (partitionTriples t).tail := by
  have h := partitionTriples_head t
  rcases hpt : partitionTriples t with _ | ⟨head, tail⟩
  · rw [hpt] at h; cases h
  · rw [hpt] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    rw [h]
    rfl

mutual

/-- Partitions preserve total order: the blocks partition the vertices. -/
theorem partitionTriples_order :
    ∀ t : PTree, ∀ tr ∈ partitionTriples t,
      PTree.order tr.1 + PTree.orderList tr.2.1 = PTree.order t
  | .node ts, tr, htr => by
      rw [partitionTriples_node] at htr
      obtain ⟨rbs, hmem, rfl⟩ := List.mem_map.mp htr
      have h := partitionCombine_order ts rbs hmem
      have h1 := PTree.order_eq_one_add_orderList_children (PTree.node rbs.1)
      have h2 := PTree.order_eq_one_add_orderList_children (PTree.node ts)
      rw [show (PTree.node rbs.1).children = rbs.1 from rfl] at h1
      rw [show (PTree.node ts).children = ts from rfl] at h2
      show PTree.order (PTree.node rbs.1) + PTree.orderList rbs.2.1 =
        PTree.order (PTree.node ts)
      omega

theorem partitionCombine_order :
    ∀ ts : List PTree, ∀ rbs ∈ partitionCombine ts,
      PTree.orderList rbs.1 + PTree.orderList rbs.2.1 =
        PTree.orderList ts
  | [], rbs, hmem => by
      simp only [partitionCombine_nil, List.mem_singleton] at hmem
      rw [hmem]
      rfl
  | c :: cs, rbs, hmem => by
      rw [partitionCombine_cons] at hmem
      obtain ⟨t, ht, hmem⟩ := List.mem_flatMap.mp hmem
      obtain ⟨rest, hrest, hmem⟩ := List.mem_flatMap.mp hmem
      have hc := partitionTriples_order c t ht
      have hcs := partitionCombine_order cs rest hrest
      rcases List.mem_cons.mp hmem with h | h
      · rw [h]
        show PTree.orderList (t.1 :: rest.1) +
          PTree.orderList (t.2.1 ++ rest.2.1) = PTree.orderList (c :: cs)
        rw [PTree.orderList_cons, PTree.orderList_append,
          PTree.orderList_cons]
        omega
      · rw [List.mem_singleton.mp h]
        show PTree.orderList rest.1 +
          PTree.orderList (t.1 :: (t.2.1 ++ rest.2.1)) =
          PTree.orderList (c :: cs)
        rw [PTree.orderList_cons, PTree.orderList_append,
          PTree.orderList_cons]
        omega

end

/-! ### Non-trivial partitions have small blocks -/

private theorem sum_flatMap {A B : Type*} {M : Type*} [AddCommMonoid M]
    (l : List A) (f : A → List B) (g : B → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
        List.map_cons, List.sum_cons]

mutual

/-- Exactly one partition — the trivial one — has no separated blocks. -/
theorem obsEmptySum_partitionTriples :
    ∀ t : PTree,
      ((partitionTriples t).map fun tr =>
        if tr.2.1.isEmpty then (1 : ℕ) else 0).sum = 1
  | .node ts => by
      rw [partitionTriples_node, List.map_map]
      exact obsEmptySum_partitionCombine ts

theorem obsEmptySum_partitionCombine :
    ∀ ts : List PTree,
      ((partitionCombine ts).map fun rbs =>
        if rbs.2.1.isEmpty then (1 : ℕ) else 0).sum = 1
  | [] => rfl
  | c :: cs => by
      rw [partitionCombine_cons, sum_flatMap]
      have hstep : ∀ t ∈ partitionTriples c,
          (((partitionCombine cs).flatMap fun rest =>
            [(t.1 :: rest.1, t.2.1 ++ rest.2.1,
                t.2.2.children ++ rest.2.2),
             (rest.1, t.1 :: (t.2.1 ++ rest.2.1),
                t.2.2 :: rest.2.2)]).map fun rbs =>
              if rbs.2.1.isEmpty then (1 : ℕ) else 0).sum =
          (if t.2.1.isEmpty then (1 : ℕ) else 0) *
            ((partitionCombine cs).map fun rest =>
              if rest.2.1.isEmpty then (1 : ℕ) else 0).sum := by
        intro t _
        rw [sum_flatMap]
        have hper : ∀ rest ∈ partitionCombine cs,
            (([(t.1 :: rest.1, t.2.1 ++ rest.2.1,
                t.2.2.children ++ rest.2.2),
              (rest.1, t.1 :: (t.2.1 ++ rest.2.1),
                t.2.2 :: rest.2.2)].map fun rbs =>
                if rbs.2.1.isEmpty then (1 : ℕ) else 0)).sum =
            (if t.2.1.isEmpty then (1 : ℕ) else 0) *
              (if rest.2.1.isEmpty then (1 : ℕ) else 0) := by
          intro rest _
          show (if (t.2.1 ++ rest.2.1).isEmpty then (1 : ℕ) else 0) +
            ((if (t.1 :: (t.2.1 ++ rest.2.1)).isEmpty then (1 : ℕ)
              else 0) + 0) = _
          rcases ht : t.2.1 with _ | ⟨o, os⟩
          · rcases hr : rest.2.1 with _ | ⟨r, rs⟩
            · simp
            · simp
          · rcases hr : rest.2.1 with _ | ⟨r, rs⟩
            · simp
            · simp
        rw [List.map_congr_left hper, List.sum_map_mul_left]
      rw [List.map_congr_left hstep, List.sum_map_mul_right,
        obsEmptySum_partitionTriples c, obsEmptySum_partitionCombine cs,
        one_mul]

end

/-- Every non-trivial partition separates at least one block. -/
theorem tail_obs_ne_nil {t : PTree} {tr : PTree × List PTree × PTree}
    (htr : tr ∈ (partitionTriples t).tail) : tr.2.1 ≠ [] := by
  intro hobs
  have hsum := obsEmptySum_partitionTriples t
  rw [partitionTriples_eq_cons t, List.map_cons, List.sum_cons] at hsum
  have hhead : (if ([] : List PTree).isEmpty then (1 : ℕ) else 0) = 1 := rfl
  rw [hhead] at hsum
  have htail : ((partitionTriples t).tail.map fun tr =>
      if tr.2.1.isEmpty then (1 : ℕ) else 0).sum = 0 := by omega
  have hzero := (List.sum_eq_zero_iff.mp htail)
    (if tr.2.1.isEmpty then (1 : ℕ) else 0)
    (List.mem_map.mpr ⟨tr, htr, rfl⟩)
  rw [hobs] at hzero
  simp at hzero

private theorem order_le_orderList (t : PTree) :
    ∀ ts : List PTree, t ∈ ts → PTree.order t ≤ PTree.orderList ts
  | [], h => nomatch h
  | u :: ts, h => by
      rcases List.mem_cons.mp h with h | h
      · subst h
        rw [PTree.orderList_cons]
        omega
      · have := order_le_orderList t ts h
        rw [PTree.orderList_cons]
        omega

/-- In a non-trivial partition, the root block is strictly smaller. -/
theorem tail_rootBlock_order_lt {t : PTree}
    {tr : PTree × List PTree × PTree}
    (htr : tr ∈ (partitionTriples t).tail) :
    PTree.order tr.1 < PTree.order t := by
  have horder := partitionTriples_order t tr
    (by rw [partitionTriples_eq_cons t]; exact List.mem_cons_of_mem _ htr)
  have hne := tail_obs_ne_nil htr
  rcases hobs : tr.2.1 with _ | ⟨o, os⟩
  · exact absurd hobs hne
  · rw [hobs, PTree.orderList_cons] at horder
    have := PTree.order_pos o
    omega

/-- In a non-trivial partition, every separated block is strictly
smaller. -/
theorem tail_block_order_lt {t : PTree} {tr : PTree × List PTree × PTree}
    (htr : tr ∈ (partitionTriples t).tail) {o : PTree}
    (ho : o ∈ tr.2.1) : PTree.order o < PTree.order t := by
  have horder := partitionTriples_order t tr
    (by rw [partitionTriples_eq_cons t]; exact List.mem_cons_of_mem _ htr)
  have hle : PTree.order o ≤ PTree.orderList tr.2.1 :=
    order_le_orderList o tr.2.1 ho
  have := PTree.order_pos tr.1
  omega

/-! ### The substitution law -/

/-- **The substitution law**: substitute the vector-field series `b`
into the B-series `a` by summing over all partitions — `b` on the
blocks, `a` on the contracted skeleton. -/
def substCoeff [CommSemiring R] (b a : PTree → R) (t : PTree) : R :=
  ((partitionTriples t).map fun tr =>
    b tr.1 * (tr.2.1.map b).prod * a tr.2.2).sum

theorem substCoeff_eq_head_add_tail [CommSemiring R] (b a : PTree → R)
    (t : PTree) :
    substCoeff b a t =
      b t * a (.node []) +
        ((partitionTriples t).tail.map fun tr =>
          b tr.1 * (tr.2.1.map b).prod * a tr.2.2).sum := by
  rw [substCoeff]
  conv_lhs => rw [partitionTriples_eq_cons t]
  rw [List.map_cons, List.sum_cons]
  show b t * (([] : List PTree).map b).prod * a (.node []) + _ = _
  rw [List.map_nil, List.prod_nil, mul_one]

/-! ### Backward error analysis: the modified vector field -/

section ModifiedField

variable [CommRing R]

/-- **The modified vector-field series** of `a` relative to a unital
series `e`: the unique `b` with `b ⋆ e = a`, constructed by strong
recursion on the tree order — on each tree, subtract the contributions
of all non-trivial partitions, whose blocks are strictly smaller. -/
noncomputable def modifiedCoeff (a e : PTree → R) (t : PTree) : R :=
  a t - (((partitionTriples t).tail.attach).map fun tr =>
    modifiedCoeff a e tr.1.1 *
      ((tr.1.2.1.attach).map fun o => modifiedCoeff a e o.1).prod *
      e tr.1.2.2).sum
termination_by PTree.order t
decreasing_by
  · exact tail_rootBlock_order_lt tr.2
  · exact tail_block_order_lt tr.2 o.2

private theorem attach_map_eq {A : Type*} {M : Type*}
    (l : List A) (F : A → M) :
    (l.attach).map (fun x => F x.1) = l.map F := by
  rw [show (fun x : {a // a ∈ l} => F x.1) = F ∘ Subtype.val from rfl,
    ← List.map_map, List.attach_map_subtype_val]

/-- The defining equation of the modified series, attach-free. -/
theorem modifiedCoeff_eq (a e : PTree → R) (t : PTree) :
    modifiedCoeff a e t =
      a t - ((partitionTriples t).tail.map fun tr =>
        modifiedCoeff a e tr.1 * (tr.2.1.map (modifiedCoeff a e)).prod *
          e tr.2.2).sum := by
  rw [modifiedCoeff]
  congr 1
  rw [attach_map_eq ((partitionTriples t).tail)
    (fun x => modifiedCoeff a e x.1 *
      ((x.2.1.attach).map fun o => modifiedCoeff a e o.1).prod *
      e x.2.2)]
  refine congrArg List.sum (List.map_congr_left fun tr _ => ?_)
  rw [attach_map_eq tr.2.1 (modifiedCoeff a e)]

/-- **Backward error analysis, existence**: the modified series
substitutes along `e` to give back `a` — the numerical method is the
`e`-flow of the modified vector field. -/
theorem substCoeff_modifiedCoeff (a e : PTree → R)
    (he : e (.node []) = 1) (t : PTree) :
    substCoeff (modifiedCoeff a e) e t = a t := by
  rw [substCoeff_eq_head_add_tail, he, mul_one, modifiedCoeff_eq]
  ring

/-- **Backward error analysis, uniqueness**: the modified series is the
only solution of `b ⋆ e = a`. -/
theorem modifiedCoeff_unique {a e b : PTree → R}
    (he : e (.node []) = 1) (hb : ∀ t, substCoeff b e t = a t) :
    ∀ t, b t = modifiedCoeff a e t := by
  suffices h : ∀ n, ∀ t, PTree.order t ≤ n →
      b t = modifiedCoeff a e t by
    intro t
    exact h (PTree.order t) t le_rfl
  intro n
  induction n with
  | zero =>
      intro t ht
      have := PTree.order_pos t
      omega
  | succ n ih =>
      intro t ht
      have hsub := hb t
      rw [substCoeff_eq_head_add_tail, he, mul_one] at hsub
      have htail : ((partitionTriples t).tail.map fun tr =>
          b tr.1 * (tr.2.1.map b).prod * e tr.2.2).sum =
          ((partitionTriples t).tail.map fun tr =>
            modifiedCoeff a e tr.1 *
              (tr.2.1.map (modifiedCoeff a e)).prod * e tr.2.2).sum := by
        refine congrArg List.sum (List.map_congr_left fun tr htr => ?_)
        have h1 : b tr.1 = modifiedCoeff a e tr.1 :=
          ih tr.1 (by have := tail_rootBlock_order_lt htr; omega)
        have h2 : tr.2.1.map b = tr.2.1.map (modifiedCoeff a e) :=
          List.map_congr_left fun o ho =>
            ih o (by have := tail_block_order_lt htr ho; omega)
        rw [h1, h2]
      rw [htail] at hsub
      rw [modifiedCoeff_eq]
      exact eq_sub_of_add_eq hsub

end ModifiedField

end BSeries
