/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Cuts.Rooted
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# The Graded Cut Identity and the Flow Identity

This file proves the combinatorial identity underlying the flow property of
the exact B-series: for every ordered forest, the sum of inverse tree
factorials over the coproduct terms whose trunk has `k` vertices is a
binomial multiple of the inverse forest factorial,

  `Σ_{cuts, |R^c| = k} 1/(P^c! R^c!) = C(|ω|, k) / ω!`,

and consequently the two-variable flow identity

  `Σ_{cuts} h^{|P^c|}/P^c! · h'^{|R^c|}/R^c! = (h + h')^{|ω|} / ω!`,

which expresses that the exact flows compose: `B_h ∘ B_{h'} = B_{h+h'}`
(Butcher; Hairer-Lubich-Wanner, *Geometric Numerical Integration*, III.1).
The tree case reduces along the `B⁺` recursion of the coproduct via
`Nat.add_one_mul_choose_eq`, and the forest case is Vandermonde's identity.
-/

namespace BSeries

open HopfAlgebras

universe u

namespace PTree

open HopfAlgebras.PTree

noncomputable section

variable {R : Type u}

/-- The `k`-graded sum of inverse tree factorials over the coproduct terms
of an ordered forest: cut terms whose trunk has `k` vertices. -/
noncomputable def gradedCutSumList (R : Type u) [Field R] (ts : List PTree)
    (k : ℕ) : R :=
  ((coproductTermsList ts).map fun t =>
    if RootedForest.order t.2 = k
    then ((RootedForest.treeFactorial t.1 : R))⁻¹ *
      ((RootedForest.treeFactorial t.2 : R))⁻¹
    else 0).sum

private theorem sum_map_finset_sum_comm {α : Type*} [Field R] (l : List α)
    (s : Finset ℕ) (f : α → ℕ → R) :
    (l.map fun a => ∑ j ∈ s, f a j).sum = ∑ j ∈ s, (l.map fun a => f a j).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [List.map_cons, List.sum_cons]

private theorem map_flatMap' {α β γ : Type*} (l : List α) (f : α → List β)
    (g : β → γ) :
    (l.flatMap f).map g = l.flatMap fun a => (f a).map g := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem sum_flatMap' {α : Type*} {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

private theorem sum_mul_sum' {α β : Type*} {M : Type*}
    [NonUnitalNonAssocSemiring M] (xs : List α) (ys : List β)
    (f : α → M) (g : β → M) :
    (xs.map f).sum * (ys.map g).sum =
      (xs.map fun x => (ys.map fun y => f x * g y).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, add_mul, ih, List.map_cons,
        List.sum_cons, List.sum_map_mul_left]

/-- Pointwise decomposition of the graded indicator on a product of cut
terms. -/
private theorem graded_pair_eq [Field R] [CharZero R]
    (x y : RootedForest × RootedForest) (k : ℕ) :
    (if RootedForest.order (x.2 + y.2) = k
      then ((RootedForest.treeFactorial (x.1 + y.1) : R))⁻¹ *
        ((RootedForest.treeFactorial (x.2 + y.2) : R))⁻¹
      else 0) =
    ∑ j ∈ Finset.range (k + 1),
      (if RootedForest.order x.2 = j
        then ((RootedForest.treeFactorial x.1 : R))⁻¹ *
          ((RootedForest.treeFactorial x.2 : R))⁻¹
        else 0) *
      (if RootedForest.order y.2 = k - j
        then ((RootedForest.treeFactorial y.1 : R))⁻¹ *
          ((RootedForest.treeFactorial y.2 : R))⁻¹
        else 0) := by
  by_cases h : RootedForest.order x.2 + RootedForest.order y.2 = k
  · rw [if_pos (by rw [RootedForest.order_add]; exact h)]
    rw [Finset.sum_eq_single_of_mem (RootedForest.order x.2)
      (Finset.mem_range.2 (by omega))
      (fun j _ hj => by
        rw [if_neg (fun hx : RootedForest.order x.2 = j => hj hx.symm),
          zero_mul])]
    rw [if_pos rfl, if_pos (by omega)]
    rw [RootedForest.treeFactorial_add, RootedForest.treeFactorial_add]
    push_cast
    rw [mul_inv, mul_inv]
    ring
  · rw [if_neg (by rw [RootedForest.order_add]; exact h)]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have hjk := Finset.mem_range.1 hj
    by_cases hx : RootedForest.order x.2 = j
    · rw [if_pos hx,
        if_neg (fun hy : RootedForest.order y.2 = k - j => h (by omega)),
        mul_zero]
    · rw [if_neg hx, zero_mul]

/-- The graded cut sum is multiplicative over products of term lists, with
the grading convolved. -/
private theorem graded_multiply [Field R] [CharZero R]
    (xs ys : List (RootedForest × RootedForest)) (k : ℕ) :
    ((multiplyCoproductTerms xs ys).map fun t =>
      if RootedForest.order t.2 = k
      then ((RootedForest.treeFactorial t.1 : R))⁻¹ *
        ((RootedForest.treeFactorial t.2 : R))⁻¹
      else 0).sum =
    ∑ j ∈ Finset.range (k + 1),
      ((xs.map fun t =>
        if RootedForest.order t.2 = j
        then ((RootedForest.treeFactorial t.1 : R))⁻¹ *
          ((RootedForest.treeFactorial t.2 : R))⁻¹
        else 0).sum) *
      ((ys.map fun t =>
        if RootedForest.order t.2 = k - j
        then ((RootedForest.treeFactorial t.1 : R))⁻¹ *
          ((RootedForest.treeFactorial t.2 : R))⁻¹
        else 0).sum) := by
  rw [multiplyCoproductTerms, map_flatMap', sum_flatMap']
  have hpoint : ((xs.map fun x =>
      ((ys.map fun y => (x.1 + y.1, x.2 + y.2)).map fun t =>
        if RootedForest.order t.2 = k
        then ((RootedForest.treeFactorial t.1 : R))⁻¹ *
          ((RootedForest.treeFactorial t.2 : R))⁻¹
        else 0).sum).sum) =
      ((xs.map fun x => (ys.map fun y =>
        ∑ j ∈ Finset.range (k + 1),
          (if RootedForest.order x.2 = j
            then ((RootedForest.treeFactorial x.1 : R))⁻¹ *
              ((RootedForest.treeFactorial x.2 : R))⁻¹
            else 0) *
          (if RootedForest.order y.2 = k - j
            then ((RootedForest.treeFactorial y.1 : R))⁻¹ *
              ((RootedForest.treeFactorial y.2 : R))⁻¹
            else 0)).sum).sum) := by
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun y _ => ?_)
    exact graded_pair_eq x y k
  rw [hpoint]
  have hswap : ((xs.map fun x => (ys.map fun y =>
      ∑ j ∈ Finset.range (k + 1),
        (if RootedForest.order x.2 = j
          then ((RootedForest.treeFactorial x.1 : R))⁻¹ *
            ((RootedForest.treeFactorial x.2 : R))⁻¹
          else 0) *
        (if RootedForest.order y.2 = k - j
          then ((RootedForest.treeFactorial y.1 : R))⁻¹ *
            ((RootedForest.treeFactorial y.2 : R))⁻¹
          else 0)).sum).sum) =
      ∑ j ∈ Finset.range (k + 1),
        ((xs.map fun x => (ys.map fun y =>
          (if RootedForest.order x.2 = j
            then ((RootedForest.treeFactorial x.1 : R))⁻¹ *
              ((RootedForest.treeFactorial x.2 : R))⁻¹
            else 0) *
          (if RootedForest.order y.2 = k - j
            then ((RootedForest.treeFactorial y.1 : R))⁻¹ *
              ((RootedForest.treeFactorial y.2 : R))⁻¹
            else 0)).sum).sum) := by
    rw [← sum_map_finset_sum_comm]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    rw [← sum_map_finset_sum_comm]
  rw [hswap]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_mul_sum']

private theorem graded_aux [Field R] [CharZero R] (n : ℕ) :
    ∀ ts : List PTree, orderList ts ≤ n → ∀ k : ℕ,
      gradedCutSumList R ts k =
        (Nat.choose (orderList ts) k : R) *
          ((treeFactorialList ts : R))⁻¹ := by
  induction n with
  | zero =>
      intro ts h k
      have hts : ts = [] := (orderList_eq_zero_iff ts).1 (by omega)
      subst hts
      rw [gradedCutSumList]
      cases k with
      | zero => simp [coproductTermsList]
      | succ k' => simp [coproductTermsList, RootedForest.order_zero]
  | succ n ih =>
      intro ts hle k
      cases ts with
      | nil =>
          rw [gradedCutSumList]
          cases k with
          | zero => simp [coproductTermsList]
          | succ k' => simp [coproductTermsList, RootedForest.order_zero]
      | cons t ts' =>
          obtain ⟨cs⟩ := t
          rw [PTree.orderList_cons] at hle
          have horder := PTree.order_pos (PTree.node cs)
          have hcs : PTree.orderList cs ≤ n := by
            have := PTree.order_eq_one_add_orderList_children (PTree.node cs)
            simp only [PTree.children_node] at this
            omega
          have hts' : PTree.orderList ts' ≤ n := by omega
          -- the value of the graded sum on a single tree
          have htree : ∀ j : ℕ,
              ((coproductTerms (PTree.node cs)).map fun term =>
                if RootedForest.order term.2 = j
                then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                  ((RootedForest.treeFactorial term.2 : R))⁻¹
                else 0).sum =
              (Nat.choose (order (PTree.node cs)) j : R) *
                ((treeFactorial (PTree.node cs) : R))⁻¹ := by
            intro j
            rw [List.Perm.sum_eq ((coproductTerms_node_perm cs).map fun term =>
              if RootedForest.order term.2 = j
              then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                ((RootedForest.treeFactorial term.2 : R))⁻¹
              else 0)]
            rw [List.map_append, List.sum_append, List.map_map]
            cases j with
            | zero =>
                have hmapped : (((coproductTermsList cs).map
                    ((fun term => if RootedForest.order term.2 = 0
                      then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                        ((RootedForest.treeFactorial term.2 : R))⁻¹
                      else 0) ∘ fun term =>
                        (term.1, RootedForest.singleton
                          (RootedForest.graft term.2)))).sum) = 0 := by
                  refine List.sum_eq_zero fun x hx => ?_
                  rcases List.mem_map.1 hx with ⟨term, _, rfl⟩
                  simp only [Function.comp_def, RootedForest.order_singleton,
                    RootedForest.order_graft]
                  rw [if_neg (by omega)]
                rw [hmapped, zero_add]
                simp [RootedForest.order_zero, RootedForest.treeFactorial_zero,
                  RootedForest.treeFactorial_singleton]
            | succ k' =>
                have hfull : ((([(RootedForest.singleton
                    (RootedTree.ofPTree (PTree.node cs)),
                    (0 : RootedForest))]).map fun term =>
                    if RootedForest.order term.2 = k' + 1
                    then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                      ((RootedForest.treeFactorial term.2 : R))⁻¹
                    else 0).sum) = 0 := by
                  simp [RootedForest.order_zero]
                rw [hfull, add_zero]
                have hmapped : (((coproductTermsList cs).map
                    ((fun term => if RootedForest.order term.2 = k' + 1
                      then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                        ((RootedForest.treeFactorial term.2 : R))⁻¹
                      else 0) ∘ fun term =>
                        (term.1, RootedForest.singleton
                          (RootedForest.graft term.2)))).sum) =
                    ((k' : R) + 1)⁻¹ * gradedCutSumList R cs k' := by
                  rw [gradedCutSumList, ← List.sum_map_mul_left]
                  refine congrArg List.sum
                    (List.map_congr_left fun term _ => ?_)
                  simp only [Function.comp_def, RootedForest.order_singleton,
                    RootedForest.order_graft,
                    RootedForest.treeFactorial_singleton,
                    RootedForest.treeFactorial_graft]
                  by_cases hr : RootedForest.order term.2 = k'
                  · rw [if_pos (by omega), if_pos hr, hr]
                    push_cast
                    rw [mul_inv]
                    ring
                  · rw [if_neg (by omega), if_neg hr, mul_zero]
                rw [hmapped, ih cs hcs k']
                have hfact : (treeFactorial (PTree.node cs) : R) =
                    ((PTree.orderList cs : R) + 1) *
                      (treeFactorialList cs : R) := by
                  have : treeFactorial (PTree.node cs) =
                      (1 + PTree.orderList cs) * treeFactorialList cs := rfl
                  rw [this]
                  push_cast
                  ring
                have horder' : order (PTree.node cs) =
                    PTree.orderList cs + 1 := by
                  have := PTree.order_eq_one_add_orderList_children
                    (PTree.node cs)
                  simp only [PTree.children_node] at this
                  omega
                rw [hfact, horder']
                have hnat := Nat.add_one_mul_choose_eq (PTree.orderList cs) k'
                have hR : ((PTree.orderList cs : R) + 1) *
                    (Nat.choose (PTree.orderList cs) k' : R) =
                    (Nat.choose (PTree.orderList cs + 1) (k' + 1) : R) *
                      ((k' : R) + 1) := by
                  exact_mod_cast hnat
                have h1 : ((treeFactorialList cs : ℕ) : R) ≠ 0 :=
                  Nat.cast_ne_zero.2 (PTree.treeFactorialList_ne_zero cs)
                have h2 : ((k' : R) + 1) ≠ 0 := by
                  have h2' : (((k' + 1 : ℕ)) : R) ≠ 0 :=
                    Nat.cast_ne_zero.2 (Nat.succ_ne_zero k')
                  push_cast at h2'
                  exact h2'
                have h3 : ((PTree.orderList cs : R) + 1) ≠ 0 := by
                  have h3' : (((PTree.orderList cs + 1 : ℕ)) : R) ≠ 0 :=
                    Nat.cast_ne_zero.2 (Nat.succ_ne_zero (PTree.orderList cs))
                  push_cast at h3'
                  exact h3'
                field_simp
                linear_combination hR
          -- assemble via the multiplicativity of graded sums
          rw [show gradedCutSumList R (PTree.node cs :: ts') k =
            ((multiplyCoproductTerms (coproductTerms (PTree.node cs))
              (coproductTermsList ts')).map fun t =>
                if RootedForest.order t.2 = k
                then ((RootedForest.treeFactorial t.1 : R))⁻¹ *
                  ((RootedForest.treeFactorial t.2 : R))⁻¹
                else 0).sum from rfl]
          rw [graded_multiply]
          have hstep : ∀ j ∈ Finset.range (k + 1),
              ((coproductTerms (PTree.node cs)).map fun term =>
                if RootedForest.order term.2 = j
                then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                  ((RootedForest.treeFactorial term.2 : R))⁻¹
                else 0).sum *
              ((coproductTermsList ts').map fun term =>
                if RootedForest.order term.2 = k - j
                then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                  ((RootedForest.treeFactorial term.2 : R))⁻¹
                else 0).sum =
              ((Nat.choose (order (PTree.node cs)) j : R) *
                (Nat.choose (PTree.orderList ts') (k - j) : R)) *
              (((treeFactorial (PTree.node cs) : R))⁻¹ *
                ((treeFactorialList ts' : R))⁻¹) := by
            intro j _
            rw [htree j, show ((coproductTermsList ts').map fun term =>
              if RootedForest.order term.2 = k - j
              then ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                ((RootedForest.treeFactorial term.2 : R))⁻¹
              else 0).sum = gradedCutSumList R ts' (k - j) from rfl,
              ih ts' hts' (k - j)]
            ring
          rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul]
          have hvander : (∑ j ∈ Finset.range (k + 1),
              (Nat.choose (order (PTree.node cs)) j : R) *
                (Nat.choose (PTree.orderList ts') (k - j) : R)) =
              (Nat.choose (order (PTree.node cs) + PTree.orderList ts') k :
                R) := by
            have h := Nat.add_choose_eq (order (PTree.node cs))
              (PTree.orderList ts') k
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
            exact_mod_cast h.symm
          rw [hvander]
          have hordercons : PTree.orderList (PTree.node cs :: ts') =
              order (PTree.node cs) + PTree.orderList ts' := rfl
          have hfactcons : (treeFactorialList (PTree.node cs :: ts') : R) =
              (treeFactorial (PTree.node cs) : R) *
                (treeFactorialList ts' : R) := by
            have : treeFactorialList (PTree.node cs :: ts') =
                treeFactorial (PTree.node cs) * treeFactorialList ts' := rfl
            rw [this]
            push_cast
            ring
          rw [hordercons, hfactcons, mul_inv]

/--
The graded cut identity: the sum of inverse tree factorials over the cut
terms of an ordered forest whose trunk has `k` vertices equals
`C(|ω|, k) / ω!` (arXiv:2507.21006 background; Hairer-Lubich-Wanner III.1).
-/
theorem gradedCutSumList_eq (R : Type u) [Field R] [CharZero R]
    (ts : List PTree) (k : ℕ) :
    gradedCutSumList R ts k =
      (Nat.choose (orderList ts) k : R) * ((treeFactorialList ts : R))⁻¹ :=
  graded_aux (orderList ts) ts le_rfl k

/--
The flow identity for cuts of ordered forests:

  `Σ_{cuts} h^{|P^c|}/P^c! · h'^{|R^c|}/R^c! = (h + h')^{|ω|} / ω!`.

This is the combinatorial content of the composition law of exact flows,
`B_h ∘ B_{h'} = B_{h+h'}`.
-/
theorem flow_identity (R : Type u) [Field R] [CharZero R] (h h' : R)
    (ts : List PTree) :
    ((coproductTermsList ts).map fun t =>
      h ^ RootedForest.order t.1 * ((RootedForest.treeFactorial t.1 : R))⁻¹ *
        (h' ^ RootedForest.order t.2 *
          ((RootedForest.treeFactorial t.2 : R))⁻¹)).sum =
    (h + h') ^ orderList ts * ((treeFactorialList ts : R))⁻¹ := by
  have hpoint : ∀ term ∈ coproductTermsList ts,
      h ^ RootedForest.order term.1 *
        ((RootedForest.treeFactorial term.1 : R))⁻¹ *
        (h' ^ RootedForest.order term.2 *
          ((RootedForest.treeFactorial term.2 : R))⁻¹) =
      ∑ k ∈ Finset.range (orderList ts + 1),
        (if RootedForest.order term.2 = k
          then h ^ (orderList ts - k) * h' ^ k *
            (((RootedForest.treeFactorial term.1 : R))⁻¹ *
              ((RootedForest.treeFactorial term.2 : R))⁻¹)
          else 0) := by
    intro term hterm
    have hgrade := coproductTermsList_order hterm
    rw [Finset.sum_eq_single_of_mem (RootedForest.order term.2)
      (Finset.mem_range.2 (by omega))
      (fun j _ hj => by
        rw [if_neg (fun hx : RootedForest.order term.2 = j => hj hx.symm)])]
    rw [if_pos rfl, show orderList ts - RootedForest.order term.2 =
      RootedForest.order term.1 from by omega]
    ring
  rw [List.map_congr_left hpoint, sum_map_finset_sum_comm]
  have hstep : ∀ k ∈ Finset.range (orderList ts + 1),
      ((coproductTermsList ts).map fun term =>
        if RootedForest.order term.2 = k
        then h ^ (orderList ts - k) * h' ^ k *
          (((RootedForest.treeFactorial term.1 : R))⁻¹ *
            ((RootedForest.treeFactorial term.2 : R))⁻¹)
        else 0).sum =
      h ^ (orderList ts - k) * h' ^ k *
        ((Nat.choose (orderList ts) k : R) *
          ((treeFactorialList ts : R))⁻¹) := by
    intro k _
    rw [← gradedCutSumList_eq R ts k, gradedCutSumList,
      ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun term _ => ?_)
    by_cases hr : RootedForest.order term.2 = k
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, mul_zero]
  rw [Finset.sum_congr rfl hstep]
  have hbin : (∑ k ∈ Finset.range (orderList ts + 1),
      h ^ (orderList ts - k) * h' ^ k *
        ((Nat.choose (orderList ts) k : R) *
          ((treeFactorialList ts : R))⁻¹)) =
      (∑ k ∈ Finset.range (orderList ts + 1),
        h' ^ k * h ^ (orderList ts - k) *
          (Nat.choose (orderList ts) k : R)) *
        ((treeFactorialList ts : R))⁻¹ := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hbin, ← add_pow, add_comm h' h]

end

end PTree

end BSeries
