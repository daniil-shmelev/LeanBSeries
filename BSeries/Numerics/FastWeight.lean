/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Reindex
import Mathlib.Data.List.GetD

/-!
# A memoised elementary-weight evaluator

The recursive elementary weight `RungeKutta.weight` recomputes stage
weights of shared subtrees once per surrounding stage index, which is
exponentially slow for `native_decide` sweeps over expensive coefficient
fields (rational functions of a generic parameter). This file provides
`RungeKutta.fastWeight`, which annotates each subtree once with its full
stage-weight vector, together with the correctness theorem
`fastWeight_eq` identifying it with `weight`.

Composed tableaux are sum-indexed; combine with `weight_reindex` and
`finSumFinEquiv` to evaluate them through a `Fin`-indexed scheme.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe v

variable {R : Type v} [CommSemiring R] {n : ℕ}

private theorem order_le_orderList_of_mem :
    ∀ {ts : List PTree} {t : PTree}, t ∈ ts →
      PTree.order t ≤ PTree.orderList ts := by
  intro ts
  induction ts with
  | nil => intro t h; cases h
  | cons a ts ih =>
      intro t h
      rw [PTree.orderList_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_add_right _ _
      · exact le_trans (ih h) (Nat.le_add_left _ _)

/-- The stage-weight vector of a tree, computed bottom-up: each subtree
is annotated exactly once. -/
def stageAnn (rk : RungeKutta (Fin n) R) : PTree → List R
  | .node ts =>
      let cs := ts.attach.map fun τ => stageAnn rk τ.1
      (List.range n).map fun i =>
        ((cs.map fun v =>
          ((List.range n).map fun j =>
            (if h : i < n ∧ j < n then rk.A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) *
              v.getD j 0).sum).prod)
  termination_by t => PTree.order t
  decreasing_by
    have h1 : PTree.order τ.1 ≤ PTree.orderList ts :=
      order_le_orderList_of_mem τ.2
    have h2 : PTree.order (PTree.node ts) = 1 + PTree.orderList ts :=
      PTree.order_eq_one_add_orderList_children _
    omega

/-- The memoised elementary weight. -/
def fastWeight (rk : RungeKutta (Fin n) R) (t : PTree) : R :=
  ((List.range n).map fun i =>
    (if h : i < n then rk.b ⟨i, h⟩ else 0) *
      (stageAnn rk t).getD i 0).sum

private theorem getD_map_range {M : Type*} [Zero M] (g : ℕ → M)
    {s i : ℕ} (h : i < s) : ((List.range s).map g).getD i 0 = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

private theorem getD_map_range_d {M : Type*} (d : M) (g : ℕ → M)
    {s i : ℕ} (h : i < s) : ((List.range s).map g).getD i d = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

private theorem list_sum_range_eq {M : Type*} [AddCommMonoid M] :
    ∀ (m : ℕ) (f : ℕ → M),
      ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i
  | 0, f => rfl
  | m + 1, f => by
      rw [List.range_succ, List.map_append, List.sum_append,
        Finset.sum_range_succ, list_sum_range_eq m f]
      simp

private theorem sum_range_dite_eq_sum_univ {M : Type*} [AddCommMonoid M]
    {m : ℕ} (f : Fin m → M) :
    (∑ i ∈ Finset.range m, if h : i < m then f ⟨i, h⟩ else 0) =
      ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i < m then f ⟨i, h⟩
    else 0) m]
  exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.isLt]

private theorem stageWeightList_eq_prod (rk : RungeKutta (Fin n) R) :
    ∀ (ts : List PTree) (i : Fin n),
      stageWeightList rk ts i =
        (ts.map fun t => ∑ j, rk.A i j * stageWeight rk t j).prod
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, List.map_cons, List.prod_cons,
        stageWeightList_eq_prod rk ts i]

private theorem stageAnn_eq (rk : RungeKutta (Fin n) R) :
    ∀ t : PTree, stageAnn rk t =
      (List.range n).map fun i =>
        if h : i < n then stageWeight rk t ⟨i, h⟩ else 0
  | .node ts => by
      rw [stageAnn]
      show (List.range n).map _ = _
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      rw [dif_pos hi, stageWeight_node, stageWeightList_eq_prod]
      have hmap : (ts.attach.map fun τ => stageAnn rk τ.1).map (fun v =>
          ((List.range n).map fun j =>
            (if h : i < n ∧ j < n then rk.A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) *
              v.getD j 0).sum) =
          ts.map fun t => ∑ j, rk.A ⟨i, hi⟩ j * stageWeight rk t j := by
        rw [List.map_map,
          ← List.attach_map_val (l := ts) (f := fun t =>
          ∑ j, rk.A ⟨i, hi⟩ j * stageWeight rk t j)]
        refine List.map_congr_left fun τ _ => ?_
        show ((List.range n).map fun j =>
          (if h : i < n ∧ j < n then rk.A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) *
            (stageAnn rk τ.1).getD j 0).sum = _
        rw [stageAnn_eq rk τ.1, list_sum_range_eq]
        rw [show (∑ j ∈ Finset.range n,
            (if h : i < n ∧ j < n then rk.A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) *
              (((List.range n).map fun k =>
                if h : k < n then stageWeight rk τ.1 ⟨k, h⟩ else 0).getD
                  j 0)) =
          ∑ j ∈ Finset.range n, if h : j < n then
            rk.A ⟨i, hi⟩ ⟨j, h⟩ * stageWeight rk τ.1 ⟨j, h⟩ else 0 from
          Finset.sum_congr rfl fun j hj => by
            rw [Finset.mem_range] at hj
            rw [dif_pos ⟨hi, hj⟩, dif_pos hj,
              getD_map_range _ hj, dif_pos hj]]
        rw [sum_range_dite_eq_sum_univ fun j =>
          rk.A ⟨i, hi⟩ j * stageWeight rk τ.1 j]
      rw [hmap]
  termination_by t => PTree.order t
  decreasing_by
    have h1 : PTree.order τ.1 ≤ PTree.orderList ts :=
      order_le_orderList_of_mem τ.2
    have h2 : PTree.order (PTree.node ts) = 1 + PTree.orderList ts :=
      PTree.order_eq_one_add_orderList_children _
    omega

/-- Materialise a `Fin`-indexed tableau: all entries are computed once
and stored as lists, so that repeated access during a weight sweep does
not re-evaluate expensive coefficient expressions. -/
def materialize (rk : RungeKutta (Fin n) R) : RungeKutta (Fin n) R :=
  let tab := (List.range n).map fun i =>
    (List.range n).map fun j =>
      if h : i < n ∧ j < n then rk.A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  let bs := (List.range n).map fun j =>
    if h : j < n then rk.b ⟨j, h⟩ else 0
  { A := fun i j => ((tab.getD i []).getD j 0)
    b := fun j => bs.getD j 0 }

theorem materialize_eq (rk : RungeKutta (Fin n) R) :
    materialize rk = rk := by
  obtain ⟨A, b⟩ := rk
  refine congrArg₂ RungeKutta.mk ?_ ?_
  · funext i j
    show ((((List.range n).map fun i' => (List.range n).map fun j' =>
      if h : i' < n ∧ j' < n then A ⟨i', h.1⟩ ⟨j', h.2⟩
      else 0).getD (i : ℕ) []).getD (j : ℕ) 0) = A i j
    rw [getD_map_range_d [] _ i.isLt, getD_map_range_d 0 _ j.isLt,
      dif_pos ⟨i.isLt, j.isLt⟩]
  · funext j
    show (((List.range n).map fun j' =>
      if h : j' < n then b ⟨j', h⟩ else 0).getD (j : ℕ) 0) = b j
    rw [getD_map_range _ j.isLt, dif_pos j.isLt]

/-- **The memoised evaluator computes the elementary weight.** -/
theorem fastWeight_eq (rk : RungeKutta (Fin n) R) (t : PTree) :
    fastWeight rk t = weight rk t := by
  rw [fastWeight, weight, list_sum_range_eq]
  rw [show (∑ i ∈ Finset.range n,
      (if h : i < n then rk.b ⟨i, h⟩ else 0) *
        (stageAnn rk t).getD i 0) =
      ∑ i ∈ Finset.range n, if h : i < n then
        rk.b ⟨i, h⟩ * stageWeight rk t ⟨i, h⟩ else 0 from
    Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi
      rw [stageAnn_eq, getD_map_range _ hi, dif_pos hi, dif_pos hi,
        dif_pos hi]]
  rw [sum_range_dite_eq_sum_univ fun i => rk.b i * stageWeight rk t i]

end RungeKutta

end BSeries
