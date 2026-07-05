/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Density
import Mathlib.Algebra.CharZero.Infinite

/-!
# Enumeration of trees by order and existence of high-order methods

We enumerate the planar trees and forests of each order, deduce that the
rooted trees of order at most `p` form a finite set, and combine this with
the density theorem 317A to obtain Butcher's existence theorem: **for every
`p` there is a Runge–Kutta method of order `p`**
(Butcher, *Numerical Methods for ODEs*, Subsection 324 via Theorem 317A).
-/

namespace BSeries

open HopfAlgebras

namespace PTree

open HopfAlgebras.PTree

mutual

/-- All planar trees of order exactly `n`. -/
def treesOfOrder : ℕ → List PTree
  | 0 => []
  | n + 1 => (forestsOfOrder n).map .node
  termination_by n => 2 * n
  decreasing_by omega

/-- All planar forests of total order exactly `m`. -/
def forestsOfOrder : ℕ → List (List PTree)
  | 0 => [[]]
  | m + 1 =>
      (List.range (m + 1)).attach.flatMap fun k =>
        (treesOfOrder (k.1 + 1)).flatMap fun t =>
          (forestsOfOrder (m - k.1)).map fun ts => t :: ts
  termination_by m => 2 * m + 1
  decreasing_by
    all_goals
      have hk := List.mem_range.1 k.2
      omega

end

mutual

/-- Completeness of the tree enumeration. -/
theorem mem_treesOfOrder : ∀ t : PTree, t ∈ treesOfOrder (order t)
  | .node ts => by
      rw [order_node, Nat.add_comm]
      simp only [treesOfOrder]
      exact List.mem_map.2 ⟨ts, mem_forestsOfOrder ts, rfl⟩

/-- Completeness of the forest enumeration. -/
theorem mem_forestsOfOrder : ∀ ts : List PTree,
    ts ∈ forestsOfOrder (orderList ts)
  | [] => by
      rw [orderList_nil]
      simp only [forestsOfOrder]
      exact List.mem_singleton.2 rfl
  | t :: ts => by
      obtain ⟨k, hk⟩ : ∃ k, order t = k + 1 :=
        ⟨order t - 1, (Nat.succ_pred_eq_of_pos (order_pos t)).symm⟩
      have horder : orderList (t :: ts) = (k + orderList ts) + 1 := by
        rw [orderList_cons, hk]
        omega
      rw [horder]
      simp only [forestsOfOrder]
      refine List.mem_flatMap.2 ⟨⟨k, List.mem_range.2 (by omega)⟩,
        List.mem_attach _ _, ?_⟩
      refine List.mem_flatMap.2 ⟨t, ?_, ?_⟩
      · rw [← hk]
        exact mem_treesOfOrder t
      · refine List.mem_map.2 ⟨ts, ?_, rfl⟩
        rw [show k + orderList ts - k = orderList ts from by omega]
        exact mem_forestsOfOrder ts

end

end PTree

namespace RootedTree

open HopfAlgebras.RootedTree

open scoped Classical in
/-- The finite set of rooted trees of order at most `p`. -/
noncomputable def treesUpToOrder (p : ℕ) : Finset RootedTree :=
  (Finset.range (p + 1)).biUnion fun n =>
    ((PTree.treesOfOrder n).map RootedTree.ofPTree).toFinset

theorem mem_treesUpToOrder {p : ℕ} {τ : RootedTree}
    (h : RootedTree.order τ ≤ p) : τ ∈ treesUpToOrder p := by
  classical
  refine Quotient.inductionOn τ (fun t h => ?_) h
  refine Finset.mem_biUnion.2 ⟨PTree.order t, ?_, ?_⟩
  · refine Finset.mem_range.2 ?_
    have h1 : RootedTree.order (RootedTree.ofPTree t) = PTree.order t :=
      RootedTree.order_ofPTree t
    have h2 : RootedTree.order (RootedTree.ofPTree t) ≤ p := h
    omega
  · exact List.mem_toFinset.2
      (List.mem_map.2 ⟨t, PTree.mem_treesOfOrder t, rfl⟩)

end RootedTree

namespace RungeKutta

/-- **Existence of Runge–Kutta methods of arbitrary order** (Butcher,
*Numerical Methods for ODEs*, Subsection 324, via Theorem 317A): for every
`p` there is a Runge–Kutta method of order `p`. -/
theorem exists_rk_hasOrder (R : Type*) [Field R] [CharZero R] (p : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (rk : RungeKutta ι R), HasOrder rk p := by
  obtain ⟨ι, hι, rk, hrk⟩ := exists_rk_forall_treeWeight
    (RootedTree.treesUpToOrder p)
    (fun τ => (RootedTree.treeFactorial τ : R)⁻¹)
  refine ⟨ι, hι, rk, (hasOrder_iff_treeWeight rk p).2 fun τ hτ => ?_⟩
  exact hrk τ (RootedTree.mem_treesUpToOrder hτ)

end RungeKutta

end BSeries
