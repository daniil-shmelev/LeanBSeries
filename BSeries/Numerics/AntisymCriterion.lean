/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.EESExistence
import BSeries.Numerics.Enumeration
import BSeries.Numerics.Reindex

/-!
# The composed-weights criterion for antisymmetric order

The master reduction turning the antisymmetric-order conditions of a
Runge–Kutta scheme (arXiv:2507.21006, Section 8) into finite tableau
arithmetic: a scheme has antisymmetric order at least `m` iff the
elementary weights of the composed tableaux `rk ∘ rk` and `rk* ∘ rk`
agree on all planar trees of order at most `m`.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

/-- **The composed-weights criterion for antisymmetric order**: by the
`SC ⟺ EC` theorem, a Runge–Kutta method has antisymmetric order at least
`m` iff the elementary weights of the two composed tableaux `rk ∘ rk` and
`rk* ∘ rk` agree on all planar trees of order at most `m` — no coproducts
or antipodes required (arXiv:2507.21006, Section 8). -/
theorem hasAntisymOrder_iff_weight_compose_eq {ι : Type} [Fintype ι]
    {R : Type} [Field R] [CharZero R] [Invertible (2 : R)]
    (rk : RungeKutta ι R) (m : ℕ) :
    ForestAlgebra.Character.HasAntisymOrder
        (Series.toCharacter (series rk)) m ↔
      ∀ t : PTree, PTree.order t ≤ m →
        weight (compose rk rk) t =
          weight (compose (adjointScheme rk) rk) t := by
  rw [ForestAlgebra.Character.hasAntisymOrder_iff_convolution_agree]
  constructor
  · intro h t ht
    have h1 := h (RootedForest.singleton (RootedTree.ofPTree t)) (by
      rw [RootedForest.order_singleton, RootedTree.order_ofPTree]
      exact ht)
    rw [← toCharacter_series_compose, ← toCharacter_series_adjointScheme,
      ← toCharacter_series_compose] at h1
    rw [toCharacter_series_evalForest, toCharacter_series_evalForest,
      forestWeight_singleton, forestWeight_singleton, treeWeight_ofPTree,
      treeWeight_ofPTree] at h1
    exact h1
  · intro h φ hφ
    have htree : ∀ τ : RootedTree, RootedTree.order τ ≤ m →
        (ForestAlgebra.Character.convolution (Series.toCharacter (series rk))
          (Series.toCharacter (series rk))).evalForest
            (RootedForest.singleton τ) =
        (ForestAlgebra.Character.convolution
          (ForestAlgebra.Character.adjointCharacter
            (Series.toCharacter (series rk)))
          (Series.toCharacter (series rk))).evalForest
            (RootedForest.singleton τ) := by
      intro τ hτ
      refine Quotient.inductionOn τ (fun t hτ => ?_) hτ
      have ht : PTree.order t ≤ m := by
        have := RootedTree.order_ofPTree t
        exact le_trans (le_of_eq this.symm) hτ
      have h1 := h t ht
      rw [show (⟦t⟧ : RootedTree) = RootedTree.ofPTree t from rfl]
      rw [← toCharacter_series_compose, ← toCharacter_series_adjointScheme,
        ← toCharacter_series_compose]
      rw [toCharacter_series_evalForest, toCharacter_series_evalForest,
        forestWeight_singleton, forestWeight_singleton, treeWeight_ofPTree,
        treeWeight_ofPTree]
      exact h1
    exact ForestAlgebra.Character.evalForest_congr_of_tree_congr htree φ hφ

/-- Agreement with the adjoint implies the corresponding antisymmetric order. -/
theorem hasAntisymOrder_of_weight_adjoint_eq {ι : Type*} [Fintype ι]
    {R : Type*} [Field R] [CharZero R] [Invertible (2 : R)]
    (rk : RungeKutta ι R) (m : ℕ)
    (h : ∀ t : PTree, PTree.order t ≤ m → weight (adjointScheme rk) t = weight rk t) :
    ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) m := by
  have hforest : ∀ φ : RootedForest, RootedForest.order φ ≤ m →
      (Series.toCharacter (series rk)).evalForest φ =
        (Series.toCharacter (series (adjointScheme rk))).evalForest φ := by
    apply ForestAlgebra.Character.evalForest_congr_of_tree_congr
    intro τ hτ
    refine Quotient.inductionOn τ (fun t hτ => ?_) hτ
    rw [show (⟦t⟧ : RootedTree) = RootedTree.ofPTree t from rfl]
    simp only [toCharacter_series_evalForest, forestWeight_singleton, treeWeight_ofPTree]
    apply (h t _).symm
    change RootedTree.order (RootedTree.ofPTree t) ≤ m at hτ
    simpa only [RootedTree.order_ofPTree] using hτ
  rw [ForestAlgebra.Character.hasAntisymOrder_iff_convolution_agree,
    ← toCharacter_series_adjointScheme]
  exact Series.convolution_evalForest_congr hforest (fun _ _ => rfl)

instance : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)

end RungeKutta

end BSeries
