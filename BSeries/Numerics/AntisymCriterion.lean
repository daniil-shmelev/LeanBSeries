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

We also record the classification of rooted trees of order at most two,
used to turn the order-two conditions into the two weight identities
`Σ b = 1` and `Σ b c = 1/2`.
-/

namespace BSeries

open HopfAlgebras

namespace RootedTree

open HopfAlgebras.RootedTree

/-- The unique tree of order one is the one-node tree. -/
theorem eq_bullet_of_order_one {τ : RootedTree} (h : order τ = 1) :
    τ = RootedTree.bullet := by
  have hbr : order τ = RootedForest.order (branches τ) + 1 := by
    conv_lhs => rw [← RootedForest.graft_branches τ]
    rw [RootedForest.order_graft]
    omega
  have hbr0 : branches τ = 0 :=
    (RootedForest.order_eq_zero_iff _).1 (by omega)
  conv_lhs => rw [← RootedForest.graft_branches τ]
  rw [hbr0, RootedForest.graft_zero]

/-- Order-one forests are the singleton one-node tree. -/
theorem forest_eq_of_order_one {ρ : RootedForest}
    (h : RootedForest.order ρ = 1) :
    ρ = RootedForest.singleton RootedTree.bullet := by
  have hne : ρ ≠ 0 := by
    intro h0
    rw [h0, RootedForest.order_zero] at h
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hsplit : (a ::ₘ s : RootedForest) =
      RootedForest.singleton a + s := rfl
  rw [hsplit, RootedForest.order_add, RootedForest.order_singleton] at h
  have hapos := RootedTree.order_pos a
  have hs : (s : RootedForest) = 0 :=
    (RootedForest.order_eq_zero_iff _).1 (by omega)
  have ha1 : order a = 1 := by omega
  rw [hsplit, hs, add_zero, eq_bullet_of_order_one ha1]

/-- The unique tree of order two is the two-chain. -/
theorem eq_chain_of_order_two {τ : RootedTree} (h : order τ = 2) :
    τ = RootedForest.graft (RootedForest.singleton RootedTree.bullet) := by
  have hbr : order τ = RootedForest.order (branches τ) + 1 := by
    conv_lhs => rw [← RootedForest.graft_branches τ]
    rw [RootedForest.order_graft]
    omega
  have hbr1 : RootedForest.order (branches τ) = 1 := by omega
  conv_lhs => rw [← RootedForest.graft_branches τ]
  rw [forest_eq_of_order_one hbr1]

end RootedTree

namespace RungeKutta

/-- The two-chain rooted tree in `PTree` form. -/
theorem graft_singleton_bullet :
    RootedForest.graft (RootedForest.singleton RootedTree.bullet) =
      RootedTree.ofPTree (PTree.node [PTree.node []]) := by
  have h := RootedForest.graft_ofPTree_list [PTree.node []]
  simp only [List.map_cons, List.map_nil] at h
  exact h

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

instance : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)

end RungeKutta

end BSeries
