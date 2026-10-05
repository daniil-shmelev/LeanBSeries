/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.AntisymCriterion
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# The stage bound for explicit EES methods

The stability-polynomial argument in Proposition `EES_2_m`
of Shmelev et al., `main_sn_2.tex`.
-/

namespace BSeries

open HopfAlgebras HopfAlgebras.ForestAlgebra

noncomputable section

namespace ForestAlgebra.Character

open HopfAlgebras.ForestAlgebra.Character

theorem evalForest_eq_adjoint_of_hasAntisymOrder {R : Type*} [Field R] [CharZero R]
    [Invertible (2 : R)] {χ : Character R} {m : ℕ} (h : HasAntisymOrder χ m)
    (φ : RootedForest) (hφ : RootedForest.order φ ≤ m) :
    χ.evalForest φ = (adjointCharacter χ).evalForest φ := by
  have hconv := (hasAntisymOrder_iff_convolution_agree χ m).mp h
  have hc := Series.convolution_evalForest_congr hconv
    (fun _ _ => rfl : ∀ ρ, RootedForest.order ρ ≤ m →
      (inverseCharacter χ).evalForest ρ = (inverseCharacter χ).evalForest ρ) φ hφ
  simpa only [convolution_assoc, convolution_inverseCharacter_right,
    convolution_unit_right] using hc

theorem convolution_involution_evalForest_of_hasAntisymOrder {R : Type*}
    [Field R] [CharZero R] [Invertible (2 : R)] {χ : Character R} {m : ℕ}
    (h : HasAntisymOrder χ m) (φ : RootedForest) (hφ : RootedForest.order φ ≤ m) :
    (convolution χ (involution χ)).evalForest φ = (unit R).evalForest φ := by
  have hc := Series.convolution_evalForest_congr
    (evalForest_eq_adjoint_of_hasAntisymOrder h)
    (fun _ _ => rfl : ∀ ρ, RootedForest.order ρ ≤ m →
      (involution χ).evalForest ρ = (involution χ).evalForest ρ) φ hφ
  simpa only [convolution_adjointCharacter_involution] using hc

end ForestAlgebra.Character

namespace PTree

/-- The chain forest of order `n`, with the empty forest at order zero. -/
def chainForest : ℕ → RootedForest
  | 0 => 0
  | n + 1 => RootedForest.singleton (RootedTree.ofPTree (tallTree n))

theorem order_chainForest (n : ℕ) : RootedForest.order (chainForest n) = n := by
  cases n with
  | zero => exact RootedForest.order_zero
  | succ n => simp only [chainForest, RootedForest.order_singleton,
      RootedTree.order_ofPTree, order_tallTree]

theorem graft_chainForest (n : ℕ) :
    RootedForest.graft (chainForest n) = RootedTree.ofPTree (tallTree n) := by
  cases n with
  | zero => exact RootedForest.graft_zero
  | succ n =>
      have h := RootedForest.graft_ofPTree_list [tallTree n]
      change RootedForest.graft (RootedForest.singleton (RootedTree.ofPTree (tallTree n))) = _ at h
      exact h

theorem coproductTerms_tallTree (n : ℕ) :
    (HopfAlgebras.PTree.coproductTerms (tallTree n)).Perm
      ((List.range (n + 2)).map (fun k => (chainForest k, chainForest (n + 1 - k)))) := by
  induction n with
  | zero =>
      simpa [List.range_succ, tallTree, chainForest, RootedTree.bullet, HopfAlgebras.PTree.bullet,
        HopfAlgebras.PTree.coproductTermsList] using
        HopfAlgebras.PTree.coproductTerms_node_perm []
  | succ n ih =>
      have hsingle : HopfAlgebras.PTree.coproductTermsList [tallTree n] =
          HopfAlgebras.PTree.coproductTerms (tallTree n) := by
        simp [HopfAlgebras.PTree.coproductTermsList, HopfAlgebras.PTree.multiplyCoproductTerms]
      have hnode := HopfAlgebras.PTree.coproductTerms_node_perm [tallTree n]
      rw [hsingle] at hnode
      have hmap := ih.map (fun term : RootedForest × RootedForest =>
        (term.1, RootedForest.singleton (RootedForest.graft term.2)))
      have h := hnode.trans (hmap.append_right _)
      change (HopfAlgebras.PTree.coproductTerms (tallTree (n + 1))).Perm _ at h
      convert h using 1
      rw [List.range_succ, List.map_append, List.map_map]
      congr 1
      · apply List.map_congr_left
        intro k hk
        have hk' := List.mem_range.mp hk
        dsimp only [Function.comp_def]
        rw [graft_chainForest]
        congr 1
        rw [show n + 1 + 1 - k = (n + 1 - k) + 1 by omega]
        rfl
      · simp only [List.map_singleton, Nat.sub_self, chainForest, tallTree]

end PTree

theorem convolution_evalForest_chainForest {R : Type*} [CommSemiring R]
    (χ ψ : Character R) (n : ℕ) :
    (ForestAlgebra.Character.convolution χ ψ).evalForest (PTree.chainForest n) =
      ∑ k ∈ Finset.range (n + 1),
        χ.evalForest (PTree.chainForest k) * ψ.evalForest (PTree.chainForest (n - k)) := by
  cases n with
  | zero => simp [PTree.chainForest]
  | succ n =>
      rw [HopfAlgebras.ForestAlgebra.Character.convolution_evalForest,
        PTree.chainForest, RootedForest.convolutionCoeff_singleton_ofPTree,
        HopfAlgebras.PTree.convolutionCoeff,
        HopfAlgebras.PTree.evalCoproductTerms_perm χ ψ (PTree.coproductTerms_tallTree n)]
      simp only [HopfAlgebras.PTree.evalCoproductTerms, List.map_map, Function.comp_def,
        HopfAlgebras.PTree.evalCoproductTerm]
      have hrange (f : ℕ → R) (m : ℕ) :
          ((List.range m).map f).sum = ∑ k ∈ Finset.range m, f k := by
        induction m with
        | zero => simp
        | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]
      exact hrange _ _

namespace RungeKutta

variable {R : Type*} [Field R] {s : ℕ}

theorem stageWeight_tallTree_eq_zero_of_lt {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (n : ℕ) (i : Fin s) (hi : i.val < n) :
    stageWeight rk (PTree.tallTree n) i = 0 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      simp only [PTree.tallTree, stageWeight_node, stageWeightList_cons,
        stageWeightList_nil, mul_one]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hji : i ≤ j
      · rw [hexp i j hji, zero_mul]
      · rw [ih j (by simp only [Fin.le_def] at hji; omega), mul_zero]

theorem weight_tallTree_eq_zero {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (n : ℕ) (hn : s ≤ n) : weight rk (PTree.tallTree n) = 0 := by
  unfold weight
  apply Finset.sum_eq_zero
  intro i _
  rw [stageWeight_tallTree_eq_zero_of_lt hexp n i (by have := i.isLt; omega), mul_zero]

/-- Coefficients of the Runge-Kutta stability series. -/
def stabilityCoeff (rk : RungeKutta (Fin s) R) : ℕ → R
  | 0 => 1
  | n + 1 => weight rk (PTree.tallTree n)

/-- The stability polynomial of an explicit `s`-stage tableau. -/
def stabilityPolynomial (rk : RungeKutta (Fin s) R) : Polynomial R := by
  classical
  exact Polynomial.ofFn (s + 1) (fun i => stabilityCoeff rk i.val)

theorem coeff_stabilityPolynomial {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk)
    (n : ℕ) : (stabilityPolynomial rk).coeff n = stabilityCoeff rk n := by
  classical
  unfold stabilityPolynomial
  by_cases hn : n < s + 1
  · exact Polynomial.ofFn_coeff_eq_val_of_lt _ hn
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
    cases n with
    | zero => omega
    | succ n => exact (weight_tallTree_eq_zero hexp n (by omega)).symm

theorem natDegree_stabilityPolynomial_le (rk : RungeKutta (Fin s) R) :
    (stabilityPolynomial rk).natDegree ≤ s := by
  classical
  have h := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ s + 1)
    (fun i : Fin (s + 1) => stabilityCoeff rk i.val)
  exact Nat.le_of_lt_succ h

theorem evalForest_chainForest (rk : RungeKutta (Fin s) R) (n : ℕ) :
    (Series.toCharacter (series rk)).evalForest (PTree.chainForest n) = stabilityCoeff rk n := by
  cases n with
  | zero => simp [PTree.chainForest, stabilityCoeff]
  | succ n => simp only [PTree.chainForest, stabilityCoeff, toCharacter_series_evalForest,
      forestWeight_singleton, treeWeight_ofPTree]

theorem coeff_stabilityPolynomial_mul_neg {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk)
    (n : ℕ) :
    (stabilityPolynomial rk * (stabilityPolynomial rk).comp (-Polynomial.X)).coeff n =
      (ForestAlgebra.Character.convolution (Series.toCharacter (series rk))
        (ForestAlgebra.Character.involution (Series.toCharacter (series rk)))).evalForest
          (PTree.chainForest n) := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    convolution_evalForest_chainForest]
  simp only [show (-Polynomial.X : Polynomial R) = Polynomial.C (-1) * Polynomial.X by simp]
  simp_rw [Polynomial.comp_C_mul_X_coeff, coeff_stabilityPolynomial hexp,
    ForestAlgebra.Character.involution_evalForest, PTree.order_chainForest, evalForest_chainForest]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem not_hasAntisymOrder_twice_stages [CharZero R] [Invertible (2 : R)]
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1) :
    ¬ ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) (2 * s) := by
  intro hanti
  let p := stabilityPolynomial rk
  have hp0 : p.coeff 0 = 1 := by rw [coeff_stabilityPolynomial hexp]; rfl
  have hp1 : p.coeff 1 = 1 := by
    rw [coeff_stabilityPolynomial hexp]
    exact (weight_bullet rk).trans hcons
  have hp : p ≠ 0 := by intro h; simp [h] at hp0
  have hneg : p.comp (-Polynomial.X) ≠ 0 := by simpa using hp
  have hdeg : (p.comp (-Polynomial.X)).natDegree = p.natDegree :=
    Polynomial.natDegree_eq_of_degree_eq Polynomial.degree_comp_neg_X
  have hproddeg : (p * p.comp (-Polynomial.X)).natDegree ≤ 2 * s := by
    rw [Polynomial.natDegree_mul hp hneg, hdeg]
    have := natDegree_stabilityPolynomial_le rk
    dsimp only [p]
    omega
  have hprod : p * p.comp (-Polynomial.X) = 1 := by
    apply Polynomial.ext
    intro n
    by_cases hn : n ≤ 2 * s
    · rw [coeff_stabilityPolynomial_mul_neg hexp,
        ForestAlgebra.Character.convolution_involution_evalForest_of_hasAntisymOrder hanti _
          (by simpa only [PTree.order_chainForest] using hn),
        HopfAlgebras.ForestAlgebra.Character.unit_evalForest]
      cases n with
      | zero => simp [PTree.chainForest]
      | succ n => simp [PTree.chainForest, HopfAlgebras.ForestAlgebra.counitCoeff,
          RootedForest.singleton_ne_zero, Polynomial.coeff_one]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [Polynomial.coeff_one, show n ≠ 0 by omega]
  have hdegree := congrArg Polynomial.natDegree hprod
  rw [Polynomial.natDegree_mul hp hneg, hdeg, Polynomial.natDegree_one] at hdegree
  have hpdeg : p.natDegree = 0 := by omega
  have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (n := 1) (by omega)
  rw [hp1] at hz
  exact one_ne_zero hz

theorem antisymOrder_lt_twice_stages [CharZero R] [Invertible (2 : R)]
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    {m : ℕ} (hanti : ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) m) :
    m < 2 * s := by
  by_contra hm
  exact not_hasAntisymOrder_twice_stages hexp hcons (hanti.mono (by omega))

end RungeKutta

end

end BSeries
