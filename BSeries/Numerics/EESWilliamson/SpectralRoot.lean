/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.NodeRecurrence
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Reciprocal roots of the composite node recurrence

The spectral mapping theorem supplies a characteristic root whose `s`th power is `-1`. Working directly with this root avoids the trigonometric parametrization and treats repeated roots in the same coefficient argument.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Matrix Complex
open scoped BigOperators Matrix

noncomputable section

/-- Two finite second-order recurrence solutions agree if their first two values agree. -/
theorem secondOrder_eq_of_initial {R : Type*} [CommRing R] {N : ℕ} (hN : 2 ≤ N)
    (a : R) (u v : Fin N → R)
    (hu : ∀ (k : ℕ) (hk : k + 2 < N),
      u ⟨k + 2, hk⟩ - a * u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ = 0)
    (hv : ∀ (k : ℕ) (hk : k + 2 < N),
      v ⟨k + 2, hk⟩ - a * v ⟨k + 1, by omega⟩ + v ⟨k, by omega⟩ = 0)
    (h₀ : u ⟨0, by omega⟩ = v ⟨0, by omega⟩)
    (h₁ : u ⟨1, by omega⟩ = v ⟨1, by omega⟩) : u = v := by
  have h (k : ℕ) : ∀ hk : k < N, u ⟨k, hk⟩ = v ⟨k, hk⟩ := by
    induction k using Nat.twoStepInduction with
    | zero => intro hk; exact h₀
    | one => intro hk; exact h₁
    | more k ih₀ ih₁ =>
        intro hk
        have h := hu k hk
        rw [ih₀ (by omega), ih₁ (by omega)] at h
        linear_combination h - hv k hk
  exact funext fun i => h i.val i.isLt

/-- A reciprocal root turns consecutive differences into a geometric sequence. -/
theorem secondOrder_geometric_difference {R : Type*} [Field R] {N : ℕ} (hN : 2 ≤ N)
    (a z : R) (hz : z ≠ 0) (hroot : z ^ 2 - a * z + 1 = 0) (u : Fin N → R)
    (hu : ∀ (k : ℕ) (hk : k + 2 < N),
      u ⟨k + 2, hk⟩ - a * u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ = 0)
    (k : ℕ) (hk : k + 1 < N) :
    u ⟨k + 1, hk⟩ - z⁻¹ * u ⟨k, by omega⟩ =
      z ^ k * (u ⟨1, by omega⟩ - z⁻¹ * u ⟨0, by omega⟩) := by
  have ha : a = z + z⁻¹ := by
    apply (mul_right_cancel₀ hz)
    field_simp
    linear_combination -hroot
  induction k with
  | zero => simp
  | succ k ih =>
      have h := hu k hk
      rw [ha] at h
      rw [pow_succ]
      linear_combination h + z * ih (by omega) + u ⟨k, by omega⟩ * (mul_inv_cancel₀ hz)

/-- With distinct reciprocal roots, a centered solution is a sum of two geometric sequences. -/
theorem secondOrder_root_solution {R : Type*} [Field R] {N : ℕ} (hN : 2 ≤ N)
    (a z : R) (hz : z ≠ 0) (hroot : z ^ 2 - a * z + 1 = 0) (hdist : z ≠ z⁻¹)
    (u : Fin N → R)
    (hu : ∀ (k : ℕ) (hk : k + 2 < N),
      u ⟨k + 2, hk⟩ - a * u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ = 0)
    (hu₀ : u ⟨0, by omega⟩ = 1) :
    ∃ A B : R, A + B = 1 ∧ ∀ j : Fin N, u j = A * z ^ j.val + B * (z⁻¹) ^ j.val := by
  let A := (u ⟨1, by omega⟩ - z⁻¹) / (z - z⁻¹)
  let v : Fin N → R := fun j => A * z ^ j.val + (1 - A) * (z⁻¹) ^ j.val
  have hi : (z⁻¹) ^ 2 - a * z⁻¹ + 1 = 0 := by
    field_simp
    linear_combination hroot
  have hv (k : ℕ) (hk : k + 2 < N) :
      v ⟨k + 2, hk⟩ - a * v ⟨k + 1, by omega⟩ + v ⟨k, by omega⟩ = 0 := by
    dsimp [v]
    simp only [pow_succ]
    linear_combination A * z ^ k * hroot + (1 - A) * (z⁻¹) ^ k * hi
  have hA : A * (z - z⁻¹) = u ⟨1, by omega⟩ - z⁻¹ :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hdist)
  refine ⟨A, 1 - A, by ring, ?_⟩
  have heq := secondOrder_eq_of_initial hN a u v hu hv
    (by simpa [v] using hu₀) (by dsimp [v]; simp only [pow_one]; linear_combination -hA)
  exact fun j => congrFun heq j

/-- The companion matrix of `u_(k+2) - a u_(k+1) + u_k = 0`. -/
def nodeCompanion (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, -1; 1, 0]

/-- Matrix powers propagate pairs of consecutive centered nodes. -/
theorem nodeCompanion_pow_mulVec {N : ℕ} (hN : 2 ≤ N) (a : ℂ) (u : Fin N → ℂ)
    (hu : ∀ (k : ℕ) (hk : k + 2 < N),
      u ⟨k + 2, hk⟩ - a * u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ = 0)
    (k : ℕ) (hk : k + 1 < N) :
    nodeCompanion a ^ k *ᵥ ![u ⟨1, by omega⟩, u ⟨0, by omega⟩] =
      ![u ⟨k + 1, hk⟩, u ⟨k, by omega⟩] := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih (by omega)]
      ext i
      fin_cases i
      · have h := hu k hk
        simp [nodeCompanion, mulVec, dotProduct, Fin.sum_univ_two]
        linear_combination -h
      · simp [nodeCompanion, mulVec, dotProduct, Fin.sum_univ_two]

/-- A nonzero vector reversed by the `s`th companion power forces a characteristic root with `s`th power `-1`. -/
theorem exists_nodeCompanion_root {s : ℕ} (hs : 0 < s) (a : ℂ)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) (hpow : nodeCompanion a ^ s *ᵥ v = -v) :
    ∃ z : ℂ, z ^ 2 - a * z + 1 = 0 ∧ z ^ s = -1 := by
  have hspec : (-1 : ℂ) ∈ spectrum ℂ (nodeCompanion a ^ s) := by
    rw [spectrum.mem_iff]
    intro hunit
    apply hv
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
    rw [map_neg, map_one, sub_mulVec, neg_mulVec, one_mulVec, hpow,
      sub_self, mulVec_zero]
  rw [spectrum.map_pow_of_pos _ hs] at hspec
  obtain ⟨z, hz, hzs⟩ := hspec
  refine ⟨z, ?_, hzs⟩
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def,
    Matrix.charpoly_fin_two] at hz
  simpa [nodeCompanion, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two] using hz

local instance spectralRootInvertibleTwo : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- Centering the abscissae gives a homogeneous recurrence with initial value one. -/
theorem forwardBackward_centered_recurrence {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) ℝ} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    let u : Fin (s + s) → ℂ := fun i => ((1 - 2 * rk.forwardBackward.abscissa i : ℝ) : ℂ)
    u ⟨0, by omega⟩ = 1 ∧ ∀ (k : ℕ) (hk : k + 2 < s + s),
      u ⟨k + 2, hk⟩ - (4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3) : ℝ) *
        u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ = 0 := by
  dsimp only
  constructor
  · have hc₀ : rk.forwardBackward.abscissa ⟨0, by omega⟩ = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact isExplicit_forwardBackward rk hexp _ j (by change 0 ≤ j.val; omega)
    rw [hc₀]
    norm_num
  · intro k hk
    have h := forwardBackward_node_recurrence hs hexp hcons hanti k hk
    have hc : (1 - 2 * rk.forwardBackward.abscissa ⟨k + 2, hk⟩) -
        (4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3)) *
          (1 - 2 * rk.forwardBackward.abscissa ⟨k + 1, by omega⟩) +
            (1 - 2 * rk.forwardBackward.abscissa ⟨k, by omega⟩) = 0 := by
      linear_combination -2 * h
    exact_mod_cast hc

/-- The block sign change supplies a reciprocal characteristic root with `s`th power `-1`. -/
theorem exists_forwardBackward_spectral_root {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) ℝ} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    ∃ z : ℂ, z ^ 2 - (4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3) : ℝ) * z + 1 = 0 ∧
      z ^ s = -1 := by
  let a : ℝ := 4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3)
  let u : Fin (s + s) → ℂ := fun i => ((1 - 2 * rk.forwardBackward.abscissa i : ℝ) : ℂ)
  obtain ⟨hu₀, hrec⟩ := forwardBackward_centered_recurrence hs hexp hcons hanti
  let i₀ : Fin s := ⟨0, by omega⟩
  let i₁ : Fin s := ⟨1, by omega⟩
  let v : Fin 2 → ℂ := ![u (i₁.castAdd s), u (i₀.castAdd s)]
  have hv : v ≠ 0 := by
    intro hv
    have h := congrFun hv 1
    change u ⟨0, by omega⟩ = 0 at h
    exact one_ne_zero (hu₀.symm.trans h)
  have hpow : nodeCompanion (a : ℂ) ^ s *ᵥ v = -v := by
    have h := nodeCompanion_pow_mulVec (by omega : 2 ≤ s + s) (a : ℂ) u hrec s (by omega)
    change nodeCompanion (a : ℂ) ^ s *ᵥ v = ![u (i₁.natAdd s), u (i₀.natAdd s)] at h
    rw [h]
    dsimp [v, u]
    simp only [abscissa_forwardBackward_right _ hcons, abscissa_forwardBackward_left]
    ext j
    fin_cases j <;> simp <;> ring
  exact exists_nodeCompanion_root (by omega : 0 < s) (a : ℂ) v hv hpow

end

end BSeries.RungeKutta
