/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.SpectralRoot
import Mathlib.Algebra.Ring.GeomSum

/-!
# The algebraic recurrence for stability coefficients

A characteristic root turns consecutive centered-node differences into a geometric sequence. Subtracting the master identities at two starts and applying Mathlib's geometric-sum identity gives the coefficient recurrence directly, without angles or a separate repeated-root argument.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Matrix
open scoped BigOperators

noncomputable section

/-- The master identities at two starts select a characteristic root satisfying the coefficient recurrence, including repeated roots. -/
theorem coefficient_recurrence_of_secondOrder {s : ℕ} (hs : 2 ≤ s)
    (a z : ℂ) (hroot : z ^ 2 - a * z + 1 = 0) (hphase : z ^ s = -1)
    (u : Fin (s + s) → ℂ) (r : ℕ → ℂ)
    (hu : ∀ (k : ℕ) (hk : k + 2 < s + s),
      u ⟨k + 2, hk⟩ - a * u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ = 0)
    (hu₀ : u ⟨0, by omega⟩ = 1)
    (hm : ∀ (i k : ℕ) (hi : i ≤ 1) (hk : k < s),
      r k * (u ⟨i, by omega⟩ + u ⟨i + k, by omega⟩) =
        2 * r (k + 1) * ∑ j : Fin (k + 1), u ⟨i + j.val, by have := j.isLt; omega⟩) :
    ∃ q : ℂ, q ^ 2 - a * q + 1 = 0 ∧ q ^ s = -1 ∧
      ∀ k : ℕ, k < s → 2 * r (k + 1) * (q ^ (k + 1) - 1) =
        r k * (q - 1) * (q ^ k + 1) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hroot
  have hd := secondOrder_geometric_difference (by omega : 2 ≤ s + s) a z hz hroot u hu
  have finish (q : ℂ) (k : ℕ)
      (h : r k * (1 + q ^ k) = 2 * r (k + 1) * ∑ j : Fin (k + 1), q ^ j.val) :
      2 * r (k + 1) * (q ^ (k + 1) - 1) = r k * (q - 1) * (q ^ k + 1) := by
    have hg := geom_sum_mul q (k + 1)
    rw [Finset.sum_range] at hg
    linear_combination -(q - 1) * h - 2 * r (k + 1) * hg
  by_cases hw : u ⟨1, by omega⟩ - z⁻¹ * u ⟨0, by omega⟩ = 0
  · have hform (j : Fin (s + s)) : u j = (z⁻¹) ^ j.val := by
      have h (k : ℕ) (hk : k < s + s) : u ⟨k, hk⟩ = (z⁻¹) ^ k := by
        induction k with
        | zero => simpa using hu₀
        | succ k ih =>
            have h := hd k hk
            rw [hw, mul_zero, ih (by omega)] at h
            rw [pow_succ]
            linear_combination h
      exact h j.val j.isLt
    refine ⟨z⁻¹, ?_, ?_, ?_⟩
    · field_simp
      linear_combination hroot
    · rw [inv_pow, hphase]; norm_num
    · intro k hk
      apply finish
      simpa only [hform, Nat.zero_add, pow_zero] using hm 0 k (by omega) hk
  · refine ⟨z, hroot, hphase, ?_⟩
    intro k hk
    apply finish
    apply mul_right_cancel₀ hw
    have h₀ := hm 0 k (by omega) hk
    have h₁ := hm 1 k (by omega) hk
    have hsum : (∑ j : Fin (k + 1), u ⟨1 + j.val, by have := j.isLt; omega⟩) -
        z⁻¹ * (∑ j : Fin (k + 1), u ⟨0 + j.val, by have := j.isLt; omega⟩) =
          (∑ j : Fin (k + 1), z ^ j.val) *
            (u ⟨1, by omega⟩ - z⁻¹ * u ⟨0, by omega⟩) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Nat.add_comm 1, Nat.zero_add] using hd j.val (by have := j.isLt; omega)
    have hkdiff := hd k (by omega)
    simp only [Nat.zero_add, Nat.add_comm 1 k] at h₀ h₁ hsum
    linear_combination h₁ - z⁻¹ * h₀ - r k * hkdiff + 2 * r (k + 1) * hsum

local instance coefficientRecurrenceInvertibleTwo : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

/-- The master identity after centering the nodes and telescoping the bidiagonal differences. -/
theorem forwardBackward_master_centered {s : ℕ}
    {rk : RungeKutta (Fin s) ℝ} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → ℝ} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (i k : ℕ) (hik : i + k < s + s) :
    stabilityCoeff rk k * ((1 - 2 * rk.forwardBackward.abscissa ⟨i, by omega⟩) +
        (1 - 2 * rk.forwardBackward.abscissa ⟨i + k, hik⟩)) =
      2 * stabilityCoeff rk (k + 1) *
        ∑ j : Fin (k + 1), (1 - 2 * rk.forwardBackward.abscissa
          ⟨i + j.val, by have := j.isLt; omega⟩) := by
  have hq (k : ℕ) (hik : i + k < s + s) :
      krylovSubdiagonal t (i + k + 1) - krylovSubdiagonal t i =
        ∑ j : Fin (k + 1), (1 - 2 * rk.forwardBackward.abscissa
          ⟨i + j.val, by have := j.isLt; omega⟩) := by
    have h := Finset.sum_range_sub (fun j => krylovSubdiagonal t (i + j)) (k + 1)
    rw [Finset.sum_range] at h
    simp only [← Nat.add_assoc, Nat.add_zero] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    exact forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht
      ⟨i + j.val, by have := j.isLt; omega⟩
  have h := forwardBackward_master_identity hexp hcons hdet hanti ht
    ⟨i, by omega⟩ ⟨i + k, hik⟩ (by change i ≤ i + k; omega)
  simp only [Nat.add_sub_cancel_left] at h
  rw [hq k hik] at h
  linear_combination -2 * h

/-- A spectral root compatible with the stability-coefficient recurrence. -/
theorem exists_stabilityCoeff_root_recurrence {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) ℝ} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    ∃ z : ℂ, z ^ 2 - (4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3) : ℝ) * z + 1 = 0 ∧
      z ^ s = -1 ∧ ∀ k : ℕ, k < s →
        2 * (↑(stabilityCoeff rk (k + 1)) : ℂ) * (z ^ (k + 1) - 1) =
          (↑(stabilityCoeff rk k) : ℂ) * (z - 1) * (z ^ k + 1) := by
  obtain ⟨z, hz, hzs⟩ := exists_forwardBackward_spectral_root hs hexp hcons hanti
  obtain ⟨hu₀, hrec⟩ := forwardBackward_centered_recurrence hs hexp hcons hanti
  have hdet := det_krylovMatrix_ne_zero (isExplicit_forwardBackward rk hexp)
    (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti)
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  refine coefficient_recurrence_of_secondOrder hs _ z hz hzs
    (fun i => ((1 - 2 * rk.forwardBackward.abscissa i : ℝ) : ℂ))
    (fun k => (↑(stabilityCoeff rk k) : ℂ)) hrec hu₀ ?_
  intro i k hi hk
  exact_mod_cast forwardBackward_master_centered hexp hcons hdet hanti ht i k (by omega)

end

end BSeries.RungeKutta
