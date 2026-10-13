/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.CoefficientRecurrence
import BSeries.Algebra.PolynomialRotation

/-!
# Primitivity of the spectral root

The polynomial rotation identity determines the stability polynomial as a product along the spectral orbit. Square-freeness forces the orbit to have length `2s`.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Polynomial
open scoped BigOperators

noncomputable section

local instance primitiveInvertibleTwo : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

/-- The primitive spectral root and the linear factors of the stability polynomial. -/
theorem exists_forwardBackward_spectral_data {s : ℕ} (hs : 2 ≤ s)
    {rk : RungeKutta (Fin s) ℝ} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    ∃ z : ℂ, z ^ 2 - (4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3) : ℝ) * z + 1 = 0 ∧
      z ^ s = -1 ∧ orderOf z = 2 * s ∧ (stabilityPolynomial rk).map Complex.ofRealHom =
        ∏ j ∈ Finset.range s, (1 - C ((z - 1) / 2 * z ^ j) * X) := by
  obtain ⟨z, hroot, hphase, hr⟩ := exists_stabilityCoeff_root_recurrence hs hexp hcons hanti
  let p : ℂ[X] := (stabilityPolynomial rk).map Complex.ofRealHom
  have hcoeff (k : ℕ) : p.coeff k = (↑(stabilityCoeff rk k) : ℂ) := by
    simp only [p, coeff_map, coeff_stabilityPolynomial hexp]
    rfl
  have hp₀ : p.coeff 0 = 1 := by rw [hcoeff]; rfl
  have hpdeg : p.natDegree = s := by
    dsimp [p]
    rw [natDegree_map_eq_of_injective Complex.ofReal_injective]
    apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_stabilityPolynomial_le rk)
    rw [coeff_stabilityPolynomial hexp]
    exact stabilityCoeff_last_ne_zero (by omega) hexp hcons hanti
  have hsq : Squarefree (p * p.comp (-X)) := by
    have h := (separable_stabilityPolynomial_mul_neg (by omega) hexp hcons hanti).map
      (f := Complex.ofRealHom)
    dsimp [p]
    simpa only [Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] using h.squarefree
  have hrec (k : ℕ) (hk : k < s) :
      2 * p.coeff (k + 1) * (z ^ (k + 1) - 1) =
        p.coeff k * (z - 1) * (z ^ k + 1) := by
    rw [hcoeff, hcoeff]
    exact hr k hk
  have hz₀ : z ≠ 0 := by intro h; simp [h] at hroot
  have hz₁ : z ≠ 1 := by intro h; rw [h, one_pow] at hphase; norm_num at hphase
  have hrot := polynomial_rotation p z ((z - 1) / 2) (fun k => by
    by_cases hk : k < s
    · linear_combination hrec k hk / 2
    · have htop : p.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      rw [htop, zero_mul]
      by_cases heq : k = s
      · rw [heq, hphase]; ring
      · rw [coeff_eq_zero_of_natDegree_lt (p := p) (n := k) (by omega)]; ring)
  have hfactor := polynomial_factor_of_rotation p z ((z - 1) / 2) hp₀ hpdeg hsq hphase hrot
  have horder := orderOf_eq_twice_of_rotation_factor p z ((z - 1) / 2) (by omega)
    (div_ne_zero (sub_ne_zero.mpr hz₁) (by norm_num)) hz₀ hphase hsq hfactor
  exact ⟨z, hroot, hphase, horder, hfactor⟩

end

end BSeries.RungeKutta
