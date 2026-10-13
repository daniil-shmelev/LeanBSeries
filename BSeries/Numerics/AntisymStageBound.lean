/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Stability

/-!
# The stage bound for explicit EES methods

The stability-polynomial argument in Proposition `EES_2_m` of Shmelev et al., `main_sn_2.tex`. The shared coefficient identities are in `Numerics.Stability`.
-/

namespace BSeries.RungeKutta

noncomputable section

variable {R : Type*} [Field R] {s : ℕ}

theorem not_hasAntisymOrder_twice_stages [CharZero R] [Invertible (2 : R)]
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1) :
    ¬ ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) (2 * s) := by
  intro hanti
  have hproddeg :
      (stabilityPolynomial rk * (stabilityPolynomial rk).comp (-Polynomial.X)).natDegree ≤
        2 * s := by
    calc
      _ ≤ (stabilityPolynomial rk).natDegree +
          ((stabilityPolynomial rk).comp (-Polynomial.X)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 2 * s := by
        rw [Polynomial.natDegree_eq_of_degree_eq Polynomial.degree_comp_neg_X]
        have := natDegree_stabilityPolynomial_le rk
        omega
  apply stabilityPolynomial_mul_neg_ne_one hexp hcons
  apply Polynomial.ext
  intro n
  by_cases hn : n ≤ 2 * s
  · exact coeff_stabilityPolynomial_mul_neg_of_hasAntisymOrder hexp hanti hn
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp [Polynomial.coeff_one, show n ≠ 0 by omega]

theorem antisymOrder_lt_twice_stages [CharZero R] [Invertible (2 : R)]
    {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    {m : ℕ} (hanti : ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) m) :
    m < 2 * s := by
  by_contra hm
  exact not_hasAntisymOrder_twice_stages hexp hcons (hanti.mono (by omega))

end

end BSeries.RungeKutta
