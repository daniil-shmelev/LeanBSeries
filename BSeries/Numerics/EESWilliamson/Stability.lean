/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Stability
import Mathlib.FieldTheory.Separable

/-!
# Stability and nondegeneracy at maximal antisymmetric order

This is the stability-polynomial argument in Step 1 of the Williamson representation proof: `R(z)R(-z) = 1 + (-1)^s r_s² z^(2s)`, with `r_s ≠ 0`. Strict triangularity identifies `r_s` with the final weight times the subdiagonal product.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Polynomial
open scoped BigOperators

noncomputable section

variable {R : Type*} [Field R] {s : ℕ}

/-- The first potentially nonzero coordinate of a chain stage vector is the product of the preceding subdiagonal entries. -/
theorem stageWeight_tallTree_pivot {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (n : ℕ) (hn : n < s) :
    stageWeight rk (PTree.tallTree n) ⟨n, hn⟩ =
      ∏ j : Fin n,
        rk.A ⟨j.val + 1, by have := j.isLt; omega⟩
          ⟨j.val, by have := j.isLt; omega⟩ := by
  induction n with
  | zero => simp [PTree.tallTree, stageWeightList]
  | succ n ih =>
      simp only [PTree.tallTree, stageWeight_node, stageWeightList_cons,
        stageWeightList_nil, mul_one]
      rw [Finset.sum_eq_single (⟨n, by omega⟩ : Fin s)]
      · rw [ih (by omega), Fin.prod_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last]
        rw [mul_comm]
      · intro j _ hj
        by_cases h : j.val < n
        · rw [stageWeight_tallTree_eq_zero_of_lt hexp n j h, mul_zero]
        · rw [hexp _ j (by
            have : j.val ≠ n := fun heq => hj (Fin.ext heq)
            change n + 1 ≤ j.val
            omega), zero_mul]
      · simp

/-- The top stability coefficient of an explicit tableau is its final weight times its subdiagonal product. -/
theorem stabilityCoeff_last {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hs : 0 < s) :
    stabilityCoeff rk s =
      rk.b ⟨s - 1, by omega⟩ *
        ∏ j : Fin (s - 1),
          rk.A ⟨j.val + 1, by have := j.isLt; omega⟩
            ⟨j.val, by have := j.isLt; omega⟩ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  simp only [stabilityCoeff, weight, Nat.succ_sub_one]
  rw [Finset.sum_eq_single (⟨n, by omega⟩ : Fin (n + 1))]
  · rw [stageWeight_tallTree_pivot hexp n (by omega)]
  · intro j _ hj
    rw [stageWeight_tallTree_eq_zero_of_lt hexp n j (by
      have := j.isLt
      have : j.val ≠ n := fun heq => hj (Fin.ext heq)
      omega), mul_zero]
  · simp

/-- A nonzero top stability coefficient forces each subdiagonal entry to be nonzero. -/
theorem subdiagonal_ne_zero_of_stabilityCoeff_last {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (htop : stabilityCoeff rk s ≠ 0)
    (i j : Fin s) (hij : i.val + 1 = j.val) : rk.A j i ≠ 0 := by
  have hs : 0 < s := by have := i.isLt; omega
  rw [stabilityCoeff_last hexp hs] at htop
  have hi : i.val < s - 1 := by have := j.isLt; omega
  have h := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp htop).2)
    (⟨i.val, hi⟩ : Fin (s - 1)) (Finset.mem_univ _)
  have heq : (⟨i.val + 1, by have := j.isLt; omega⟩ : Fin s) = j := Fin.ext hij
  simpa only [heq] using h

variable [CharZero R] [Invertible (2 : R)]

/-- The forward--backward stability polynomial has only its constant and top terms. -/
theorem stabilityPolynomial_mul_neg_eq {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    stabilityPolynomial rk * (stabilityPolynomial rk).comp (-X) =
      1 + C ((-1 : R) ^ s * stabilityCoeff rk s ^ 2) * X ^ (2 * s) := by
  have hdeg := natDegree_stabilityPolynomial_le rk
  have hneg : ((stabilityPolynomial rk).comp (-X)).natDegree ≤ s := by
    rwa [natDegree_eq_of_degree_eq degree_comp_neg_X]
  apply Polynomial.ext
  intro n
  rcases lt_trichotomy n (2 * s) with hn | rfl | hn
  · rw [coeff_stabilityPolynomial_mul_neg_of_hasAntisymOrder hexp hanti (by omega : n ≤ 2 * s - 1)]
    rw [coeff_add, coeff_C_mul_X_pow, ite_eq_right (Nat.ne_of_lt hn), add_zero]
  · rw [show 2 * s = s + s by omega,
      coeff_mul_add_eq_of_natDegree_le hdeg hneg]
    rw [show (-X : R[X]) = C (-1) * X by simp, comp_C_mul_X_coeff,
      coeff_stabilityPolynomial hexp]
    rw [coeff_add, coeff_C_mul_X_pow, ite_eq_left rfl, coeff_one,
      ite_eq_right (by omega : s + s ≠ 0), zero_add]
    ring
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (natDegree_mul_le.trans (by omega)) hn)]
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_one,
      ite_eq_right (show n ≠ 0 by omega), ite_eq_right (Nat.ne_of_gt hn), zero_add]

/-- Consistency rules out loss of the top stability coefficient at maximal antisymmetric order. -/
theorem stabilityCoeff_last_ne_zero {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    stabilityCoeff rk s ≠ 0 := by
  intro hz
  have hprod := stabilityPolynomial_mul_neg_eq hs hexp hanti
  simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, map_zero, zero_mul, add_zero] at hprod
  exact stabilityPolynomial_mul_neg_ne_one hexp hcons hprod

/-- The quadratic coefficient is forced to be `1/2`, as used in the node recurrence. -/
theorem stabilityCoeff_two_of_hasAntisymOrder {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    stabilityCoeff rk 2 = 1 / 2 := by
  have h := coeff_stabilityPolynomial_mul_neg_of_hasAntisymOrder hexp hanti
    (by omega : 2 ≤ 2 * s - 1)
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [show (-X : R[X]) = C (-1) * X by simp] at h
  simp_rw [comp_C_mul_X_coeff, coeff_stabilityPolynomial hexp] at h
  have h0 : stabilityCoeff rk 0 = 1 := rfl
  norm_num [Finset.sum_range_succ, stabilityCoeff_one_of_consistent hcons, h0, coeff_one] at h
  linear_combination h / 2

/-- Nonvanishing of the final weight and of every subdiagonal entry, as a single product. -/
theorem subdiagonal_product_ne_zero_of_hasAntisymOrder {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    rk.b ⟨s - 1, by omega⟩ *
        (∏ j : Fin (s - 1),
          rk.A ⟨j.val + 1, by have := j.isLt; omega⟩
            ⟨j.val, by have := j.isLt; omega⟩) ≠ 0 := by
  rw [← stabilityCoeff_last hexp hs]
  exact stabilityCoeff_last_ne_zero hs hexp hcons hanti

/-- The forward--backward stability polynomial is separable, hence has no nonconstant square factor. -/
theorem separable_stabilityPolynomial_mul_neg {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    (stabilityPolynomial rk * (stabilityPolynomial rk).comp (-X)).Separable := by
  rw [stabilityPolynomial_mul_neg_eq hs hexp hanti]
  let a := (-1 : R) ^ s * stabilityCoeff rk s ^ 2
  have ha : a ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (pow_ne_zero _ (stabilityCoeff_last_ne_zero hs hexp hcons hanti))
  have hsep := (separable_X_pow_sub_C (-a⁻¹)
    (Nat.cast_ne_zero.mpr (by omega : 2 * s ≠ 0)) (neg_ne_zero.mpr (inv_ne_zero ha)))
  have heq : (1 : R[X]) + C a * X ^ (2 * s) =
      C a * (X ^ (2 * s) - C (-a⁻¹)) := by
    rw [mul_sub, map_neg, mul_neg, sub_neg_eq_add, ← map_mul, mul_inv_cancel₀ ha,
      map_one, add_comm]
  rw [heq]
  exact Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)) hsep

end

end BSeries.RungeKutta
