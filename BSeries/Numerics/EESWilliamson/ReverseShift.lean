/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.BlockSwap
import BSeries.Numerics.Williamson.Subdiagonal

/-!
# Reverse shift and recovery of the tableau

Conjugating the transpose of the nilpotent Krylov shift to stage coordinates gives the coefficient matrix of multiplication by the independent variable in the stage-polynomial basis. Its three-term recurrence determines the tableau row identities used by Williamson reconstruction.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Matrix
open scoped BigOperators

noncomputable section

variable {R : Type*} [Field R] {s : ℕ}

/-- The reverse shift in stage coordinates. -/
def reverseShift (rk : RungeKutta (Fin s) R) : Matrix (Fin s) (Fin s) R :=
  rk.krylovMatrix * upperShift s * rk.krylovMatrix⁻¹

theorem reverseShift_mul_krylovMatrix {rk : RungeKutta (Fin s) R}
    (hdet : rk.krylovMatrix.det ≠ 0) :
    rk.reverseShift * rk.krylovMatrix = rk.krylovMatrix * upperShift s := by
  rw [reverseShift, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    mul_one]

/-- The reverse shift lowers each nonconstant chain vector by one degree. -/
theorem reverseShift_mul_chain {rk : RungeKutta (Fin s) R}
    (hdet : rk.krylovMatrix.det ≠ 0) (k : ℕ) (hk : k < s) :
    rk.reverseShift *ᵥ stageWeight rk (PTree.tallTree k) =
      if k = 0 then 0 else stageWeight rk (PTree.tallTree (k - 1)) := by
  ext i
  have h := congrArg (fun M : Matrix (Fin s) (Fin s) R => M i ⟨k, hk⟩)
    (reverseShift_mul_krylovMatrix hdet)
  change (rk.reverseShift *ᵥ stageWeight rk (PTree.tallTree k)) i =
    ∑ j, rk.krylovMatrix i j * (if k = j.val + 1 then 1 else 0) at h
  rw [h]
  by_cases hk₀ : k = 0
  · simp [hk₀]
  · rw [ite_eq_right hk₀, Finset.sum_eq_single (⟨k - 1, by omega⟩ : Fin s),
      ite_eq_left (by dsimp; omega), mul_one]
    · rfl
    · intro j hj hne
      rw [ite_eq_right (fun heq => hne (Fin.ext (by dsimp; omega))), mul_zero]
    · simp

theorem reverseShift_mul_one {rk : RungeKutta (Fin s) R}
    (hdet : rk.krylovMatrix.det ≠ 0) : rk.reverseShift *ᵥ 1 = 0 := by
  by_cases hs : 0 < s
  · have h := reverseShift_mul_chain hdet 0 hs
    have hv : stageWeight rk (PTree.tallTree 0) = (1 : Fin s → R) := by
      ext i; simp [PTree.tallTree, stageWeightList]
    simpa only [hv, ite_true] using h
  · ext i; have := i.isLt; omega

/-- The reverse shift is upper Hessenberg in stage coordinates. -/
theorem reverseShift_eq_zero_of_lt {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    (i j : Fin s) (hij : i.val + 1 < j.val) : rk.reverseShift i j = 0 := by
  let := rk.krylovMatrix.invertibleOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (det_krylovMatrix_ne_zero hexp hsub))
  have htri := Matrix.blockTriangular_inv_of_blockTriangular (krylovMatrix_isLowerTriangular hexp)
  simp only [reverseShift, Matrix.mul_apply, upperShift]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkj : k < j
  · rw [htri hkj, mul_zero]
  · suffices (∑ l, rk.krylovMatrix i l * if k.val = l.val + 1 then 1 else 0) = 0 by
      rw [this, zero_mul]
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hkl : k.val = l.val + 1
    · rw [krylovMatrix_isLowerTriangular hexp (i := i) (j := l) (by
        change ¬k.val < j.val at hkj
        change i.val < l.val
        omega), zero_mul]
    · rw [ite_eq_right hkl, mul_zero]

/-- Away from the final row, lowering after raising is the identity. This is coefficientwise the polynomial relation `DP = zP`. -/
theorem reverseShift_mul_stageMatrix {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    (i j : Fin s) (hi : i.val + 1 < s) :
    (rk.reverseShift * rk.stageMatrix) i j = (1 : Matrix (Fin s) (Fin s) R) i j := by
  have hrow (k : Fin s) :
      (rk.reverseShift * rk.stageMatrix * rk.krylovMatrix) i k = rk.krylovMatrix i k := by
    change ((rk.reverseShift * rk.stageMatrix) *ᵥ stageWeight rk (PTree.tallTree k.val)) i = _
    rw [← mulVec_mulVec, ← stageWeight_tallTree_succ]
    by_cases hk : k.val + 1 < s
    · rw [reverseShift_mul_chain hdet (k.val + 1) hk, ite_eq_right (by omega),
        Nat.add_sub_cancel]
      rfl
    · have hv : stageWeight rk (PTree.tallTree (k.val + 1)) = 0 := by
        ext l
        exact stageWeight_tallTree_eq_zero_of_lt hexp _ l (by have := l.isLt; omega)
      rw [hv, mulVec_zero]
      exact (stageWeight_tallTree_eq_zero_of_lt hexp k.val i (by have := k.isLt; omega)).symm
  let := rk.krylovMatrix.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet)
  have hrow_eq : (rk.reverseShift * rk.stageMatrix) i = (1 : Matrix (Fin s) (Fin s) R) i := by
    apply Matrix.vecMul_injective_of_invertible rk.krylovMatrix
    ext k
    change (rk.reverseShift * rk.stageMatrix * rk.krylovMatrix) i k =
      ((1 : Matrix (Fin s) (Fin s) R) * rk.krylovMatrix) i k
    rw [hrow, one_mul]
  exact congrFun hrow_eq j

/-- The superdiagonal of the reverse shift is the reciprocal of the tableau subdiagonal. -/
theorem reverseShift_superdiagonal {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    (i j : Fin s) (hij : i.val + 1 = j.val) :
    rk.reverseShift i j = (rk.A j i)⁻¹ := by
  have h := reverseShift_mul_stageMatrix hexp (det_krylovMatrix_ne_zero hexp hsub)
    i i (by have := j.isLt; omega)
  rw [Matrix.one_apply_eq, Matrix.mul_apply, Finset.sum_eq_single j] at h
  · change rk.reverseShift i j * rk.A j i = 1 at h
    apply mul_right_cancel₀ (hsub i j hij)
    rw [h, inv_mul_cancel₀ (hsub i j hij)]
  · intro k hk hkj
    by_cases hik : i.val + 1 < k.val
    · rw [reverseShift_eq_zero_of_lt hexp hsub i k hik, zero_mul]
    · change rk.reverseShift i k * rk.A k i = 0
      rw [hexp k i (by
        have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        change k.val ≤ i.val; omega), mul_zero]
  · simp

/-- A tridiagonal reverse-shift row has exactly the three expected contributions. -/
theorem reverseShift_mulVec_of_tridiagonal {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    (p i n : Fin s) (hpi : p.val + 1 = i.val) (hin : i.val + 1 = n.val)
    (htri : ∀ j : Fin s, j.val + 1 < i.val → rk.reverseShift i j = 0)
    (v : Fin s → R) :
    (rk.reverseShift *ᵥ v) i =
      rk.reverseShift i p * v p + rk.reverseShift i i * v i + rk.reverseShift i n * v n := by
  have hpi' : p ≠ i := by intro h; have := congrArg Fin.val h; omega
  have hpn' : p ≠ n := by intro h; have := congrArg Fin.val h; omega
  have hin' : i ≠ n := by intro h; have := congrArg Fin.val h; omega
  calc
    _ = ∑ j ∈ ({p, i, n} : Finset (Fin s)), rk.reverseShift i j * v j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      have hjp : j.val ≠ p.val := fun h => hj.1 (Fin.ext h)
      have hji : j.val ≠ i.val := fun h => hj.2.1 (Fin.ext h)
      have hjn : j.val ≠ n.val := fun h => hj.2.2 (Fin.ext h)
      by_cases hjlt : j.val + 1 < i.val
      · rw [htri j hjlt, zero_mul]
      · rw [reverseShift_eq_zero_of_lt hexp hsub i j (by omega), zero_mul]
    _ = _ := by simp [hpi', hpn', hin', add_assoc]

/-- Tridiagonality gives the successive-row identity with the reverse-shift ratio. -/
theorem reverseShift_row_difference {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    (p i n : Fin s) (hpi : p.val + 1 = i.val) (hin : i.val + 1 = n.val)
    (htri : ∀ j : Fin s, j.val + 1 < i.val → rk.reverseShift i j = 0)
    (j : Fin s) (hji : j < i) :
    rk.reverseShift i n * (rk.A n j - rk.A i j) =
      rk.reverseShift i p * (rk.A i j - rk.A p j) := by
  have hdet := det_krylovMatrix_ne_zero hexp hsub
  have hsum := congrFun (reverseShift_mul_one hdet) i
  rw [reverseShift_mulVec_of_tridiagonal hexp hsub p i n hpi hin htri] at hsum
  simp only [Pi.one_apply, Pi.zero_apply, mul_one] at hsum
  have hmul := reverseShift_mul_stageMatrix hexp hdet i j (by have := n.isLt; omega)
  change (rk.reverseShift *ᵥ (fun k => rk.A k j)) i = _ at hmul
  rw [reverseShift_mulVec_of_tridiagonal hexp hsub p i n hpi hin htri,
    Matrix.one_apply_ne (ne_of_gt hji)] at hmul
  linear_combination hmul - rk.A i j * hsum

/-- Comparing the penultimate coefficient identifies the ratio entirely from tableau entries. -/
theorem tableau_row_difference_of_reverseShift_tridiagonal {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin s, i.val + 1 = j.val → rk.A j i ≠ 0)
    (p i n : Fin s) (hpi : p.val + 1 = i.val) (hin : i.val + 1 = n.val)
    (htri : ∀ j : Fin s, j.val + 1 < i.val → rk.reverseShift i j = 0)
    (j : Fin s) (hji : j < i) :
    rk.A n j - rk.A i j =
      ((rk.A n p - rk.A i p) / rk.A i p) * (rk.A i j - rk.A p j) := by
  have h := reverseShift_row_difference hexp hsub p i n hpi hin htri j hji
  have hp := reverseShift_row_difference hexp hsub p i n hpi hin htri p (by
    change p.val < i.val; omega)
  rw [hexp p p le_rfl, sub_zero] at hp
  have hD : rk.reverseShift i n ≠ 0 := by
    rw [reverseShift_superdiagonal hexp hsub i n hin]
    exact inv_ne_zero (hsub i n hin)
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (hsub p i hpi)).mpr
  apply mul_left_cancel₀ hD
  linear_combination rk.A i p * h - (rk.A i j - rk.A p j) * hp

/-- The row after an original stage is the next original row, or the output row at the block boundary. -/
theorem forwardBackward_A_succ_eq_rowAfter (rk : RungeKutta (Fin s) R)
    (i j : Fin s) :
    rk.forwardBackward.A ⟨i.val + 1, by have := i.isLt; omega⟩ (j.castAdd s) =
      rk.rowAfter i j := by
  unfold rowAfter
  by_cases hi : i.val + 1 < s
  · rw [dite_eq_left hi]
    exact forwardBackward_A_left_left rk ⟨i.val + 1, hi⟩ j
  · rw [dite_eq_right hi]
    have heq : (⟨i.val + 1, by have := i.isLt; omega⟩ : Fin (s + s)) =
        (⟨0, by have := i.isLt; omega⟩ : Fin s).natAdd s := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      have := i.isLt
      omega
    rw [heq, forwardBackward_A_right_left]

/-- Tridiagonality of the first block of the composite reverse shift implies all original tableau row-difference identities, including the final weights. -/
theorem rowDifferenceCondition_of_reverseShift_tridiagonal {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin (s + s), i.val + 1 = j.val → rk.forwardBackward.A j i ≠ 0)
    (htri : ∀ (i : Fin s) (j : Fin (s + s)), j.val + 1 < i.val →
      rk.forwardBackward.reverseShift (i.castAdd s) j = 0) :
    RowDifferenceCondition rk := by
  intro i hi j hji
  let p : Fin s := ⟨i.val - 1, by have := i.isLt; omega⟩
  let n : Fin (s + s) := ⟨i.val + 1, by have := i.isLt; omega⟩
  have hpi : p.val + 1 = i.val := by dsimp [p]; omega
  have h := tableau_row_difference_of_reverseShift_tridiagonal
    (isExplicit_forwardBackward rk hexp) hsub (p.castAdd s) (i.castAdd s) n
    hpi rfl (htri i) (j.castAdd s) hji
  change rk.rowDifference i j =
    (rk.rowDifference i p / rk.A i p) * rk.rowDifference p j
  simp only [n, forwardBackward_A_succ_eq_rowAfter, forwardBackward_A_left_left] at h
  simpa only [rowDifference, rowAfter_succ rk hpi] using h

end

end BSeries.RungeKutta
