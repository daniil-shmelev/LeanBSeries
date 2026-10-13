/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.Krylov

/-!
# Block swap in the regular chain basis

The forward--backward stage equations give the coefficients of the block swap in the Krylov basis. Its anticommutation relation with multiplication by the abscissae gives the scalar identities in Step 3 of the Williamson proof.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Matrix
open scoped BigOperators

noncomputable section

variable {R : Type*} [Field R] {s : ℕ}

/-- Exchange the two stage blocks, retaining their internal order. -/
def swapBlocks (v : Fin (s + s) → R) : Fin (s + s) → R :=
  Fin.addCases (fun i => v (i.natAdd s)) (fun i => v (i.castAdd s))

omit [Field R] in
@[simp] theorem swapBlocks_left (v : Fin (s + s) → R) (i : Fin s) :
    swapBlocks v (i.castAdd s) = v (i.natAdd s) := by
  simp only [swapBlocks, Fin.addCases_left]

omit [Field R] in
@[simp] theorem swapBlocks_right (v : Fin (s + s) → R) (i : Fin s) :
    swapBlocks v (i.natAdd s) = v (i.castAdd s) := by
  simp only [swapBlocks, Fin.addCases_right]

theorem forwardBackward_mulVec_left (rk : RungeKutta (Fin s) R)
    (v : Fin (s + s) → R) (i : Fin s) :
    (rk.forwardBackward.stageMatrix *ᵥ v) (i.castAdd s) =
      ∑ j, rk.A i j * v (j.castAdd s) := by
  simp only [mulVec, dotProduct, stageMatrix, Fin.sum_univ_add,
    forwardBackward_A_left_left, forwardBackward_A_left_right,
    zero_mul, Finset.sum_const_zero, add_zero]

theorem forwardBackward_mulVec_right (rk : RungeKutta (Fin s) R)
    (v : Fin (s + s) → R) (i : Fin s) :
    (rk.forwardBackward.stageMatrix *ᵥ v) (i.natAdd s) =
      (∑ j, rk.b j * v (j.castAdd s)) - ∑ j, rk.A i j * v (j.natAdd s) := by
  simp only [mulVec, dotProduct, stageMatrix, Fin.sum_univ_add,
    forwardBackward_A_right_left, forwardBackward_A_right_right,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The block stage equations, with the vanishing composite output used to identify the two block moments. -/
theorem swapBlocks_mulVec (rk : RungeKutta (Fin s) R)
    (v : Fin (s + s) → R) (hv : rk.forwardBackward.b ⬝ᵥ v = 0) :
    swapBlocks (rk.forwardBackward.stageMatrix *ᵥ v) =
      (fun _ => ∑ j, rk.b j * v (j.castAdd s)) -
        rk.forwardBackward.stageMatrix *ᵥ swapBlocks v := by
  have hv' : (∑ j, rk.b j * v (j.castAdd s)) =
      ∑ j, rk.b j * v (j.natAdd s) := by
    simp only [dotProduct, Fin.sum_univ_add, forwardBackward_b_left,
      forwardBackward_b_right, neg_mul, Finset.sum_neg_distrib] at hv
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hv)
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [swapBlocks_left, Pi.sub_apply, forwardBackward_mulVec_left,
      forwardBackward_mulVec_right]
  · simp only [swapBlocks_right, Pi.sub_apply, forwardBackward_mulVec_left,
      forwardBackward_mulVec_right, swapBlocks_left, swapBlocks_right]
    rw [hv']
    ring

theorem stageWeight_forwardBackward_left (rk : RungeKutta (Fin s) R)
    (t : PTree) (i : Fin s) :
    stageWeight rk.forwardBackward t (i.castAdd s) = stageWeight rk t i := by
  simp only [forwardBackward, stageWeight_reindex, finSumFinEquiv_symm_apply_castAdd,
    stageWeight_compose_inl]

theorem stageWeight_tallTree_succ (rk : RungeKutta (Fin s) R) (k : ℕ) :
    stageWeight rk (PTree.tallTree (k + 1)) =
      rk.stageMatrix *ᵥ stageWeight rk (PTree.tallTree k) := by
  rw [stageWeight_tallTree_eq_mulVec, stageWeight_tallTree_eq_mulVec,
    mulVec_mulVec, pow_succ']

/-- The permutation matrix exchanging the two blocks. -/
def blockSwapMatrix : Matrix (Fin (s + s)) (Fin (s + s)) R :=
  fun i j => swapBlocks (fun l => (1 : Matrix (Fin (s + s)) (Fin (s + s)) R) l j) i

theorem blockSwapMatrix_mulVec (v : Fin (s + s) → R) :
    blockSwapMatrix *ᵥ v = swapBlocks v := by
  ext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [mulVec, dotProduct, blockSwapMatrix, swapBlocks_left, swapBlocks_right,
      Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]

/-- Swapping blocks exchanges `c` with `1 - c`. -/
theorem blockSwapMatrix_diagonal (rk : RungeKutta (Fin s) R)
    (hcons : weightBullet rk = 1) :
    blockSwapMatrix * diagonal rk.forwardBackward.abscissa +
      diagonal rk.forwardBackward.abscissa * blockSwapMatrix =
        (blockSwapMatrix : Matrix (Fin (s + s)) (Fin (s + s)) R) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    blockSwapMatrix]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    simp only [swapBlocks_left, swapBlocks_right, Matrix.one_apply] <;>
    split_ifs with h
  · subst j
    rw [abscissa_forwardBackward_left, abscissa_forwardBackward_right _ hcons]
    ring
  · ring
  · subst j
    rw [abscissa_forwardBackward_left, abscissa_forwardBackward_right _ hcons]
    ring
  · ring

variable [CharZero R] [Invertible (2 : R)]

/-- Coefficientwise form of `SP(z) = R(z)P(-z)` modulo `z^(2s)`. -/
theorem swapBlocks_stageWeight_tallTree {rk : RungeKutta (Fin s) R}
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (k : ℕ) (hk : k < s + s) :
    swapBlocks (stageWeight rk.forwardBackward (PTree.tallTree k)) =
      ∑ i ∈ Finset.range (k + 1),
        ((-1 : R) ^ i * stabilityCoeff rk (k - i)) •
          stageWeight rk.forwardBackward (PTree.tallTree i) := by
  induction k with
  | zero =>
      ext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [swapBlocks_left, swapBlocks_right, Nat.zero_add, Finset.range_one,
          Finset.sum_singleton, pow_zero, Nat.sub_self, stabilityCoeff, one_mul, one_smul,
          PTree.tallTree, stageWeight_node, stageWeightList_nil]
  | succ k ih =>
      have hm := forwardBackward_chain_moment hanti k (by omega)
      rw [← stageWeight_tallTree_eq_mulVec] at hm
      rw [stageWeight_tallTree_succ, swapBlocks_mulVec _ _ hm, ih (by omega)]
      have hconst : (fun _ : Fin (s + s) =>
          ∑ j, rk.b j * stageWeight rk.forwardBackward (PTree.tallTree k) (j.castAdd s)) =
          stabilityCoeff rk (k + 1) • stageWeight rk.forwardBackward (PTree.tallTree 0) := by
        ext i
        simp only [stageWeight_forwardBackward_left, Pi.smul_apply, smul_eq_mul,
          PTree.tallTree, stageWeight_node, stageWeightList_nil]
        simp only [stabilityCoeff, weight, mul_one]
      rw [hconst]
      have hshift : rk.forwardBackward.stageMatrix *ᵥ
          (∑ i ∈ Finset.range (k + 1),
            ((-1 : R) ^ i * stabilityCoeff rk (k - i)) •
              stageWeight rk.forwardBackward (PTree.tallTree i)) =
          -(∑ i ∈ Finset.range (k + 1),
            ((-1 : R) ^ (i + 1) * stabilityCoeff rk (k + 1 - (i + 1))) •
              stageWeight rk.forwardBackward (PTree.tallTree (i + 1))) := by
        ext j
        simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum, Pi.neg_apply]
        rw [← Finset.sum_neg_distrib]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.add_sub_add_right, pow_succ, mul_neg_one, neg_mul, neg_mul, neg_neg]
        rw [stageWeight_tallTree_succ]
        simp only [mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      rw [hshift, sub_neg_eq_add, Finset.sum_range_succ' (n := k + 1)]
      simp only [pow_zero, Nat.sub_zero, one_mul]
      exact add_comm _ _

/-- The block swap is upper triangular in Krylov coordinates, with the stability coefficients on its superdiagonals. -/
theorem inKrylovBasis_blockSwapMatrix {rk : RungeKutta (Fin s) R}
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (i j : Fin (s + s)) :
    rk.forwardBackward.inKrylovBasis hdet blockSwapMatrix i j =
      if i ≤ j then (-1 : R) ^ i.val * stabilityCoeff rk (j.val - i.val) else 0 := by
  rw [inKrylovBasis_apply, blockSwapMatrix_mulVec,
    swapBlocks_stageWeight_tallTree hanti j.val j.isLt]
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  change (∑ k ∈ Finset.range (j.val + 1),
    ((-1 : R) ^ k * stabilityCoeff rk (j.val - k)) *
      rk.forwardBackward.krylovCoordinates hdet (stageWeight rk.forwardBackward (PTree.tallTree k)) i) = _
  by_cases hij : i ≤ j
  · rw [ite_eq_left hij, Finset.sum_eq_single i.val,
      krylovCoordinates_tallTree hdet i.val i.isLt, ite_eq_left rfl, mul_one]
    · intro k hk hki
      rw [krylovCoordinates_tallTree hdet k (by
        have := Finset.mem_range.mp hk; have := j.isLt; omega),
        ite_eq_right (Ne.symm hki), mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_range.mpr (by exact Nat.lt_succ_of_le hij)))
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro k hk
    rw [krylovCoordinates_tallTree hdet k (by
      have := Finset.mem_range.mp hk; have := j.isLt; omega),
      ite_eq_right (by have := Finset.mem_range.mp hk; simp only [Fin.le_def] at hij; omega),
      mul_zero]

omit [CharZero R] [Invertible (2 : R)] in
/-- Conjugating the block-swap anticommutator gives the matrix identity from which all scalar coefficient relations follow. -/
theorem blockSwap_anticommutator_inKrylovBasis {rk : RungeKutta (Fin s) R}
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0) (hcons : weightBullet rk = 1) :
    rk.forwardBackward.inKrylovBasis hdet blockSwapMatrix *
        rk.forwardBackward.inKrylovBasis hdet (diagonal rk.forwardBackward.abscissa) +
      rk.forwardBackward.inKrylovBasis hdet (diagonal rk.forwardBackward.abscissa) *
        rk.forwardBackward.inKrylovBasis hdet blockSwapMatrix =
      rk.forwardBackward.inKrylovBasis hdet blockSwapMatrix := by
  simpa only [map_add, map_mul] using
    congrArg (rk.forwardBackward.inKrylovBasis hdet) (blockSwapMatrix_diagonal rk hcons)

/-- The master identity, with `q(k + 1) = t_k` and zero boundary values `q(0) = q(2s) = 0`. -/
theorem forwardBackward_master_identity {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → R} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (i j : Fin (s + s)) (hij : i ≤ j) :
    (rk.forwardBackward.abscissa i + rk.forwardBackward.abscissa j - 1) *
        stabilityCoeff rk (j.val - i.val) +
      (krylovSubdiagonal t (j.val + 1) - krylovSubdiagonal t i.val) *
        stabilityCoeff rk (j.val - i.val + 1) = 0 := by
  let U := rk.forwardBackward.inKrylovBasis hdet blockSwapMatrix
  let L := rk.forwardBackward.inKrylovBasis hdet (diagonal rk.forwardBackward.abscissa)
  have hU (a b : Fin (s + s)) (hab : a ≤ b) :
      U a b = (-1 : R) ^ a.val * stabilityCoeff rk (b.val - a.val) := by
    exact (inKrylovBasis_blockSwapMatrix hdet hanti a b).trans (ite_eq_left hab)
  have hright : (U * L) i j = (-1 : R) ^ i.val *
      (stabilityCoeff rk (j.val - i.val) * rk.forwardBackward.abscissa j +
        krylovSubdiagonal t (j.val + 1) * stabilityCoeff rk (j.val - i.val + 1)) := by
    rw [ht.mul_inKrylovBasis_diagonal (isExplicit_forwardBackward rk hexp) hdet, hU i j hij]
    by_cases hj : j.val + 1 < s + s
    · rw [dite_eq_left hj, hU i ⟨j.val + 1, hj⟩ (by
        change i.val ≤ j.val + 1; exact Nat.le_succ_of_le hij)]
      have heq : j.val + 1 - i.val = j.val - i.val + 1 := by
        simp only [Fin.le_def] at hij; omega
      simp only [heq]
      ring
    · rw [dite_eq_right hj,
        show j.val + 1 = s + s by have := j.isLt; omega, krylovSubdiagonal_end]
      ring
  have hleft : (L * U) i j = (-1 : R) ^ i.val *
      (rk.forwardBackward.abscissa i * stabilityCoeff rk (j.val - i.val) -
        krylovSubdiagonal t i.val * stabilityCoeff rk (j.val - i.val + 1)) := by
    rw [ht.inKrylovBasis_diagonal_mul (isExplicit_forwardBackward rk hexp) hdet, hU i j hij]
    by_cases hi : 0 < i.val
    · rw [dite_eq_left hi, hU ⟨i.val - 1, by have := i.isLt; omega⟩ j (by
        change i.val - 1 ≤ j.val; exact (Nat.sub_le _ _).trans hij)]
      have heq : j.val - (i.val - 1) = j.val - i.val + 1 := by
        simp only [Fin.le_def] at hij; omega
      have hsign : (-1 : R) ^ (i.val - 1) = -(-1 : R) ^ i.val := by
        calc
          _ = -((-1 : R) ^ (i.val - 1) * -1) := by ring
          _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hi]
      simp only [heq, hsign]
      ring
    · rw [dite_eq_right hi, show i.val = 0 by omega, krylovSubdiagonal_zero]
      ring
  have heq := congrArg (fun M : Matrix (Fin (s + s)) (Fin (s + s)) R => M i j)
    (blockSwap_anticommutator_inKrylovBasis hdet hcons)
  change (U * L) i j + (L * U) i j = U i j at heq
  rw [hright, hleft, hU i j hij] at heq
  apply (mul_eq_zero.mp (show (-1 : R) ^ i.val *
    ((rk.forwardBackward.abscissa i + rk.forwardBackward.abscissa j - 1) *
      stabilityCoeff rk (j.val - i.val) +
      (krylovSubdiagonal t (j.val + 1) - krylovSubdiagonal t i.val) *
      stabilityCoeff rk (j.val - i.val + 1)) = 0 from ?_)).resolve_left
        (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  linear_combination heq

end

end BSeries.RungeKutta
