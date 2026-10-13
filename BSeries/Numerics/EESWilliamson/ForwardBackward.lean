/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.Stability
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Forward--backward composition and its tree conditions

Only the composite tableau is reindexed, preserving the stage order in each block. The antisymmetric order condition makes its elementary weights vanish through the prescribed order. Chains and two-branch trees give the moments and broom conditions of Steps 1–2 of the Williamson proof.
-/

namespace BSeries

open HopfAlgebras Matrix
open scoped BigOperators

namespace PTree

/-- Add `l` unary vertices above a tree. -/
def unaryAbove : ℕ → HopfAlgebras.PTree → HopfAlgebras.PTree
  | 0, t => t
  | l + 1, t => .node [unaryAbove l t]

theorem order_unaryAbove (l : ℕ) (t : HopfAlgebras.PTree) :
    (unaryAbove l t).order = t.order + l := by
  induction l with
  | zero => simp [unaryAbove]
  | succ l ih => simp [unaryAbove, HopfAlgebras.PTree.orderList, ih]; omega

/-- Two branches, a single vertex and a chain of `k + 1` vertices, with `l` unary vertices above their common root. -/
def broom (k l : ℕ) : HopfAlgebras.PTree :=
  unaryAbove l (.node [.bullet, tallTree k])

theorem order_broom (k l : ℕ) : (broom k l).order = k + 3 + l := by
  simp [broom, order_unaryAbove, HopfAlgebras.PTree.order,
    HopfAlgebras.PTree.orderList, order_tallTree]
  omega

end PTree

namespace RungeKutta

variable {R : Type*} {s : ℕ}

/-- The composition of a step with the same tableau at negative step size, in the original order within each block. -/
def forwardBackward [CommRing R] (rk : RungeKutta (Fin s) R) :
    RungeKutta (Fin (s + s)) R :=
  reindex finSumFinEquiv.symm (compose rk (negScheme rk))

section Ring

variable [CommRing R] (rk : RungeKutta (Fin s) R)

@[simp] theorem forwardBackward_A_left_left (i j : Fin s) :
    rk.forwardBackward.A (i.castAdd s) (j.castAdd s) = rk.A i j := by
  simp only [forwardBackward, reindex, finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem forwardBackward_A_left_right (i j : Fin s) :
    rk.forwardBackward.A (i.castAdd s) (j.natAdd s) = 0 := by
  simp only [forwardBackward, reindex, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]
  rfl

@[simp] theorem forwardBackward_A_right_left (i j : Fin s) :
    rk.forwardBackward.A (i.natAdd s) (j.castAdd s) = rk.b j := by
  simp only [forwardBackward, reindex, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]
  rfl

@[simp] theorem forwardBackward_A_right_right (i j : Fin s) :
    rk.forwardBackward.A (i.natAdd s) (j.natAdd s) = -rk.A i j := by
  simp only [forwardBackward, reindex, finSumFinEquiv_symm_apply_natAdd]
  rfl

@[simp] theorem forwardBackward_b_left (i : Fin s) :
    rk.forwardBackward.b (i.castAdd s) = rk.b i := by
  simp only [forwardBackward, reindex, finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem forwardBackward_b_right (i : Fin s) :
    rk.forwardBackward.b (i.natAdd s) = -rk.b i := by
  simp only [forwardBackward, reindex, finSumFinEquiv_symm_apply_natAdd]
  rfl

theorem isExplicit_forwardBackward (hexp : IsExplicit rk) :
    IsExplicit rk.forwardBackward := by
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> intro hij
  · exact (rk.forwardBackward_A_left_left i j).trans (hexp i j hij)
  · exact rk.forwardBackward_A_left_right i j
  · have := i.isLt
    have := j.isLt
    simp only [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at hij
    omega
  · rw [rk.forwardBackward_A_right_right, hexp i j (by
      simp only [Fin.le_def, Fin.val_natAdd] at hij ⊢; omega), neg_zero]

theorem abscissa_forwardBackward_left (i : Fin s) :
    rk.forwardBackward.abscissa (i.castAdd s) = rk.abscissa i := by
  simp only [abscissa, Fin.sum_univ_add, forwardBackward_A_left_left,
    forwardBackward_A_left_right, Finset.sum_const_zero, add_zero]

theorem abscissa_forwardBackward_right (hcons : weightBullet rk = 1) (i : Fin s) :
    rk.forwardBackward.abscissa (i.natAdd s) = 1 - rk.abscissa i := by
  simp only [abscissa, Fin.sum_univ_add, forwardBackward_A_right_left,
    forwardBackward_A_right_right, Finset.sum_neg_distrib]
  change weightBullet rk + -rk.abscissa i = _
  rw [hcons, sub_eq_add_neg]
  rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The stage matrix, with matrix multiplication rather than pointwise multiplication of functions. -/
def stageMatrix (rk : RungeKutta ι R) : Matrix ι ι R := rk.A

/-- Chain stage weights are the Krylov vectors `A^k 𝟙`. -/
theorem stageWeight_tallTree_eq_mulVec (rk : RungeKutta ι R) (k : ℕ) :
    stageWeight rk (PTree.tallTree k) = rk.stageMatrix ^ k *ᵥ 1 := by
  induction k with
  | zero => ext i; simp [PTree.tallTree, stageWeightList]
  | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ← ih]
      ext i
      simp [PTree.tallTree, stageWeightList, stageMatrix, mulVec, dotProduct]

/-- Unary vertices apply powers of the stage matrix to a stage vector. -/
theorem stageWeight_unaryAbove (rk : RungeKutta ι R) (l : ℕ) (t : PTree) :
    stageWeight rk (PTree.unaryAbove l t) =
      rk.stageMatrix ^ l *ᵥ stageWeight rk t := by
  induction l with
  | zero => simp [PTree.unaryAbove]
  | succ l ih =>
      rw [pow_succ', ← mulVec_mulVec, ← ih]
      ext i
      simp [PTree.unaryAbove, stageWeightList, stageMatrix, mulVec, dotProduct]

/-- The nonlinear two-branch tree supplies multiplication by the diagonal of the abscissae. -/
theorem stageWeight_broom (rk : RungeKutta ι R) (k l : ℕ) :
    stageWeight rk (PTree.broom k l) =
      rk.stageMatrix ^ l *ᵥ
        (Matrix.diagonal rk.abscissa *ᵥ (rk.stageMatrix ^ (k + 1) *ᵥ 1)) := by
  rw [PTree.broom, stageWeight_unaryAbove, ← stageWeight_tallTree_eq_mulVec]
  congr 1
  ext i
  simp [PTree.tallTree, stageWeightList, Matrix.mulVec_diagonal, abscissa]

end Ring

noncomputable section

variable [Field R] [CharZero R] [Invertible (2 : R)]

omit [CharZero R] [Invertible (2 : R)] in
/-- The stability series of the composite is the product `R(z)R(-z)`. -/
theorem stabilityCoeff_forwardBackward {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (n : ℕ) :
    stabilityCoeff rk.forwardBackward n =
      (stabilityPolynomial rk * (stabilityPolynomial rk).comp (-Polynomial.X)).coeff n := by
  rw [coeff_stabilityPolynomial_mul_neg hexp,
    ← toCharacter_series_negScheme, ← toCharacter_series_compose]
  cases n with
  | zero => simp [stabilityCoeff, PTree.chainForest]
  | succ n =>
      simp only [stabilityCoeff, forwardBackward, weight_reindex, PTree.chainForest,
        toCharacter_series_evalForest, forestWeight_singleton, treeWeight_ofPTree]

/-- The final composite moment is nonzero. -/
theorem stabilityCoeff_forwardBackward_last_ne_zero {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    stabilityCoeff rk.forwardBackward (s + s) ≠ 0 := by
  rw [stabilityCoeff_forwardBackward hexp, stabilityPolynomial_mul_neg_eq hs hexp hanti]
  rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X_pow,
    ite_eq_right (by omega : s + s ≠ 0), ite_eq_left (by omega : s + s = 2 * s), zero_add]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (pow_ne_zero _ (stabilityCoeff_last_ne_zero hs hexp hcons hanti))

/-- Every subdiagonal entry of the forward--backward composition is nonzero. -/
theorem forwardBackward_subdiagonal_ne_zero {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (i j : Fin (s + s)) (hij : i.val + 1 = j.val) : rk.forwardBackward.A j i ≠ 0 :=
  subdiagonal_ne_zero_of_stabilityCoeff_last (isExplicit_forwardBackward rk hexp)
    (stabilityCoeff_forwardBackward_last_ne_zero hs hexp hcons hanti) i j hij

/-- Every nonempty-tree weight of the forward--backward composition vanishes through the antisymmetric order. -/
theorem weight_forwardBackward_eq_zero {rk : RungeKutta (Fin s) R} {m : ℕ}
    (hanti : ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) m)
    (t : PTree) (ht : t.order ≤ m) : weight rk.forwardBackward t = 0 := by
  have h := ForestAlgebra.Character.convolution_involution_evalForest_of_hasAntisymOrder hanti
    (RootedForest.singleton (RootedTree.ofPTree t)) (by simpa using ht)
  rw [← toCharacter_series_negScheme, ← toCharacter_series_compose,
    toCharacter_series_evalForest, forestWeight_singleton, treeWeight_ofPTree] at h
  rw [forwardBackward, weight_reindex]
  simpa [HopfAlgebras.ForestAlgebra.Character.unit_evalForest,
    HopfAlgebras.ForestAlgebra.counitCoeff, RootedForest.singleton_ne_zero] using h

/-- The chain moments of the composition vanish below the maximal degree. -/
theorem forwardBackward_chain_moment {rk : RungeKutta (Fin s) R} {m : ℕ}
    (hanti : ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) m)
    (k : ℕ) (hk : k + 1 ≤ m) :
    rk.forwardBackward.b ⬝ᵥ (rk.forwardBackward.stageMatrix ^ k *ᵥ 1) = 0 := by
  rw [← stageWeight_tallTree_eq_mulVec]
  exact weight_forwardBackward_eq_zero hanti _ (by simpa only [PTree.order_tallTree] using hk)

/-- The broom identities are the nonlinear input of Step 2. Here the second branch has `k + 1` vertices. -/
theorem forwardBackward_broom_moment {rk : RungeKutta (Fin s) R} {m : ℕ}
    (hanti : ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) m)
    (k l : ℕ) (hkl : k + 3 + l ≤ m) :
    rk.forwardBackward.b ⬝ᵥ
      (rk.forwardBackward.stageMatrix ^ l *ᵥ
        (Matrix.diagonal rk.forwardBackward.abscissa *ᵥ
          (rk.forwardBackward.stageMatrix ^ (k + 1) *ᵥ 1))) = 0 := by
  rw [← stageWeight_broom]
  exact weight_forwardBackward_eq_zero hanti _ (by simpa only [PTree.order_broom] using hkl)

end

end RungeKutta

end BSeries
