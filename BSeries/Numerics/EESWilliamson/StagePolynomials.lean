import BSeries.Numerics.EESWilliamson.ReverseShift
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Stage polynomials and multiplication by the independent variable

The reverse-shift matrix already used for tableau reconstruction is the coefficient matrix of multiplication by `X` in the degree-ordered stage polynomials. Evaluation at roots of the stability polynomial removes its output term.
-/

namespace BSeries.RungeKutta
open HopfAlgebras Matrix Polynomial
open scoped BigOperators
noncomputable section
variable {R : Type*} [Field R] {s : ℕ}

def stagePolynomial (rk : RungeKutta (Fin s) R) (i : Fin s) : R[X] := by
  classical
  exact Polynomial.ofFn s (rk.krylovMatrix i)

theorem coeff_stagePolynomial {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk)
    (i : Fin s) (k : ℕ) : (stagePolynomial rk i).coeff k = stageWeight rk (PTree.tallTree k) i := by
  classical
  by_cases hk : k < s
  · exact ofFn_coeff_eq_val_of_lt _ hk
  · rw [stagePolynomial, ofFn_coeff_eq_zero_of_ge _ (by omega)]
    exact (stageWeight_tallTree_eq_zero_of_lt hexp k i (by have := i.isLt; omega)).symm

/-- Away from the last stage, the reverse shift is multiplication by `X` in the stage-polynomial basis. -/
theorem reverseShift_stagePolynomial {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdet : rk.krylovMatrix.det ≠ 0)
    (i : Fin s) (hi : i.val + 1 < s) :
    (∑ j, C (rk.reverseShift i j) * stagePolynomial rk j) = X * stagePolynomial rk i := by
  classical
  ext k
  simp only [finsetSum_coeff, coeff_C_mul, coeff_stagePolynomial hexp]
  by_cases hk : k < s
  · have h := congrFun (reverseShift_mul_chain hdet k hk) i
    change (∑ j, rk.reverseShift i j * stageWeight rk (PTree.tallTree k) j) = _ at h
    rw [h]
    cases k with
    | zero => simp
    | succ k => simp [coeff_stagePolynomial hexp]
  · have hzero (j : Fin s) : stageWeight rk (PTree.tallTree k) j = 0 :=
      stageWeight_tallTree_eq_zero_of_lt hexp k j (by have := j.isLt; omega)
    simp only [hzero, mul_zero, Finset.sum_const_zero]
    cases k with
    | zero => simp
    | succ k =>
        rw [coeff_X_mul, coeff_stagePolynomial hexp]
        exact (stageWeight_tallTree_eq_zero_of_lt hexp k i (by omega)).symm

theorem stagePolynomial_forwardBackward_left {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (i : Fin s) :
    stagePolynomial rk.forwardBackward (i.castAdd s) = stagePolynomial rk i := by
  ext k
  rw [coeff_stagePolynomial (isExplicit_forwardBackward rk hexp), coeff_stagePolynomial hexp,
    stageWeight_forwardBackward_left]

theorem stagePolynomial_forwardBackward_output {rk : RungeKutta (Fin s) R}
    (hs : 0 < s) (hexp : IsExplicit rk) :
    stagePolynomial rk.forwardBackward ((⟨0, hs⟩ : Fin s).natAdd s) = stabilityPolynomial rk := by
  ext k
  rw [coeff_stagePolynomial (isExplicit_forwardBackward rk hexp), coeff_stabilityPolynomial hexp]
  cases k with
  | zero => simp [PTree.tallTree, stageWeightList, stabilityCoeff]
  | succ k =>
      rw [stageWeight_tallTree_succ, forwardBackward_mulVec_right]
      have hz : (∑ j, rk.A ⟨0, hs⟩ j * stageWeight rk.forwardBackward (PTree.tallTree k) (j.natAdd s)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [hexp _ j (by change 0 ≤ j.val; omega), zero_mul]
      rw [hz, sub_zero]
      simp only [stageWeight_forwardBackward_left]
      rfl

variable {K : Type*} [Field K]

/-- Columns are stage polynomials evaluated at the given points. Mathlib's Vandermonde matrix supplies the evaluation isomorphism. -/
def stageEvaluation (rk : RungeKutta (Fin s) R) (f : R →+* K) (x : Fin s → K) :
    Matrix (Fin s) (Fin s) K := vandermonde x * (rk.krylovMatrix.map f)ᵀ

theorem stageEvaluation_apply (rk : RungeKutta (Fin s) R) (f : R →+* K)
    (x : Fin s → K) (l i : Fin s) :
    stageEvaluation rk f x l i = (stagePolynomial rk i).eval₂ f (x l) := by
  classical
  simp only [stageEvaluation, Matrix.mul_apply, vandermonde_apply, transpose_apply,
    Matrix.map_apply, stagePolynomial, ofFn_eq_sum_monomial, eval₂_finsetSum, eval₂_monomial]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem det_stageEvaluation_ne_zero (rk : RungeKutta (Fin s) R) (f : R →+* K)
    (x : Fin s → K) (hx : Function.Injective x) (hdet : rk.krylovMatrix.det ≠ 0) :
    (stageEvaluation rk f x).det ≠ 0 := by
  rw [stageEvaluation, det_mul, det_transpose]
  have hmap : (rk.krylovMatrix.map f).det = f rk.krylovMatrix.det := (f.map_det _).symm
  rw [hmap]
  exact mul_ne_zero (det_vandermonde_ne_zero_iff.mpr hx) ((_root_.map_ne_zero f).mpr hdet)

/-- At a root of the stability polynomial, the next-stage term in the final original row vanishes. -/
theorem stageEvaluation_mul_reverseShift {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk)
    (hsub : ∀ i j : Fin (s + s), i.val + 1 = j.val → rk.forwardBackward.A j i ≠ 0)
    (f : R →+* K) (x : Fin s → K)
    (hx : ∀ l, (stabilityPolynomial rk).eval₂ f (x l) = 0) :
    diagonal x * stageEvaluation rk f x = stageEvaluation rk f x *
      (fun i j : Fin s => f (rk.forwardBackward.reverseShift (i.castAdd s) (j.castAdd s)))ᵀ := by
  classical
  have hexpc := isExplicit_forwardBackward rk hexp
  have hdet := det_krylovMatrix_ne_zero hexpc hsub
  ext l i
  have hs : 0 < s := by have := i.isLt; omega
  have h := congrArg (Polynomial.eval₂RingHom f (x l))
    (reverseShift_stagePolynomial hexpc hdet (i.castAdd s) (by simp only [Fin.val_castAdd]; have := i.isLt; omega))
  simp only [coe_eval₂RingHom, eval₂_add, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_X, Fin.sum_univ_add,
    stagePolynomial_forwardBackward_left hexp] at h
  have hright : (∑ j : Fin s,
      f (rk.forwardBackward.reverseShift (i.castAdd s) (j.natAdd s)) *
        (stagePolynomial rk.forwardBackward (j.natAdd s)).eval₂ f (x l)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val = 0
    · have heq : j = ⟨0, hs⟩ := Fin.ext hj
      rw [heq, stagePolynomial_forwardBackward_output hs hexp, hx, mul_zero]
    · rw [reverseShift_eq_zero_of_lt hexpc hsub (i.castAdd s) (j.natAdd s)
        (by simp only [Fin.val_castAdd, Fin.val_natAdd]; have := i.isLt; omega), map_zero, zero_mul]
  rw [hright, add_zero] at h
  rw [diagonal_mul, stageEvaluation_apply, Matrix.mul_apply]
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [stageEvaluation_apply]
  exact mul_comm ..

end
end BSeries.RungeKutta
