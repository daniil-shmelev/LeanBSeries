import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.LinearCombination

/-!
# Irreducible tridiagonal matrices

An eigenvector of an upper Hessenberg matrix with nonzero superdiagonal is determined by its first coordinate. A tridiagonal matrix with both adjacent diagonals nonzero is symmetric for a nonsingular diagonal bilinear form.
-/

open Module
open scoped BigOperators

namespace Matrix
noncomputable section
variable {K : Type*} [Field K] {n : ℕ}

theorem eigenvector_eq_zero_of_first (T : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (hupper : ∀ i j : Fin n, i.val + 1 < j.val → T i j = 0)
    (hsuper : ∀ i j : Fin n, i.val + 1 = j.val → T i j ≠ 0)
    (v : Fin n → K) (c : K) (hv : T *ᵥ v = c • v) (hfirst : v ⟨0, hn⟩ = 0) :
    v = 0 := by
  have hzero (k : ℕ) (hk : k < n) : v ⟨k, hk⟩ = 0 := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk₀ : k = 0
      · subst k; exact hfirst
      let i : Fin n := ⟨k - 1, by omega⟩
      let j : Fin n := ⟨k, hk⟩
      have hi : v i = 0 := ih (k - 1) (by omega) i.isLt
      have h := congrFun hv i
      change (∑ l, T i l * v l) = c * v i at h
      rw [Finset.sum_eq_single j, hi, mul_zero] at h
      · exact (mul_eq_zero.mp h).resolve_left (hsuper i j (by dsimp [i, j]; omega))
      · intro l _ hlj
        by_cases hl : l.val < k
        · rw [ih l.val hl l.isLt, mul_zero]
        · rw [hupper i l (by have : l.val ≠ j.val := fun h => hlj (Fin.ext h); dsimp [i, j] at *; omega), zero_mul]
      · simp
  ext i
  exact hzero i.val i.isLt

theorem eigenvalues_injective_of_hessenberg (T : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (hupper : ∀ i j : Fin n, i.val + 1 < j.val → T i j = 0)
    (hsuper : ∀ i j : Fin n, i.val + 1 = j.val → T i j ≠ 0)
    (b : Basis (Fin n) K (Fin n → K)) (c : Fin n → K)
    (hb : ∀ i, T *ᵥ b i = c i • b i) : Function.Injective c := by
  classical
  let z : Fin n := ⟨0, hn⟩
  have hfirst (i : Fin n) : b i z ≠ 0 := fun h => b.ne_zero i
    (eigenvector_eq_zero_of_first T hn hupper hsuper (b i) (c i) (hb i) h)
  intro i j hij
  by_contra hne
  let v := b j z • b i - b i z • b j
  have hv : T *ᵥ v = c i • v := by
    simp only [v, mulVec_sub, mulVec_smul, hb, ← hij, smul_sub]
    module
  have hz : v = 0 := eigenvector_eq_zero_of_first T hn hupper hsuper v (c i) hv
    (by dsimp [v, z]; simp [mul_comm])
  have h := congrArg (fun w => b.repr w i) hz
  apply hfirst j
  simpa [v, hne, Ne.symm hne] using h

theorem exists_diagonal_symmetrizer (T : Matrix (Fin n) (Fin n) K)
    (hband : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → T i j = 0)
    (hadj : ∀ i j : Fin n, i.val + 1 = j.val → T i j ≠ 0 ∧ T j i ≠ 0) :
    ∃ d : Fin n → K, (∀ i, d i ≠ 0) ∧ Tᵀ * diagonal d = diagonal d * T := by
  classical
  let d (i : Fin n) : K := ∏ j : Fin i.val,
    T ⟨j.val, by omega⟩ ⟨j.val + 1, by omega⟩ /
      T ⟨j.val + 1, by omega⟩ ⟨j.val, by omega⟩
  have hd (i : Fin n) : d i ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact div_ne_zero (hadj _ _ rfl).1 (hadj _ _ rfl).2
  have hnext (i j : Fin n) (hij : i.val + 1 = j.val) : T j i * d j = d i * T i j := by
    have hprod : d j = d i * (T i j / T j i) := by
      rcases i with ⟨i, hi⟩
      rcases j with ⟨j, hj⟩
      dsimp at hij
      subst j
      simp only [d, Fin.prod_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [hprod]
    have hne := (hadj i j hij).2
    field_simp
  refine ⟨d, hd, ?_⟩
  ext i j
  simp only [mul_diagonal, diagonal_mul, transpose_apply]
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · by_cases h : i.val + 1 = j.val
    · exact hnext i j h
    · rw [hband i j (Or.inl (by omega)), hband j i (Or.inr (by omega))]; simp
  · have h : i = j := Fin.ext hij
    subst j
    exact mul_comm ..
  · by_cases h : j.val + 1 = i.val
    · simpa only [mul_comm] using (hnext j i h).symm
    · rw [hband i j (Or.inr (by omega)), hband j i (Or.inl (by omega))]; simp

/-- A degree-ordered eigenbasis of an irreducible tridiagonal operator makes any diagonal multiplication operator tridiagonal too, as soon as degree supplies its upper Hessenberg zeros. The diagonal Gram matrix expresses orthogonality for the symmetrizing bilinear form. -/
theorem tridiagonal_of_eigenbasis (T W H : Matrix (Fin n) (Fin n) K)
    (hn : 0 < n) (hW : W.det ≠ 0) (c x : Fin n → K)
    (hband : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val → T i j = 0)
    (hadj : ∀ i j : Fin n, i.val + 1 = j.val → T i j ≠ 0 ∧ T j i ≠ 0)
    (hTW : T * W = W * diagonal c) (hXW : diagonal x * W = W * Hᵀ)
    (hH : ∀ i j : Fin n, i.val + 1 < j.val → H i j = 0) :
    ∀ i j : Fin n, j.val + 1 < i.val → H i j = 0 := by
  classical
  let b := (Pi.basisFun K (Fin n)).map
    (W.toLinearEquiv' (W.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hW)))
  have hb (i : Fin n) : b i = W.col i := by
    ext j
    simp only [b, Basis.map_apply, Pi.basisFun_apply]
    change (W *ᵥ Pi.single i 1) j = W j i
    simp only [mulVec_single_one, col_apply]
  have heig (i : Fin n) : T *ᵥ b i = c i • b i := by
    rw [hb]
    ext j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M j i) hTW
    rw [mul_diagonal] at h
    change (T *ᵥ W.col i) j = W j i * c i at h
    simpa only [col_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
  have hinj := eigenvalues_injective_of_hessenberg T hn (fun i j h => hband i j (Or.inl h))
    (fun i j h => (hadj i j h).1) b c heig
  obtain ⟨d, hd, hsym⟩ := exists_diagonal_symmetrizer T hband hadj
  let G := Wᵀ * diagonal d * W
  have hTWt : Wᵀ * Tᵀ = diagonal c * Wᵀ := by
    simpa using congrArg Matrix.transpose hTW
  have hcomm : diagonal c * G = G * diagonal c := by
    dsimp [G]
    calc
      _ = (diagonal c * Wᵀ) * (diagonal d * W) := by simp only [Matrix.mul_assoc]
      _ = (Wᵀ * Tᵀ) * (diagonal d * W) := by rw [hTWt]
      _ = Wᵀ * (Tᵀ * diagonal d) * W := by simp only [Matrix.mul_assoc]
      _ = Wᵀ * (diagonal d * T) * W := by rw [hsym]
      _ = Wᵀ * diagonal d * (T * W) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hTW]; simp only [Matrix.mul_assoc]
  have hG : G = diagonal (fun i => G i i) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · rw [diagonal_apply_ne _ hij]
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hcomm
      simp only [diagonal_mul, mul_diagonal] at h
      apply (mul_eq_zero.mp (show (c i - c j) * G i j = 0 by linear_combination h)).resolve_left
      exact sub_ne_zero.mpr (fun h => hij (hinj h))
  have hnorm (i : Fin n) : G i i ≠ 0 := by
    have hdet : G.det ≠ 0 := by
      simp only [G, det_mul, det_transpose, det_diagonal]
      exact mul_ne_zero (mul_ne_zero hW (Finset.prod_ne_zero_iff.mpr (fun i _ => hd i))) hW
    rw [hG, det_diagonal] at hdet
    exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
  have hXWt : Wᵀ * diagonal x = H * Wᵀ := by
    simpa using congrArg Matrix.transpose hXW
  have hself : H * G = G * Hᵀ := by
    dsimp [G]
    calc
      _ = (H * Wᵀ) * (diagonal d * W) := by simp only [Matrix.mul_assoc]
      _ = (Wᵀ * diagonal x) * (diagonal d * W) := by rw [hXWt]
      _ = Wᵀ * (diagonal x * diagonal d) * W := by simp only [Matrix.mul_assoc]
      _ = Wᵀ * (diagonal d * diagonal x) * W := by
        simp only [diagonal_mul_diagonal, mul_comm]
      _ = Wᵀ * diagonal d * (diagonal x * W) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hXW]; simp only [Matrix.mul_assoc]
  intro i j hji
  rw [hG] at hself
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) hself
  simp only [mul_diagonal, diagonal_mul, transpose_apply, hH j i hji, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_right (hnorm j)

end
end Matrix
