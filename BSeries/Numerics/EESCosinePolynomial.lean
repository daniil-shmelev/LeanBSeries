/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESCosine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial identities for the cosine EES tableau

The Chebyshev primitive and Lagrange cancellation in the proof of
Proposition `EES_2_m` in Shmelev et al., `main_sn_2.tex`.
-/

namespace BSeries.RungeKutta

noncomputable section

open Polynomial.Chebyshev

/-- The angle of a cosine stage node, with zero-based indices. -/
def eesCosinePhase (s n : ℕ) : ℝ := ((n : ℝ) + 1 / 2) * eesCosineAngle s

/-- The Chebyshev nodes used in the polynomial order conditions. -/
def eesCosineNode (s : ℕ) (i : Fin s) : ℝ := Real.cos (eesCosinePhase s i.val)

theorem cosine_difference_sin (θ : ℝ) (n : ℕ) :
    Real.cos (n * θ) - Real.cos ((n + 1 : ℕ) * θ) =
      2 * Real.sin (θ / 2) * Real.sin (((n : ℝ) + 1 / 2) * θ) := by
  rw [Real.cos_sub_cos]
  have hsum : ((n : ℝ) * θ + ((n + 1 : ℕ) : ℝ) * θ) / 2 =
      ((n : ℝ) + 1 / 2) * θ := by push_cast; ring
  have hsub : ((n : ℝ) * θ - ((n + 1 : ℕ) : ℝ) * θ) / 2 = -(θ / 2) := by
    push_cast
    ring
  rw [hsum, hsub, Real.sin_neg]
  ring

theorem eesCosineD_sin {s : ℕ} (i : Fin s) :
    eesCosineD s i = 2 * Real.sin (eesCosineAngle s / 2) *
      Real.sin (eesCosinePhase s i.val) :=
  cosine_difference_sin _ _

theorem eesCosinePhase_pos {s : ℕ} (hs : 0 < s) (n : ℕ) :
    0 < eesCosinePhase s n := by
  unfold eesCosinePhase
  exact mul_pos (by positivity) (eesCosineAngle_pos hs)

theorem eesCosinePhase_lt_pi {s : ℕ} (i : Fin s) :
    eesCosinePhase s i.val < Real.pi := by
  have hs : 0 < s := by have := i.isLt; omega
  rw [← mul_eesCosineAngle hs]
  unfold eesCosinePhase
  apply mul_lt_mul_of_pos_right _ (eesCosineAngle_pos hs)
  have hi : ((i.val + 1 : ℕ) : ℝ) ≤ s := Nat.cast_le.mpr (by omega)
  push_cast at hi
  linarith

theorem eesCosineNode_injective {s : ℕ} : Function.Injective (eesCosineNode s) := by
  intro i j hij
  apply Fin.ext
  by_contra hne
  have hs : 0 < s := by have := i.isLt; omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hphase : eesCosinePhase s i.val < eesCosinePhase s j.val := by
      unfold eesCosinePhase
      apply mul_lt_mul_of_pos_right _ (eesCosineAngle_pos hs)
      linarith [show (i.val : ℝ) < j.val from Nat.cast_lt.mpr hlt]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (eesCosinePhase_pos hs _).le
      (eesCosinePhase_lt_pi j).le hphase
    exact (ne_of_lt h) hij.symm
  · have hphase : eesCosinePhase s j.val < eesCosinePhase s i.val := by
      unfold eesCosinePhase
      apply mul_lt_mul_of_pos_right _ (eesCosineAngle_pos hs)
      linarith [show (j.val : ℝ) < i.val from Nat.cast_lt.mpr hlt]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (eesCosinePhase_pos hs _).le
      (eesCosinePhase_lt_pi i).le hphase
    exact (ne_of_lt h) hij

private theorem mul_eesCosinePhase {s : ℕ} (i : Fin s) :
    (s : ℝ) * eesCosinePhase s i.val = (i.val : ℝ) * Real.pi + Real.pi / 2 := by
  have hs : 0 < s := by have := i.isLt; omega
  unfold eesCosinePhase
  calc
    _ = ((i.val : ℝ) + 1 / 2) * ((s : ℝ) * eesCosineAngle s) := by ring
    _ = _ := by rw [mul_eesCosineAngle hs]; ring

theorem eesCosineNode_root {s : ℕ} (i : Fin s) :
    (T ℝ s).eval (eesCosineNode s i) = 0 := by
  simp only [eesCosineNode, T_real_cos, Int.cast_natCast, mul_eesCosinePhase]
  simp [Real.cos_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]

theorem eesCosineNode_derivative {s : ℕ} (i : Fin s) :
    (T ℝ s).derivative.eval (eesCosineNode s i) * Real.sin (eesCosinePhase s i.val) =
      (s : ℝ) * alternatingSign i := by
  rw [T_derivative_eq_U]
  simp only [Polynomial.eval_mul, Int.cast_natCast, eesCosineNode]
  rw [mul_assoc, U_real_cos]
  simp [mul_eesCosinePhase, Real.sin_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi,
    alternatingSign_eq_pow]

private theorem eesCosine_chebyshev_nodal (s : ℕ) :
    T ℝ s = Polynomial.C (T ℝ s).leadingCoeff *
      Lagrange.nodal Finset.univ (eesCosineNode s) := by
  classical
  have hlc : (T ℝ s).leadingCoeff ≠ 0 := by rw [leadingCoeff_T]; positivity
  apply Polynomial.eq_of_degree_le_of_eval_index_eq (Finset.univ : Finset (Fin s))
    eesCosineNode_injective.injOn
  · simp [degree_T]
  · rw [Polynomial.degree_C_mul hlc]
    simp [degree_T]
  · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Lagrange.nodal_monic.leadingCoeff, mul_one]
  · intro i _
    rw [eesCosineNode_root, Polynomial.eval_mul, Polynomial.eval_C,
      Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero]

private theorem cosine_primitive_step (a b α η : ℝ) (hb : Real.sin b ≠ 0) :
    Real.sin η / Real.sin b * (Real.cos α - Real.cos (a + b)) =
      Real.sin η / Real.sin b * (Real.cos α - Real.cos (a - b)) +
        2 * Real.sin η * Real.sin a := by
  rw [Real.cos_add, Real.cos_sub]
  field_simp
  ring

private theorem alternatingPrefix_sine (θ : ℝ) (k n : ℕ)
    (hθ : Real.sin ((k : ℝ) * θ) ≠ 0) :
    alternatingPrefix (fun j => 2 * Real.sin (θ / 2) *
        Real.sin ((k : ℝ) * (((j : ℝ) + 1 / 2) * θ))) n =
      Real.sin (θ / 2) / Real.sin ((k : ℝ) * θ) *
        (Real.cos ((k : ℝ) * (θ / 2)) -
          Real.cos ((k : ℝ) * (((n : ℝ) + 1 / 2) * θ))) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [alternatingPrefix_zero]
      norm_num only [Nat.cast_zero, zero_add]
      rw [show (1 / 2 : ℝ) * θ = θ / 2 from by ring, sub_self, mul_zero]
  | one =>
      rw [alternatingPrefix_one]
      have h := cosine_primitive_step ((k : ℝ) * (θ / 2)) ((k : ℝ) * θ)
        ((k : ℝ) * (θ / 2)) (θ / 2) hθ
      have hm : (k : ℝ) * (θ / 2) - (k : ℝ) * θ = -((k : ℝ) * (θ / 2)) := by ring
      rw [hm, Real.cos_neg, sub_self, mul_zero, zero_add] at h
      have hp : (k : ℝ) * (θ / 2) + (k : ℝ) * θ =
          (k : ℝ) * ((1 + 1 / 2) * θ) := by ring
      rw [hp] at h
      norm_num only [Nat.cast_zero, Nat.cast_one, zero_add]
      rw [show (1 / 2 : ℝ) * θ = θ / 2 from by ring]
      norm_num at h
      exact h.symm
  | more n ih _ =>
      rw [alternatingPrefix_add_two, ih]
      have h := cosine_primitive_step ((k : ℝ) * (((n : ℝ) + 1 + 1 / 2) * θ))
        ((k : ℝ) * θ) ((k : ℝ) * (θ / 2)) (θ / 2) hθ
      have hp : (k : ℝ) * (((n : ℝ) + 1 + 1 / 2) * θ) + (k : ℝ) * θ =
          (k : ℝ) * ((((n + 2 : ℕ) : ℝ) + 1 / 2) * θ) := by push_cast; ring
      have hm : (k : ℝ) * (((n : ℝ) + 1 + 1 / 2) * θ) - (k : ℝ) * θ =
          (k : ℝ) * (((n : ℝ) + 1 / 2) * θ) := by ring
      rw [hp, hm] at h
      simpa only [Nat.cast_add, Nat.cast_one] using h.symm

/-- The Chebyshev primitive, proved from the alternating row recurrence. -/
theorem eesCosine_chebyshev_primitive {s k : ℕ} (hk : 0 < k) (hks : k < s) (i : Fin s) :
    (∑ j, (eesCosine s).A i j * (U ℝ ((k : ℤ) - 1)).eval (eesCosineNode s j)) =
      Real.sin (eesCosineAngle s / 2) / Real.sin ((k : ℝ) * eesCosineAngle s) *
        (Real.cos ((k : ℝ) * (eesCosineAngle s / 2)) -
          (T ℝ k).eval (eesCosineNode s i)) := by
  have hs : 0 < s := by omega
  have hsin : Real.sin ((k : ℝ) * eesCosineAngle s) ≠ 0 := by
    apply ne_of_gt
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos (Nat.cast_pos.mpr hk) (eesCosineAngle_pos hs)
    · rw [← mul_eesCosineAngle hs]
      exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hks) (eesCosineAngle_pos hs)
  have hterm (n : ℕ) :
      (Real.cos (n * eesCosineAngle s) - Real.cos ((n + 1 : ℕ) * eesCosineAngle s)) *
          (U ℝ ((k : ℤ) - 1)).eval (Real.cos (eesCosinePhase s n)) =
        2 * Real.sin (eesCosineAngle s / 2) * Real.sin ((k : ℝ) * eesCosinePhase s n) := by
    rw [cosine_difference_sin]
    change (2 * Real.sin (eesCosineAngle s / 2) * Real.sin (eesCosinePhase s n)) *
      (U ℝ ((k : ℤ) - 1)).eval (Real.cos (eesCosinePhase s n)) = _
    rw [mul_right_comm _ (Real.sin (eesCosinePhase s n)), mul_assoc, U_real_cos]
    simp
  unfold eesCosine eesCosineD eesCosineNode
  rw [alternatingTableau_apply
    (fun n : ℕ => Real.cos (n * eesCosineAngle s) - Real.cos ((n + 1 : ℕ) * eesCosineAngle s))
    (fun n : ℕ => (U ℝ ((k : ℤ) - 1)).eval (Real.cos (eesCosinePhase s n))) i]
  simp_rw [hterm]
  simp only [eesCosinePhase]
  rw [alternatingPrefix_sine _ _ _ hsin, T_real_cos]
  simp only [Int.cast_natCast]

/-- The primitive belongs to the polynomial space of the required degree. -/
theorem eesCosine_chebyshev_stagePolynomial {s k : ℕ} (hk : 0 < k) (hks : k < s) :
    IsStagePolynomial (eesCosineNode s) k
      (fun i => ∑ j, (eesCosine s).A i j * (U ℝ ((k : ℤ) - 1)).eval (eesCosineNode s j)) := by
  have hbase : IsStagePolynomial (eesCosineNode s) k (fun i =>
      Real.cos ((k : ℝ) * (eesCosineAngle s / 2)) - (T ℝ k).eval (eesCosineNode s i)) := by
    refine ⟨Polynomial.C (Real.cos ((k : ℝ) * (eesCosineAngle s / 2))) - T ℝ k, ?_, ?_⟩
    · simpa only [Polynomial.natDegree_C, natDegree_T, Int.natAbs_natCast, zero_le,
        max_eq_right] using Polynomial.natDegree_sub_le
          (Polynomial.C (Real.cos ((k : ℝ) * (eesCosineAngle s / 2)))) (T ℝ k)
    · intro i
      simp
  convert hbase.smul (Real.sin (eesCosineAngle s / 2) /
    Real.sin ((k : ℝ) * eesCosineAngle s)) using 1
  funext i
  exact eesCosine_chebyshev_primitive hk hks i

/-- The alternating matrix raises the degree of low-degree stage polynomials by at most one. -/
theorem eesCosine_polynomial_closure {s k : ℕ} (hk : k + 1 < s)
    {f : Fin s → ℝ} (hf : IsStagePolynomial (eesCosineNode s) k f) :
    IsStagePolynomial (eesCosineNode s) (k + 1) (fun i => ∑ j, (eesCosine s).A i j * f j) := by
  classical
  obtain ⟨p, hp, hf⟩ := hf
  let seq : Polynomial.Sequence ℝ :=
    { elems' := fun n => U ℝ n, degree_eq' := fun n => degree_U_natCast ℝ n }
  have hmem : p ∈ Polynomial.degreeLT ℝ (k + 1) := by
    rw [Polynomial.mem_degreeLT]
    exact lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp)
  rw [← Polynomial.Sequence.span_degreeLT seq (by
      intro n _
      simp only [seq, leadingCoeff_U_natCast]
      exact isUnit_iff_ne_zero.mpr (by positivity)),
    show Set.Iio (k + 1) = (Finset.range (k + 1) : Set ℕ) by ext n; simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨a, ha⟩ := hmem
  change (∑ n ∈ Finset.range (k + 1), a n • U ℝ n) = p at ha
  have hpoly : IsStagePolynomial (eesCosineNode s) (k + 1)
      (fun i => ∑ n ∈ Finset.range (k + 1), a n *
        (∑ j, (eesCosine s).A i j * (U ℝ n).eval (eesCosineNode s j))) := by
    apply IsStagePolynomial.sum
    intro n hn
    have hn' := Finset.mem_range.mp hn
    have h := eesCosine_chebyshev_stagePolynomial (s := s) (k := n + 1) (by omega) (by omega)
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h
    exact (h.mono (by omega)).smul (a n)
  convert hpoly using 1
  funext i
  simp_rw [hf, ← ha, Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Lagrange interpolation makes the signed quadrature weights annihilate low-degree polynomials. -/
theorem eesCosine_polynomial_annihilation {s k : ℕ} (hk : k + 1 < s)
    {f : Fin s → ℝ} (hf : IsStagePolynomial (eesCosineNode s) k f) :
    ∑ i, (eesCosine s).b i * alternatingSign i * f i = 0 := by
  classical
  obtain ⟨p, hp, hf⟩ := hf
  let D : Fin s → ℝ := fun i =>
    ∏ j ∈ Finset.univ.erase i, (eesCosineNode s i - eesCosineNode s j)
  let K : ℝ := (s : ℝ) * Real.sin (eesCosineAngle s / 2) / (T ℝ s).leadingCoeff
  have hdegree : p.degree < s :=
    lt_of_le_of_lt p.degree_le_natDegree (by exact_mod_cast hp.trans_lt (by omega : k < s))
  have hsum := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin s)))
    eesCosineNode_injective.injOn (P := p) (by simpa using hdegree)
  have hcoeff : p.coeff (s - 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hzero : (∑ i, p.eval (eesCosineNode s i) / D i) = 0 := by
    simpa only [Finset.card_univ, Fintype.card_fin, hcoeff, D] using hsum.symm
  have hv (i : Fin s) : (eesCosine s).b i * alternatingSign i = K / D i := by
    have hD : D i ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j hj
      apply sub_ne_zero.mpr
      intro hij
      exact (Finset.mem_erase.mp hj).1 (eesCosineNode_injective hij).symm
    have hb : (eesCosine s).b i = Real.sin (eesCosineAngle s / 2) *
        Real.sin (eesCosinePhase s i.val) := by
      change eesCosineD s i / 2 = _
      rw [eesCosineD_sin]
      ring
    have hweighted : (eesCosine s).b i * alternatingSign i *
        (T ℝ s).derivative.eval (eesCosineNode s i) =
          (s : ℝ) * Real.sin (eesCosineAngle s / 2) := by
      rw [hb]
      calc
        _ = Real.sin (eesCosineAngle s / 2) * alternatingSign i *
            ((T ℝ s).derivative.eval (eesCosineNode s i) * Real.sin (eesCosinePhase s i.val)) := by ring
        _ = Real.sin (eesCosineAngle s / 2) * alternatingSign i *
            ((s : ℝ) * alternatingSign i) := by rw [eesCosineNode_derivative]
        _ = _ := by unfold alternatingSign; split_ifs <;> ring
    have hderivative := congrArg
      (fun P : Polynomial ℝ => P.derivative.eval (eesCosineNode s i)) (eesCosine_chebyshev_nodal s)
    simp only [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C] at hderivative
    rw [Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ i),
      Lagrange.eval_nodal] at hderivative
    change (T ℝ s).derivative.eval (eesCosineNode s i) = (T ℝ s).leadingCoeff * D i at hderivative
    rw [hderivative] at hweighted
    apply (eq_div_iff hD).mpr
    unfold K
    apply (eq_div_iff (by rw [leadingCoeff_T]; positivity : (T ℝ s).leadingCoeff ≠ 0)).mpr
    linear_combination hweighted
  calc
    _ = ∑ i, K * (p.eval (eesCosineNode s i) / D i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf i, hv i]
      ring
    _ = K * (∑ i, p.eval (eesCosineNode s i) / D i) := (Finset.mul_sum _ _ _).symm
    _ = 0 := by rw [hzero, mul_zero]

/-- The polynomial hypotheses of the general rank-one order lemma. -/
theorem rankOneOrderConditions_eesCosine {s : ℕ} (hs : 2 ≤ s) :
    RankOneOrderConditions (eesCosine s) alternatingSign (eesCosineNode s) (s - 1) where
  closure k hk _ hf := eesCosine_polynomial_closure (by omega) hf
  annihilation k hk _ hf := eesCosine_polynomial_annihilation (by omega) hf
  defect := alternatingTableau_rank_one _

instance : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)

theorem hasAntisymOrder_eesCosine {s : ℕ} (hs : 2 ≤ s) :
    ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series (eesCosine s))) (2 * s - 1) := by
  have h := (rankOneOrderConditions_eesCosine hs).hasAntisymOrder Fin.revPerm
    (reindex_adjoint_eesCosine s)
  simpa only [show 2 * (s - 1) + 1 = 2 * s - 1 by omega] using h

end

end BSeries.RungeKutta
