/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Alternating
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Cosine EES methods

The `s`-stage family of Shmelev et al., Proposition `EES_2_m` in
`main_sn_2.tex`, Section `A General Family of EES(2,m) Schemes`.
With zero-based indices, `d_j = cos(j * pi / s) - cos((j+1) * pi / s)`.
-/

namespace BSeries.RungeKutta

noncomputable section

/-- The angle between consecutive cosine nodes. -/
def eesCosineAngle (s : ℕ) : ℝ := Real.pi / s

/-- Twice the quadrature weight of a cosine EES stage. -/
def eesCosineD (s : ℕ) (j : Fin s) : ℝ :=
  Real.cos (j.val * eesCosineAngle s) -
    Real.cos ((j.val + 1 : ℕ) * eesCosineAngle s)

/-- The cosine method with `s` stages; the EES order claim uses `s ≥ 2`. -/
def eesCosine (s : ℕ) : RungeKutta (Fin s) ℝ :=
  alternatingTableau (eesCosineD s)

theorem isExplicit_eesCosine (s : ℕ) : IsExplicit (eesCosine s) :=
  isExplicit_alternatingTableau _

theorem eesCosineAngle_pos {s : ℕ} (hs : 0 < s) : 0 < eesCosineAngle s :=
  div_pos Real.pi_pos (Nat.cast_pos.mpr hs)

theorem mul_eesCosineAngle {s : ℕ} (hs : 0 < s) :
    (s : ℝ) * eesCosineAngle s = Real.pi := by
  unfold eesCosineAngle
  have hs' : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  field_simp

theorem eesCosineD_pos {s : ℕ} (hs : 0 < s) (j : Fin s) :
    0 < eesCosineD s j := by
  unfold eesCosineD
  apply sub_pos.mpr
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · exact mul_nonneg (Nat.cast_nonneg _) (eesCosineAngle_pos hs).le
  · calc
      ((j.val + 1 : ℕ) : ℝ) * eesCosineAngle s ≤ (s : ℝ) * eesCosineAngle s :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega))
          (eesCosineAngle_pos hs).le
      _ = Real.pi := mul_eesCosineAngle hs
  · apply mul_lt_mul_of_pos_right _ (eesCosineAngle_pos hs)
    exact_mod_cast Nat.lt_succ_self j.val

theorem eesCosineD_rev {s : ℕ} (j : Fin s) : eesCosineD s j.rev = eesCosineD s j := by
  have hs : 0 < s := by have := j.isLt; omega
  have hi : j.rev.val + (j.val + 1) = s := by simp only [Fin.val_rev]; omega
  have hangle : (j.rev.val : ℝ) * eesCosineAngle s +
      ((j.val + 1 : ℕ) : ℝ) * eesCosineAngle s = Real.pi := by
    rw [← add_mul, ← Nat.cast_add, hi, mul_eesCosineAngle hs]
  have hfirst : (j.rev.val : ℝ) * eesCosineAngle s =
      Real.pi - ((j.val + 1 : ℕ) : ℝ) * eesCosineAngle s := by linarith
  have hsecond : ((j.rev.val + 1 : ℕ) : ℝ) * eesCosineAngle s =
      Real.pi - (j.val : ℝ) * eesCosineAngle s := by push_cast at *; linarith
  simp only [eesCosineD, hfirst, hsecond, Real.cos_pi_sub]
  ring

theorem reindex_adjoint_eesCosine (s : ℕ) :
    reindex Fin.revPerm (adjointScheme (eesCosine s)) =
      rankOnePerturb (eesCosine s) alternatingSign :=
  reindex_adjoint_alternatingTableau _ eesCosineD_rev

theorem isWilliamson2N_eesCosine (s : ℕ) : IsWilliamson2N (eesCosine s) := by
  apply isWilliamson2N_alternatingTableau
  intro j
  exact ne_of_gt (eesCosineD_pos (by have := j.isLt; omega) j)

/-- The two-stage member is Heun's explicit trapezoidal method. -/
theorem eesCosine_two_eq_heun : eesCosine 2 = heun ℝ := by
  have hd (j : Fin 2) : eesCosineD 2 j = 1 := by
    fin_cases j <;> norm_num [eesCosineD, eesCosineAngle,
      show 2 * (Real.pi / 2) = Real.pi by ring]
  apply ext
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [eesCosine, alternatingTableau, hd, heun, twoStageExplicit]
  · intro j
    fin_cases j <;> norm_num [eesCosine, alternatingTableau, hd, heun, twoStageExplicit]

theorem sum_cosine_differences (θ : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (Real.cos (j * θ) - Real.cos ((j + 1 : ℕ) * θ)) =
      1 - Real.cos (n * θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem cosine_difference_identity (a θ : ℝ) :
    (1 + Real.cos θ) * (Real.cos a - Real.cos (a + θ)) =
      Real.sin θ * (Real.sin a + Real.sin (a + θ)) := by
  rw [Real.cos_add, Real.sin_add]
  linear_combination -Real.cos a * Real.sin_sq_add_cos_sq θ

private theorem sum_signed_cosine_differences (θ : ℝ) (n : ℕ) :
    (1 + Real.cos θ) *
        (∑ j ∈ Finset.range n, (-1 : ℝ) ^ j *
          (Real.cos (j * θ) - Real.cos ((j + 1 : ℕ) * θ))) =
      -Real.sin θ * (-1) ^ n * Real.sin (n * θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, ← mul_assoc,
        mul_comm (1 + Real.cos θ) ((-1 : ℝ) ^ n), mul_assoc]
      have harg : ((n + 1 : ℕ) : ℝ) * θ = (n : ℝ) * θ + θ := by push_cast; ring
      rw [harg, mul_assoc ((-1 : ℝ) ^ n), cosine_difference_identity, pow_succ]
      ring

theorem sum_eesCosineD {s : ℕ} (hs : 0 < s) : ∑ j, eesCosineD s j = 2 := by
  simp only [eesCosineD]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    Real.cos (j * eesCosineAngle s) - Real.cos ((j + 1 : ℕ) * eesCosineAngle s))]
  rw [sum_cosine_differences, mul_eesCosineAngle hs, Real.cos_pi]
  norm_num

theorem sum_eesCosineD_alternatingSign {s : ℕ} (hs : 2 ≤ s) :
    ∑ j, eesCosineD s j * alternatingSign j = 0 := by
  have hs0 : 0 < s := by omega
  have hθ := eesCosineAngle_pos hs0
  have hθpi : eesCosineAngle s < Real.pi := by
    unfold eesCosineAngle
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hs0)).mpr
    nlinarith [show (2 : ℝ) ≤ s by exact_mod_cast hs, Real.pi_pos]
  have hC : 0 < 1 + Real.cos (eesCosineAngle s) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le le_rfl hθpi
    rw [Real.cos_pi] at h
    linarith
  have h := sum_signed_cosine_differences (eesCosineAngle s) s
  rw [mul_eesCosineAngle hs0, Real.sin_pi, mul_zero] at h
  have hz := (mul_eq_zero.mp h).resolve_left (ne_of_gt hC)
  simp only [eesCosineD, alternatingSign_eq_pow]
  simp_rw [mul_comm _ ((-1 : ℝ) ^ _)]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (-1 : ℝ) ^ j *
    (Real.cos (j * eesCosineAngle s) - Real.cos ((j + 1 : ℕ) * eesCosineAngle s)))]
  exact hz

theorem weightBullet_eesCosine {s : ℕ} (hs : 0 < s) :
    weightBullet (eesCosine s) = 1 := by
  change ∑ j, eesCosineD s j / 2 = 1
  rw [← Finset.sum_div, sum_eesCosineD hs]
  norm_num

theorem hasOrder_two_eesCosine {s : ℕ} (hs : 2 ≤ s) : HasOrder (eesCosine s) 2 :=
  hasOrder_two_alternatingTableau _ (sum_eesCosineD (by omega))
    (sum_eesCosineD_alternatingSign hs)

end

end BSeries.RungeKutta
