/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESCosinePolynomial
import BSeries.Numerics.AntisymStageBound

/-!
# Exact orders of the cosine EES methods

The quadratic moment and order-three defect in Proposition `EES_2_m`
of Shmelev et al., `main_sn_2.tex`.
-/

namespace BSeries.RungeKutta

noncomputable section

open HopfAlgebras Polynomial.Chebyshev

private theorem eesCosineAngle_le_pi_div_two {s : ℕ} (hs : 2 ≤ s) :
    eesCosineAngle s ≤ Real.pi / 2 := by
  unfold eesCosineAngle
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.mpr (by omega)
  apply (div_le_iff₀ hs0).mpr
  nlinarith [show (2 : ℝ) ≤ s by exact_mod_cast hs, Real.pi_pos]

private theorem eesCosine_half_cos_pos {s : ℕ} (hs : 2 ≤ s) :
    0 < Real.cos (eesCosineAngle s / 2) := by
  have hθ := eesCosineAngle_pos (by omega : 0 < s)
  have hθpi := eesCosineAngle_le_pi_div_two hs
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

private theorem eesCosine_half_sin_pos {s : ℕ} (hs : 2 ≤ s) :
    0 < Real.sin (eesCosineAngle s / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (eesCosineAngle_pos (by omega)) (by norm_num)
  · linarith [eesCosineAngle_le_pi_div_two hs, Real.pi_pos]

theorem abscissa_eesCosine {s : ℕ} (hs : 2 ≤ s) (i : Fin s) :
    abscissa (eesCosine s) i = 1 / 2 -
      eesCosineNode s i / (2 * Real.cos (eesCosineAngle s / 2)) := by
  have h := eesCosine_chebyshev_primitive (s := s) (k := 1) (by omega) (by omega) i
  simp only [Nat.cast_one, sub_self, U_zero, T_one,
    Polynomial.eval_one, Polynomial.eval_X, mul_one, one_mul] at h
  change abscissa (eesCosine s) i = _ at h
  have hsin : Real.sin (eesCosineAngle s) =
      2 * Real.sin (eesCosineAngle s / 2) * Real.cos (eesCosineAngle s / 2) := by
    nth_rw 1 [show eesCosineAngle s = 2 * (eesCosineAngle s / 2) from by ring]
    rw [Real.sin_two_mul]
  rw [h, hsin]
  field_simp [ne_of_gt (eesCosine_half_sin_pos hs), ne_of_gt (eesCosine_half_cos_pos hs)]

theorem eesCosineNode_rev {s : ℕ} (i : Fin s) :
    eesCosineNode s i.rev = -eesCosineNode s i := by
  have hs : 0 < s := by have := i.isLt; omega
  have hi : i.rev.val + i.val + 1 = s := by simp only [Fin.val_rev]; omega
  have hi' : (i.rev.val : ℝ) + i.val + 1 = s := by exact_mod_cast hi
  have hphase : eesCosinePhase s i.rev.val + eesCosinePhase s i.val = Real.pi := by
    unfold eesCosinePhase
    calc
      _ = ((i.rev.val : ℝ) + i.val + 1) * eesCosineAngle s := by ring
      _ = Real.pi := by rw [hi', mul_eesCosineAngle hs]
  unfold eesCosineNode
  rw [show eesCosinePhase s i.rev.val = Real.pi - eesCosinePhase s i.val by linarith,
    Real.cos_pi_sub]

theorem sum_eesCosine_b_mul_node (s : ℕ) :
    ∑ i, (eesCosine s).b i * eesCosineNode s i = 0 := by
  have hb (i : Fin s) : (eesCosine s).b i.rev = (eesCosine s).b i := by
    simp only [eesCosine, alternatingTableau, eesCosineD_rev]
  have h := Equiv.sum_comp Fin.revPerm (fun i : Fin s => (eesCosine s).b i * eesCosineNode s i)
  simp only [Fin.revPerm_apply, hb, eesCosineNode_rev, mul_neg, Finset.sum_neg_distrib] at h
  linarith

private theorem sum_sine_midpoints (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * (∑ j ∈ Finset.range n, Real.sin (((j : ℝ) + 1 / 2) * θ)) =
      1 - Real.cos ((n : ℝ) * θ) := by
  rw [Finset.mul_sum]
  simp_rw [← cosine_difference_sin]
  exact sum_cosine_differences θ n

theorem sum_eesCosine_b_mul_node_sq {s : ℕ} (hs : 2 ≤ s) :
    ∑ i, (eesCosine s).b i * eesCosineNode s i ^ 2 =
      (1 + Real.cos (eesCosineAngle s)) / (2 * (1 + 2 * Real.cos (eesCosineAngle s))) := by
  let θ := eesCosineAngle s
  let η := θ / 2
  let C := Real.cos θ
  let M := ∑ i, (eesCosine s).b i * eesCosineNode s i ^ 2
  let S1 := ∑ i : Fin s, Real.sin (eesCosinePhase s i.val)
  let S3 := ∑ i : Fin s, Real.sin (3 * eesCosinePhase s i.val)
  have hC : 0 ≤ C := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by have := eesCosineAngle_pos (by omega : 0 < s); dsimp [C, θ]; linarith [Real.pi_pos])
    (eesCosineAngle_le_pi_div_two hs)
  have htriple : Real.sin (3 * η) = Real.sin η * (1 + 2 * C) := by
    have hc : C = 1 - 2 * Real.sin η ^ 2 := by
      dsimp only [C]
      rw [show θ = 2 * η from by dsimp [η]; ring, Real.cos_two_mul_eq_one_sub]
    rw [hc, Real.sin_three_mul]
    ring
  have hrange1 : S1 = ∑ j ∈ Finset.range s, Real.sin (((j : ℝ) + 1 / 2) * θ) :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => Real.sin (((j : ℝ) + 1 / 2) * θ)) s
  have hrange3 : S3 = ∑ j ∈ Finset.range s, Real.sin (((j : ℝ) + 1 / 2) * (3 * θ)) := by
    unfold S3 eesCosinePhase
    simp_rw [show ∀ j : ℕ, 3 * (((j : ℝ) + 1 / 2) * eesCosineAngle s) =
      ((j : ℝ) + 1 / 2) * (3 * θ) from fun _ => by dsimp [θ]; ring]
    exact Fin.sum_univ_eq_sum_range (fun j : ℕ => Real.sin (((j : ℝ) + 1 / 2) * (3 * θ))) s
  have hsum1 : 2 * Real.sin η * S1 = 2 := by
    rw [hrange1]
    have h := sum_sine_midpoints θ s
    rw [mul_eesCosineAngle (by omega : 0 < s), Real.cos_pi] at h
    norm_num at h
    exact h
  have hsum3 : 2 * Real.sin η * (1 + 2 * C) * S3 = 2 := by
    rw [mul_assoc 2, ← htriple, hrange3]
    have h := sum_sine_midpoints (3 * θ) s
    have hangle : (s : ℝ) * (3 * θ) = 3 * Real.pi := by
      calc
        _ = 3 * ((s : ℝ) * θ) := by ring
        _ = _ := by rw [mul_eesCosineAngle (by omega : 0 < s)]
    rw [show (3 * θ) / 2 = 3 * η from by dsimp [η]; ring, hangle] at h
    rw [show 3 * Real.pi = Real.pi + 2 * Real.pi by ring, Real.cos_add_two_pi,
      Real.cos_pi] at h
    norm_num at h
    exact h
  have hpoint (i : Fin s) : 4 * ((eesCosine s).b i * eesCosineNode s i ^ 2) =
      Real.sin η * (Real.sin (eesCosinePhase s i.val) + Real.sin (3 * eesCosinePhase s i.val)) := by
    change 4 * (eesCosineD s i / 2 * Real.cos (eesCosinePhase s i.val) ^ 2) = _
    rw [eesCosineD_sin, Real.sin_three_mul]
    dsimp only [η, θ]
    linear_combination 4 * Real.sin (eesCosineAngle s / 2) *
      Real.sin (eesCosinePhase s i.val) * Real.sin_sq_add_cos_sq (eesCosinePhase s i.val)
  have hmoment := congrArg (fun f : Fin s → ℝ => ∑ i, f i) (funext hpoint)
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hmoment
  change 4 * M = Real.sin η * S1 + Real.sin η * S3 at hmoment
  change M = (1 + C) / (2 * (1 + 2 * C))
  apply (eq_div_iff (by positivity : 2 * (1 + 2 * C) ≠ 0)).mpr
  linear_combination (1 + 2 * C) * hmoment / 2 + (1 + 2 * C) * hsum1 / 4 + hsum3 / 4

/-- The order-three cherry condition has a positive defect for every stage count. -/
theorem weight_cherry_eesCosine_sub_third {s : ℕ} (hs : 2 ≤ s) :
    weight (eesCosine s) PTree.cherry - 1 / 3 =
      (1 - Real.cos (eesCosineAngle s)) / (6 * (1 + 2 * Real.cos (eesCosineAngle s))) := by
  let θ := eesCosineAngle s
  let η := θ / 2
  let C := Real.cos θ
  let M := ∑ i, (eesCosine s).b i * eesCosineNode s i ^ 2
  let W := ∑ i, (eesCosine s).b i * abscissa (eesCosine s) i ^ 2
  have hC : 0 ≤ C := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by have := eesCosineAngle_pos (by omega : 0 < s); dsimp [C, θ]; linarith [Real.pi_pos])
    (eesCosineAngle_le_pi_div_two hs)
  have hc : 0 < Real.cos η := eesCosine_half_cos_pos hs
  have hb : ∑ i, (eesCosine s).b i = 1 := weightBullet_eesCosine (by omega : 0 < s)
  have hx := sum_eesCosine_b_mul_node s
  have hM : M = (1 + C) / (2 * (1 + 2 * C)) := sum_eesCosine_b_mul_node_sq hs
  have hcos : Real.cos η ^ 2 = (1 + C) / 2 := by
    have h := Real.cos_two_mul η
    rw [show 2 * η = θ from by dsimp [η]; ring] at h
    dsimp only [C]
    linarith
  have hpoint (i : Fin s) : 4 * Real.cos η ^ 2 *
      ((eesCosine s).b i * abscissa (eesCosine s) i ^ 2) =
      Real.cos η ^ 2 * (eesCosine s).b i -
        2 * Real.cos η * ((eesCosine s).b i * eesCosineNode s i) +
          (eesCosine s).b i * eesCosineNode s i ^ 2 := by
    rw [abscissa_eesCosine hs]
    change 4 * Real.cos η ^ 2 * ((eesCosine s).b i *
      (1 / 2 - eesCosineNode s i / (2 * Real.cos η)) ^ 2) = _
    field_simp [ne_of_gt hc]
    ring
  have hquadratic := congrArg (fun f : Fin s → ℝ => ∑ i, f i) (funext hpoint)
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hquadratic
  rw [hb, hx, mul_one, mul_zero, sub_zero] at hquadratic
  change 4 * Real.cos η ^ 2 * W = Real.cos η ^ 2 + M at hquadratic
  have hscalar : 4 * Real.cos η ^ 2 * M = Real.cos η ^ 2 + M := by
    rw [hcos, hM]
    field_simp [(by positivity : (1 + 2 * C) ≠ 0)]
    ring
  have hW : W = M := mul_left_cancel₀ (by positivity : 4 * Real.cos η ^ 2 ≠ 0)
    (hquadratic.trans hscalar.symm)
  rw [weight_cherry]
  simp only [← sq]
  change W - 1 / 3 = (1 - C) / (6 * (1 + 2 * C))
  rw [hW, hM]
  field_simp [(by positivity : (1 + 2 * C) ≠ 0)]
  ring

theorem not_hasOrder_three_eesCosine {s : ℕ} (hs : 2 ≤ s) : ¬ HasOrder (eesCosine s) 3 := by
  intro h
  have hweight := h.weight (t := PTree.cherry) (by decide)
  norm_num [PTree.cherry, PTree.treeFactorial, PTree.treeFactorialList] at hweight
  change weight (eesCosine s) PTree.cherry = 1 / 3 at hweight
  have hdefect := weight_cherry_eesCosine_sub_third hs
  rw [hweight, sub_self] at hdefect
  have hC : 0 ≤ Real.cos (eesCosineAngle s) := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [eesCosineAngle_pos (by omega : 0 < s), Real.pi_pos])
    (eesCosineAngle_le_pi_div_two hs)
  have hClt : Real.cos (eesCosineAngle s) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
      (by linarith [eesCosineAngle_le_pi_div_two hs, Real.pi_pos])
      (eesCosineAngle_pos (by omega : 0 < s))
    simpa using h
  have hpos : 0 < (1 - Real.cos (eesCosineAngle s)) /
      (6 * (1 + 2 * Real.cos (eesCosineAngle s))) := div_pos (by linarith) (by positivity)
  linarith

theorem isEES_eesCosine {s : ℕ} (hs : 2 ≤ s) : IsEES (eesCosine s) 2 (2 * s - 1) := by
  refine ⟨isExplicit_eesCosine s, ⟨hasOrder_two_eesCosine hs, not_hasOrder_three_eesCosine hs⟩,
    hasAntisymOrder_eesCosine hs, ?_⟩
  rw [show 2 * s - 1 + 1 = 2 * s by omega]
  exact not_hasAntisymOrder_twice_stages (isExplicit_eesCosine s)
    (weightBullet_eesCosine (by omega))

/-- The cosine EES method indexed by its prescribed antisymmetric order. -/
def eesCosineForOrder (m : ℕ) : RungeKutta (Fin ((m + 1) / 2)) ℝ :=
  eesCosine ((m + 1) / 2)

theorem isEES_eesCosineForOrder {m : ℕ} (hm : 3 ≤ m) (hodd : Odd m) :
    IsEES (eesCosineForOrder m) 2 m := by
  obtain ⟨k, hk⟩ := hodd
  have hs : 2 ≤ (m + 1) / 2 := by omega
  have heq : 2 * ((m + 1) / 2) - 1 = m := by omega
  simpa only [eesCosineForOrder, heq] using isEES_eesCosine hs

theorem isWilliamson2N_eesCosineForOrder (m : ℕ) : IsWilliamson2N (eesCosineForOrder m) :=
  isWilliamson2N_eesCosine _

/-- No consistent explicit tableau with fewer stages attains this antisymmetric order. -/
theorem eesCosine_minimal_stages {s k : ℕ} (hs : 2 ≤ s) {rk : RungeKutta (Fin k) ℝ}
    (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder (Series.toCharacter (series rk)) (2 * s - 1)) :
    s ≤ k := by
  have := antisymOrder_lt_twice_stages hexp hcons hanti
  omega

end

end BSeries.RungeKutta
