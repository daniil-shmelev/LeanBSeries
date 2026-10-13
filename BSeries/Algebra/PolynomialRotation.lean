import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.OrderOfElement

/-!
# Polynomial rotation and the primitive spectral root

The coefficient recurrence gives a rotation identity. Iterating it through a half turn and using coprimality determines the linear factors of the stability polynomial. Square-freeness then forces the full period.
-/

namespace Polynomial

open scoped BigOperators

noncomputable section
variable {R : Type*} [Field R]

theorem polynomial_rotation (p : R[X]) (q a : R)
    (hrec : ∀ k, p.coeff (k + 1) * (q ^ (k + 1) - 1) =
      a * p.coeff k * (q ^ k + 1)) :
    (1 - C a * X) * p.comp (C q * X) = (1 + C a * X) * p := by
  ext n
  cases n with
  | zero => simp
  | succ k =>
      simp only [sub_mul, add_mul, one_mul, coeff_sub, coeff_add, mul_assoc,
        coeff_C_mul, coeff_X_mul, comp_C_mul_X_coeff]
      linear_combination hrec k

theorem polynomial_rotation_iterate (p : R[X]) (q a : R)
    (hrot : (1 - C a * X) * p.comp (C q * X) = (1 + C a * X) * p) (k : ℕ) :
    p.comp (C (q ^ k) * X) * (∏ j ∈ Finset.range k, (1 - C (a * q ^ j) * X)) =
      p * (∏ j ∈ Finset.range k, (1 + C (a * q ^ j) * X)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := congrArg (fun f : R[X] => f.comp (C (q ^ k) * X)) hrot
      simp only [mul_comp, sub_comp, add_comp, one_comp, C_comp, X_comp,
        comp_assoc, ← C_mul, ← mul_assoc] at h
      rw [← pow_succ'] at h
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      calc
        _ = (∏ j ∈ Finset.range k, (1 - C (a * q ^ j) * X)) *
            ((1 - C (a * q ^ k) * X) * p.comp (C (q ^ (k + 1)) * X)) := by ring
        _ = _ := by rw [h]; linear_combination (1 + C (a * q ^ k) * X) * ih

theorem polynomial_factor_of_rotation (p : R[X]) (q a : R) {s : ℕ}
    (hp₀ : p.coeff 0 = 1) (hdeg : p.natDegree = s)
    (hsq : Squarefree (p * p.comp (-X))) (hqs : q ^ s = -1)
    (hrot : (1 - C a * X) * p.comp (C q * X) = (1 + C a * X) * p) :
    p = ∏ j ∈ Finset.range s, (1 - C (a * q ^ j) * X) := by
  let f : R[X] := ∏ j ∈ Finset.range s, (1 - C (a * q ^ j) * X)
  have hf₀ : f.coeff 0 = 1 := by simp [f, coeff_zero_prod]
  have hp : p ≠ 0 := by intro h; simp [h] at hp₀
  have hf : f ≠ 0 := by intro h; simp [h] at hf₀
  have hiter := polynomial_rotation_iterate p q a hrot s
  rw [hqs] at hiter
  simp only [map_neg, map_one, neg_one_mul] at hiter
  have hdvd : p ∣ f := (IsRelPrime.of_squarefree_mul hsq).dvd_of_dvd_mul_left
    (hiter ▸ dvd_mul_right p _)
  obtain ⟨g, hg⟩ := hdvd
  have hg₀ : g ≠ 0 := by intro h; simp [h] at hg; exact hf hg
  have hbound : f.natDegree ≤ s := by
    calc
      _ ≤ ∑ j ∈ Finset.range s, (1 - C (a * q ^ j) * X).natDegree := natDegree_prod_le (Finset.range s) (fun j => (1 - C (a * q ^ j) * X))
      _ ≤ ∑ _j ∈ Finset.range s, 1 := by
        apply Finset.sum_le_sum
        intro j _
        compute_degree!
      _ = s := by simp
  have hgd : g.natDegree = 0 := by rw [hg, natDegree_mul hp hg₀, hdeg] at hbound; omega
  have hconst := eq_C_of_natDegree_eq_zero hgd
  have hc : g.coeff 0 = 1 := by simpa [hg, coeff_mul, hp₀] using hf₀
  rw [hconst, hc, C_1, mul_one] at hg
  exact hg.symm

theorem squarefree_prod_inj {ι : Type*} [DecidableEq ι] (f : ι → R[X]) (t : Finset ι)
    (hsq : Squarefree (∏ i ∈ t, f i)) (hn : ∀ i ∈ t, ¬ IsUnit (f i))
    {i j : ι} (hi : i ∈ t) (hj : j ∈ t) (heq : f i = f j) : i = j := by
  by_contra hij
  have hj' : j ∈ t.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hprod : (∏ k ∈ t, f k) = f i * f i * ∏ k ∈ (t.erase i).erase j, f k := by
    rw [← Finset.mul_prod_erase t f hi, ← Finset.mul_prod_erase (t.erase i) f hj', ← heq]
    ring
  exact hn i hi (hsq (f i) (by rw [hprod]; exact dvd_mul_right ..))

theorem orderOf_eq_twice_of_rotation_factor (p : R[X]) (q a : R) {s : ℕ}
    (hs : 0 < s) (ha : a ≠ 0) (hq : q ≠ 0) (hqs : q ^ s = -1)
    (hsq : Squarefree (p * p.comp (-X)))
    (hf : p = ∏ j ∈ Finset.range s, (1 - C (a * q ^ j) * X)) :
    orderOf q = 2 * s := by
  let f : ℕ → R[X] := fun j => 1 - C (a * q ^ j) * X
  have hfull : (∏ j ∈ Finset.range (2 * s), f j) = p * p.comp (-X) := by
    rw [two_mul, Finset.prod_range_add, hf]
    simp only [prod_comp, sub_comp, one_comp, mul_comp, C_comp, X_comp, f,
      pow_add, hqs, mul_neg]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    ring_nf
    rw [map_neg]
    ring
  have hn (i : ℕ) (_hi : i ∈ Finset.range (2 * s)) : ¬ IsUnit (f i) := by
    intro h
    have hc := coeff_eq_zero_of_natDegree_lt (p := f i) (n := 1)
      (by rw [natDegree_eq_zero_of_isUnit h]; omega)
    simp only [f, coeff_sub, coeff_one, coeff_C_mul_X, ite_false, one_ne_zero, neg_eq_zero, zero_sub] at hc
    exact mul_ne_zero ha (pow_ne_zero i hq) hc
  have hpow : q ^ (2 * s) = 1 := by rw [mul_comm 2 s, pow_mul, hqs]; simp
  have hpos : 0 < orderOf q := (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * s, by omega, hpow⟩).orderOf_pos
  have hle := orderOf_le_of_pow_eq_one (by omega : 0 < 2 * s) hpow
  by_contra hne
  have h := squarefree_prod_inj f (Finset.range (2 * s)) (hfull ▸ hsq) hn
    (Finset.mem_range.mpr (show orderOf q < 2 * s by omega))
    (Finset.mem_range.mpr (show 0 < 2 * s by omega)) (by simp only [f, pow_orderOf_eq_one, pow_zero, mul_one])
  omega

end
end Polynomial
