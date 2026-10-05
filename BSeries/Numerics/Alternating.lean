/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Williamson
import BSeries.Numerics.RankOneOrder
import Mathlib.Algebra.BigOperators.Field

/-!
# Alternating Runge-Kutta tableaux

The tableau of the cosine EES family in Shmelev et al., Section
`A General Family of EES(2,m) Schemes`: `b_j = d_j / 2` and
`a_ij = d_j` for `j < i` of opposite parity, and zero otherwise.
-/

namespace BSeries.RungeKutta

universe v

variable {R : Type v} {s : ℕ}

/-- The alternating prefix sum in a row of the tableau. -/
def alternatingPrefix [AddCommMonoid R] (a : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, if n % 2 ≠ j % 2 then a j else 0

@[simp]
theorem alternatingPrefix_zero [AddCommMonoid R] (a : ℕ → R) :
    alternatingPrefix a 0 = 0 := by simp [alternatingPrefix]

@[simp]
theorem alternatingPrefix_one [AddCommMonoid R] (a : ℕ → R) :
    alternatingPrefix a 1 = a 0 := by simp [alternatingPrefix]

theorem alternatingPrefix_add_two [AddCommMonoid R] (a : ℕ → R) (n : ℕ) :
    alternatingPrefix a (n + 2) = alternatingPrefix a n + a (n + 1) := by
  have hp : (n + 2) % 2 = n % 2 := by omega
  have hn : n % 2 ≠ (n + 1) % 2 := by omega
  simp [alternatingPrefix, Finset.sum_range_succ, hp, hn]

/-- The alternating tableau, with zero-based stage indices. -/
def alternatingTableau [Field R] (d : Fin s → R) : RungeKutta (Fin s) R where
  A i j := if j < i ∧ i.val % 2 ≠ j.val % 2 then d j else 0
  b j := d j / 2

theorem alternatingTableau_apply [Field R] (d f : ℕ → R) (i : Fin s) :
    (∑ j, (alternatingTableau (fun j : Fin s => d j)).A i j * f j) =
      alternatingPrefix (fun j => d j * f j) i.val := by
  simp only [alternatingTableau, Fin.lt_def, ite_mul, zero_mul, ite_and]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    if j < i.val then (if i.val % 2 ≠ j % 2 then d j * f j else 0) else 0)]
  calc
    _ = ∑ j ∈ Finset.range i.val,
        if j < i.val then (if i.val % 2 ≠ j % 2 then d j * f j else 0) else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt i.isLt))
      intro j _ hj
      simp only [Finset.mem_range] at hj
      simp [hj]
    _ = alternatingPrefix (fun j => d j * f j) i.val := by
      unfold alternatingPrefix
      exact Finset.sum_congr rfl fun j hj => by simp [Finset.mem_range.mp hj]

theorem isExplicit_alternatingTableau [Field R] (d : Fin s → R) :
    IsExplicit (alternatingTableau d) := by
  intro i j hij
  exact ite_eq_right (by omega)

/-- Alternating tableaux satisfy Bazavov's compatibility condition. -/
theorem bazavovCondition_alternatingTableau [Field R] [CharZero R] (d : Fin s → R) :
    BazavovCondition (alternatingTableau d) := by
  intro i j k hk hki
  simp only [alternatingTableau, Fin.lt_def]
  split_ifs <;> first | omega | ring

/-- Every alternating tableau with nonzero weights is Williamson 2N. -/
theorem isWilliamson2N_alternatingTableau [Field R] [CharZero R]
    (d : Fin s → R) (hd : ∀ j, d j ≠ 0) :
    IsWilliamson2N (alternatingTableau d) := by
  cases s with
  | zero =>
      refine ⟨⟨Fin.elim0, Fin.elim0⟩, ext ?_ ?_⟩ <;> intro i <;> exact Fin.elim0 i
  | succ n =>
      apply isWilliamson2N_of_bazavovCondition (isExplicit_alternatingTableau d)
      · intro j
        exact div_ne_zero (hd j) (by norm_num)
      · exact bazavovCondition_alternatingTableau d

/-- The alternating signs in the rank-one defect. -/
def alternatingSign [One R] [Neg R] (i : Fin s) : R :=
  if i.val % 2 = 0 then 1 else -1

theorem alternatingSign_eq_pow [Ring R] (i : Fin s) :
    alternatingSign i = (-1 : R) ^ i.val := by
  simp [alternatingSign, neg_one_pow_eq_ite, Nat.even_iff]

/-- The entrywise rank-one defect of an alternating tableau. -/
theorem alternatingTableau_rank_one [Field R] [CharZero R]
    (d : Fin s → R) (i j : Fin s) :
    (alternatingTableau d).b i * (alternatingTableau d).A i j +
        (alternatingTableau d).b j * (alternatingTableau d).A j i =
      (alternatingTableau d).b i * (alternatingTableau d).b j -
        ((alternatingTableau d).b i * alternatingSign i) *
          ((alternatingTableau d).b j * alternatingSign j) := by
  simp only [alternatingTableau, alternatingSign, Fin.lt_def]
  split_ifs <;> first | omega | ring

/-- Reversal expresses the adjoint of a symmetric alternating tableau as a rank-one perturbation. -/
theorem reindex_adjoint_alternatingTableau [Field R] [CharZero R]
    (d : Fin s → R) (hd : ∀ j, d j.rev = d j) :
    reindex Fin.revPerm (adjointScheme (alternatingTableau d)) =
      rankOnePerturb (alternatingTableau d) alternatingSign := by
  apply ext
  · intro i j
    simp only [reindex, adjointScheme, rankOnePerturb, alternatingTableau,
      Fin.revPerm_apply, hd, alternatingSign, Fin.lt_def, Fin.val_rev]
    split_ifs <;> first | omega | ring
  · intro j
    simp [reindex, adjointScheme, rankOnePerturb, alternatingTableau, hd]

/-- The rank-one identity reduces the second-order condition to two sums. -/
theorem hasOrder_two_alternatingTableau [Field R] [CharZero R]
    (d : Fin s → R) (hd : ∑ j, d j = 2)
    (hq : ∑ j, d j * alternatingSign j = 0) :
    HasOrder (alternatingTableau d) 2 := by
  let rk := alternatingTableau d
  have hb : ∑ j, rk.b j = 1 := by
    change ∑ j, d j / 2 = 1
    rw [← Finset.sum_div, hd]
    norm_num
  have hv : ∑ j, rk.b j * alternatingSign j = 0 := by
    change ∑ j, d j / 2 * alternatingSign j = 0
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hq, zero_div]
  have h := congrArg (fun f : Fin s → Fin s → R => ∑ i, ∑ j, f i j)
    (funext fun i => funext fun j => alternatingTableau_rank_one d i j)
  have hswap : (∑ i, ∑ j, rk.b j * rk.A j i) = ∑ i, ∑ j, rk.b i * rk.A i j :=
    Finset.sum_comm
  change (∑ i, ∑ j, (rk.b i * rk.A i j + rk.b j * rk.A j i)) =
    ∑ i, ∑ j, (rk.b i * rk.b j -
      (rk.b i * alternatingSign i) * (rk.b j * alternatingSign j)) at h
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [hswap, hb, hv] at h
  simp only [mul_one, mul_zero, Finset.sum_const_zero, sub_zero, hb] at h
  rw [hasOrder_two_iff_hasOrderOne_and_weight_chain2]
  refine ⟨hb, ?_⟩
  simp only [weight, stageWeight_chain2, abscissa]
  change (∑ i, rk.b i * ∑ j, rk.A i j) = (2 : R)⁻¹
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum] at h
  linear_combination h / 2

end BSeries.RungeKutta
