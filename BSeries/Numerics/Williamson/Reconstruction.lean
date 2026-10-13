/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Williamson.Basic

/-!
# A common reconstruction criterion

Consecutive tableau rows describe consecutive stage inputs; the output weights form the row after the final stage. Their differences are exactly the increments in a Williamson recurrence. Matching these increments with `LowStorage.beta` recovers the entire tableau, without division or nonvanishing assumptions.
-/

namespace BSeries.RungeKutta

open scoped BigOperators

variable {R : Type*} {s : ℕ}

/-- The row following stage `i`, with output weights following the final stage. -/
def rowAfter (rk : RungeKutta (Fin s) R) (i j : Fin s) : R :=
  if hi : i.val + 1 < s then rk.A ⟨i.val + 1, hi⟩ j else rk.b j

theorem rowAfter_succ (rk : RungeKutta (Fin s) R) {i k : Fin s}
    (hk : i.val + 1 = k.val) (j : Fin s) : rk.rowAfter i j = rk.A k j := by
  have hi : i.val + 1 < s := hk ▸ k.isLt
  simp only [rowAfter, dite_eq_left hi]
  congr 1
  exact Fin.ext hk

@[simp] theorem rowAfter_last {n : ℕ} (rk : RungeKutta (Fin (n + 1)) R)
    (j : Fin (n + 1)) : rk.rowAfter (Fin.last n) j = rk.b j := by
  simp [rowAfter]

/-- Coefficients of the difference between consecutive stage inputs, including the final output. -/
def rowDifference [Sub R] (rk : RungeKutta (Fin s) R) (i j : Fin s) : R :=
  rk.rowAfter i j - rk.A i j

variable [CommRing R]

theorem rowDifference_self {rk : RungeKutta (Fin s) R} (hexp : IsExplicit rk)
    (i : Fin s) : rk.rowDifference i i = rk.rowAfter i i := by
  simp [rowDifference, hexp i i le_rfl]

theorem rowDifference_eq_zero_of_lt {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) {i j : Fin s} (hij : i < j) :
    rk.rowDifference i j = 0 := by
  have hi : i.val + 1 < s := by have := j.isLt; simp only [Fin.lt_def] at hij; omega
  simp only [rowDifference, rowAfter, dite_eq_left hi, hexp i j hij.le]
  rw [hexp _ j (by simp only [Fin.le_def, Fin.lt_def] at *; omega), sub_self]

namespace LowStorage

/-- Each increment of the unrolled tableau has coefficients `beta`. -/
theorem rowDifference_toRK (ls : LowStorage s R) (i j : Fin s) :
    ls.toRK.rowDifference i j = ls.beta i j := by
  classical
  unfold rowDifference rowAfter
  by_cases hi : i.val + 1 < s
  · rw [dite_eq_left hi, toRK_A, toRK_A]
    have hset : Finset.Iio (⟨i.val + 1, hi⟩ : Fin s) = insert i (Finset.Iio i) := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    ring
  · rw [dite_eq_right hi, toRK_b, toRK_A]
    have hset : (Finset.univ : Finset (Fin s)) = insert i (Finset.Iio i) := by
      ext k
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_Iio, Fin.lt_def,
        Fin.ext_iff, true_iff]
      have := k.isLt
      have := i.isLt
      omega
    rw [hset, Finset.sum_insert (by simp)]
    ring

/-- Matching the successive increments reconstructs all stages and the output. This criterion works over any commutative ring and permits zero register coefficients and output weights. -/
theorem toRK_eq_of_rowDifference (ls : LowStorage s R) {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hdiff : ∀ i j, rk.rowDifference i j = ls.beta i j) :
    ls.toRK = rk := by
  have hd (i j : Fin s) : ls.toRK.rowDifference i j = rk.rowDifference i j := by
    rw [ls.rowDifference_toRK, hdiff]
  cases s with
  | zero => exact ext (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | succ n =>
    have hA : ∀ i j, ls.toRK.A i j = rk.A i j := by
      intro i
      induction i using Fin.induction with
      | zero =>
        intro j
        rw [ls.toRK_A_of_le (Fin.zero_le j), hexp 0 j (Fin.zero_le j)]
      | succ i ih =>
        intro j
        have h := hd i.castSucc j
        have hi : i.castSucc.val + 1 < n + 1 := i.succ.isLt
        simp only [rowDifference, rowAfter, dite_eq_left hi] at h
        change ls.toRK.A i.succ j - ls.toRK.A i.castSucc j =
          rk.A i.succ j - rk.A i.castSucc j at h
        rw [ih j] at h
        exact sub_left_injective h
    apply ext hA
    intro j
    have h := hd (Fin.last n) j
    simp only [rowDifference, rowAfter_last] at h
    rw [hA] at h
    exact sub_left_injective h

end LowStorage

end BSeries.RungeKutta
