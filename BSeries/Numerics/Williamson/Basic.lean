/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.EES
import Mathlib.Data.List.GetD

/-!
# Williamson two-register coefficients

`LowStorage` records the coefficients of the two-register recurrence. `LowStorage.toRK` unrolls it into a Butcher tableau, and `IsWilliamson2N` states that a tableau is obtained this way. No nonvanishing assumptions are needed for these definitions or their coefficient identities.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe v

variable {ι : Type*} {R : Type v}

/-- Tableaux agreeing entrywise are equal. -/
theorem ext {rk₁ rk₂ : RungeKutta ι R}
    (hA : ∀ i j, rk₁.A i j = rk₂.A i j) (hb : ∀ j, rk₁.b j = rk₂.b j) :
    rk₁ = rk₂ := by
  cases rk₁
  cases rk₂
  simp only [mk.injEq]
  exact ⟨funext fun i => funext (hA i), funext hb⟩

/-- Low-storage (Williamson 2N) coefficient data for an `s`-stage scheme:
the two-register recurrence `δ_l = A_l δ_{l-1} + h K_l`,
`Y_l = Y_{l-1} + B_l δ_l`. The leading coefficient `A 0` is never used. -/
structure LowStorage (s : ℕ) (R : Type v) where
  A : Fin s → R
  B : Fin s → R

namespace LowStorage

variable {s n : ℕ} [CommRing R]

/-- The product `A_{j+1} A_{j+2} ⋯ A_l` of recurrence coefficients, over
natural indices (empty product when `l ≤ j`). -/
def prodA (ls : LowStorage s R) (j l : ℕ) : R :=
  ∏ k ∈ Finset.Ico (j + 1) (l + 1), if h : k < s then ls.A ⟨k, h⟩ else 1

@[simp]
theorem prodA_self (ls : LowStorage s R) (j : ℕ) : ls.prodA j j = 1 := by
  rw [prodA, Finset.Ico_self, Finset.prod_empty]

theorem prodA_succ_bot (ls : LowStorage s R) {j l : ℕ} (h : j < l)
    (hs : j + 1 < s) :
    ls.prodA j l = ls.A ⟨j + 1, hs⟩ * ls.prodA (j + 1) l := by
  rw [prodA, Finset.prod_eq_prod_Ico_succ_bot (by omega), dite_eq_left hs]
  rfl

/-- The unrolled slope weights: `β_{l,j} = B_l A_l ⋯ A_{j+1}` for `j ≤ l`,
and `0` otherwise. -/
def beta (ls : LowStorage s R) (l j : Fin s) : R :=
  if j ≤ l then ls.B l * ls.prodA (j : ℕ) (l : ℕ) else 0

@[simp]
theorem beta_self (ls : LowStorage s R) (j : Fin s) : ls.beta j j = ls.B j := by
  rw [beta, ite_eq_left le_rfl, prodA_self, mul_one]

theorem beta_eq_zero_of_lt (ls : LowStorage s R) {l j : Fin s} (h : l < j) :
    ls.beta l j = 0 :=
  ite_eq_right (not_le.mpr h)

/-- The one-step recurrence of the slope weights in the second index:
`β_{m,j} = A_{j+1} β_{m,j+1}` off the diagonal. -/
theorem beta_eq (ls : LowStorage s R) {j k : Fin s}
    (hk : (j : ℕ) + 1 = (k : ℕ)) (m : Fin s) :
    ls.beta m j = if m = j then ls.B j else ls.A k * ls.beta m k := by
  by_cases hm : m = j
  · subst hm
    rw [ite_eq_left rfl, beta_self]
  · rw [ite_eq_right hm]
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · have hmk : m < k := by rw [Fin.lt_def] at hlt ⊢; omega
      rw [ls.beta_eq_zero_of_lt hlt, ls.beta_eq_zero_of_lt hmk, mul_zero]
    · have hkm : k ≤ m := by
        rw [Fin.lt_def] at hgt
        rw [Fin.le_def]
        omega
      have hs : (j : ℕ) + 1 < s := hk ▸ k.isLt
      rw [beta, beta, ite_eq_left hgt.le, ite_eq_left hkm,
        ls.prodA_succ_bot (Fin.lt_def.mp hgt) hs,
        show (⟨(j : ℕ) + 1, hs⟩ : Fin s) = k from Fin.ext hk, hk]
      ring

/-- The Butcher tableau induced by unrolling the Williamson recurrence:
`a_{ij} = Σ_{m<i} β_{m,j}` and `b_j = Σ_m β_{m,j}`. -/
def toRK (ls : LowStorage s R) : RungeKutta (Fin s) R where
  A i j := ∑ m ∈ Finset.Iio i, ls.beta m j
  b j := ∑ m, ls.beta m j

theorem toRK_A (ls : LowStorage s R) (i j : Fin s) :
    (toRK ls).A i j = ∑ m ∈ Finset.Iio i, ls.beta m j :=
  rfl

theorem toRK_b (ls : LowStorage s R) (j : Fin s) :
    (toRK ls).b j = ∑ m, ls.beta m j :=
  rfl

/-- The induced tableau is strictly lower triangular. -/
theorem toRK_A_of_le (ls : LowStorage s R) {i j : Fin s} (hij : i ≤ j) :
    (toRK ls).A i j = 0 := by
  rw [toRK_A]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [Finset.mem_Iio] at hm
  exact ls.beta_eq_zero_of_lt (lt_of_lt_of_le hm hij)

/-- The induced tableau is explicit. -/
theorem isExplicit_toRK (ls : LowStorage s R) : IsExplicit (toRK ls) :=
  fun _ _ => ls.toRK_A_of_le

private theorem sum_beta_eq (ls : LowStorage s R) {j k : Fin s}
    (hk : (j : ℕ) + 1 = (k : ℕ)) {t : Finset (Fin s)} (hj : j ∈ t) :
    ∑ m ∈ t, ls.beta m j = ls.B j + ls.A k * ∑ m ∈ t, ls.beta m k := by
  have hjk : j < k := by rw [Fin.lt_def]; omega
  have h1 : ∀ m ∈ t, ls.beta m j =
      ls.A k * ls.beta m k + if m = j then ls.B j else 0 := by
    intro m _
    rw [ls.beta_eq hk m]
    by_cases hm : m = j
    · subst hm
      rw [ite_eq_left rfl, ite_eq_left rfl, ls.beta_eq_zero_of_lt hjk, mul_zero,
        zero_add]
    · rw [ite_eq_right hm, ite_eq_right hm, add_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
    Finset.sum_ite_eq' t j fun _ => ls.B j, ite_eq_left hj, Finset.mul_sum,
    add_comm]

/-- The recurrence of the induced weights: `b_j = B_j + A_{j+1} b_{j+1}`. -/
theorem toRK_b_succ (ls : LowStorage s R) {j k : Fin s}
    (hk : (j : ℕ) + 1 = (k : ℕ)) :
    (toRK ls).b j = ls.B j + ls.A k * (toRK ls).b k :=
  ls.sum_beta_eq hk (Finset.mem_univ j)

/-- The recurrence of the induced stage matrix:
`a_{ij} = B_j + A_{j+1} a_{i,j+1}` for `j < i`. -/
theorem toRK_A_of_lt (ls : LowStorage s R) {i j k : Fin s}
    (hk : (j : ℕ) + 1 = (k : ℕ)) (hji : j < i) :
    (toRK ls).A i j = ls.B j + ls.A k * (toRK ls).A i k :=
  ls.sum_beta_eq hk (Finset.mem_Iio.mpr hji)

/-- The subdiagonal of the induced tableau recovers the `B` coefficients:
`a_{j+1,j} = B_j`. -/
theorem toRK_A_succ_self (ls : LowStorage s R) {j k : Fin s}
    (hk : (j : ℕ) + 1 = (k : ℕ)) :
    (toRK ls).A k j = ls.B j := by
  have hjk : j < k := by rw [Fin.lt_def]; omega
  rw [ls.toRK_A_of_lt hk hjk, ls.toRK_A_of_le le_rfl, mul_zero, add_zero]

/-- Materialise low-storage data: coefficients are computed once and
stored as lists, so repeated access does not re-evaluate expensive
coefficient expressions. -/
def materialize (ls : LowStorage s R) : LowStorage s R :=
  let as := (List.range s).map fun i =>
    if h : i < s then ls.A ⟨i, h⟩ else 0
  let bs := (List.range s).map fun i =>
    if h : i < s then ls.B ⟨i, h⟩ else 0
  ⟨fun i => as.getD i 0, fun i => bs.getD i 0⟩

private theorem getD_map_range' {M : Type*} [Zero M] (g : ℕ → M)
    {m i : ℕ} (h : i < m) : ((List.range m).map g).getD i 0 = g i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem materialize_eq (ls : LowStorage s R) : ls.materialize = ls := by
  obtain ⟨A, B⟩ := ls
  refine congrArg₂ LowStorage.mk ?_ ?_ <;> funext i
  · show (((List.range s).map fun i' =>
      if h : i' < s then A ⟨i', h⟩ else 0).getD (i : ℕ) 0) = A i
    rw [getD_map_range' _ i.isLt, dite_eq_left i.isLt]
  · show (((List.range s).map fun i' =>
      if h : i' < s then B ⟨i', h⟩ else 0).getD (i : ℕ) 0) = B i
    rw [getD_map_range' _ i.isLt, dite_eq_left i.isLt]

/-- The last induced weight is `B_{s-1}`. -/
theorem toRK_b_last (ls : LowStorage (n + 1) R) :
    (toRK ls).b (Fin.last n) = ls.B (Fin.last n) := by
  rw [toRK_b, Finset.sum_eq_single (Fin.last n)]
  · exact ls.beta_self _
  · intro m _ hm
    exact ls.beta_eq_zero_of_lt (lt_of_le_of_ne (Fin.le_last m) hm)
  · exact fun h => absurd (Finset.mem_univ _) h

end LowStorage

/-- A tableau is **Williamson 2N** if it arises from a two-register
low-storage recurrence (arXiv:2509.20599, equation (2)). -/
def IsWilliamson2N [CommRing R] {s : ℕ} (rk : RungeKutta (Fin s) R) : Prop :=
  ∃ ls : LowStorage s R, ls.toRK = rk

end RungeKutta

end BSeries
