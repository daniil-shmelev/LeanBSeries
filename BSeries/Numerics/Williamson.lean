/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.EES
import BSeries.Numerics.CommutatorFree
import Mathlib.Data.List.GetD

/-!
# Williamson 2N-storage Runge–Kutta schemes

A Williamson low-storage scheme advances an `s`-stage Runge–Kutta step
using only two registers via the recurrence

  `δ_l = A_l δ_{l-1} + h K_l`,  `Y_l = Y_{l-1} + B_l δ_l`.

Unrolling the recurrence expresses each register update as a linear
combination of the stage slopes with weights
`β_{l,j} = B_l A_l A_{l-1} ⋯ A_{j+1}`, which induces a Butcher tableau.
Bazavov's criterion (arXiv:2509.20599, Theorem 3.1) characterises the
explicit tableaux arising this way:

  `a_{ik} (b_j - a_{kj}) = (a_{ij} - a_{kj}) b_k`  whenever `k = j + 1 ≤ i`.

We prove both directions, formalise Bazavov's commutator-free lift of a
low-storage scheme (arXiv:2509.20599, equation (4)) together with its
collapse to the classical Runge–Kutta step under a flat (translation)
exponential action — the structural input for the CF-EES lifts of the
`EES(2,5;x)` and `EES(2,7;x)` families (arXiv:2509.20599,
Proposition 3.1).

## References

* Williamson, *Low-storage Runge-Kutta schemes*
* Bazavov, *Low-storage Runge-Kutta schemes and commutator-free Lie group
  methods*
* Shmelev, Thompson, Salvi, arXiv:2509.20599, Section 3 and Appendix D
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe v w

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
  rw [prodA, Finset.prod_eq_prod_Ico_succ_bot (by omega), dif_pos hs]
  rfl

/-- The unrolled slope weights: `β_{l,j} = B_l A_l ⋯ A_{j+1}` for `j ≤ l`,
and `0` otherwise. -/
def beta (ls : LowStorage s R) (l j : Fin s) : R :=
  if j ≤ l then ls.B l * ls.prodA (j : ℕ) (l : ℕ) else 0

@[simp]
theorem beta_self (ls : LowStorage s R) (j : Fin s) : ls.beta j j = ls.B j := by
  rw [beta, if_pos le_rfl, prodA_self, mul_one]

theorem beta_eq_zero_of_lt (ls : LowStorage s R) {l j : Fin s} (h : l < j) :
    ls.beta l j = 0 :=
  if_neg (not_le.mpr h)

/-- The one-step recurrence of the slope weights in the second index:
`β_{m,j} = A_{j+1} β_{m,j+1}` off the diagonal. -/
theorem beta_eq (ls : LowStorage s R) {j k : Fin s}
    (hk : (j : ℕ) + 1 = (k : ℕ)) (m : Fin s) :
    ls.beta m j = if m = j then ls.B j else ls.A k * ls.beta m k := by
  by_cases hm : m = j
  · subst hm
    rw [if_pos rfl, beta_self]
  · rw [if_neg hm]
    rcases lt_or_gt_of_ne hm with hlt | hgt
    · have hmk : m < k := by rw [Fin.lt_def] at hlt ⊢; omega
      rw [ls.beta_eq_zero_of_lt hlt, ls.beta_eq_zero_of_lt hmk, mul_zero]
    · have hkm : k ≤ m := by
        rw [Fin.lt_def] at hgt
        rw [Fin.le_def]
        omega
      have hs : (j : ℕ) + 1 < s := hk ▸ k.isLt
      rw [beta, beta, if_pos hgt.le, if_pos hkm,
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
      rw [if_pos rfl, if_pos rfl, ls.beta_eq_zero_of_lt hjk, mul_zero,
        zero_add]
    · rw [if_neg hm, if_neg hm, add_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib,
    Finset.sum_ite_eq' t j fun _ => ls.B j, if_pos hj, Finset.mul_sum,
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
    rw [getD_map_range' _ i.isLt, dif_pos i.isLt]
  · show (((List.range s).map fun i' =>
      if h : i' < s then B ⟨i', h⟩ else 0).getD (i : ℕ) 0) = B i
    rw [getD_map_range' _ i.isLt, dif_pos i.isLt]

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

/-- **Bazavov's compatibility condition** (arXiv:2509.20599, Theorem 3.1):
`a_{ik} (b_j - a_{kj}) = (a_{ij} - a_{kj}) b_k` whenever `k = j + 1 ≤ i`. -/
def BazavovCondition [CommRing R] {s : ℕ} (rk : RungeKutta (Fin s) R) : Prop :=
  ∀ i j k : Fin s, (j : ℕ) + 1 = (k : ℕ) → k ≤ i →
    rk.A i k * (rk.b j - rk.A k j) = (rk.A i j - rk.A k j) * rk.b k

/-- Williamson 2N tableaux satisfy Bazavov's condition (the forward
direction of arXiv:2509.20599, Theorem 3.1). -/
theorem IsWilliamson2N.bazavovCondition [CommRing R] {s : ℕ}
    {rk : RungeKutta (Fin s) R} (h : IsWilliamson2N rk) :
    BazavovCondition rk := by
  obtain ⟨ls, rfl⟩ := h
  intro i j k hk hki
  have hjk : j < k := by rw [Fin.lt_def]; omega
  have hji : j < i := lt_of_lt_of_le hjk hki
  rw [ls.toRK_A_succ_self hk, ls.toRK_b_succ hk, ls.toRK_A_of_lt hk hji]
  ring

namespace LowStorage

variable {n : ℕ}

/-- Reconstruct low-storage data from an explicit tableau:
`B_j = a_{j+1,j}` (with `B_{s-1} = b_{s-1}`) and
`A_{j+1} = (b_j - a_{j+1,j}) / b_{j+1}`. -/
def ofTableau [Field R] (rk : RungeKutta (Fin (n + 1)) R) :
    LowStorage (n + 1) R where
  B j := if h : (j : ℕ) + 1 < n + 1 then rk.A ⟨(j : ℕ) + 1, h⟩ j else rk.b j
  A k :=
    if h : 0 < (k : ℕ) then
      (rk.b ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ -
          rk.A k ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩) / rk.b k
    else 0

theorem ofTableau_B [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    (j : Fin (n + 1)) :
    (ofTableau rk).B j =
      if h : (j : ℕ) + 1 < n + 1 then rk.A ⟨(j : ℕ) + 1, h⟩ j
      else rk.b j :=
  rfl

theorem ofTableau_A [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    (k : Fin (n + 1)) :
    (ofTableau rk).A k =
      if h : 0 < (k : ℕ) then
        (rk.b ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ -
            rk.A k ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩) / rk.b k
      else 0 :=
  rfl

theorem ofTableau_B_of_succ [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    {j k : Fin (n + 1)} (hk : (j : ℕ) + 1 = (k : ℕ)) :
    (ofTableau rk).B j = rk.A k j := by
  have h : (j : ℕ) + 1 < n + 1 := hk ▸ k.isLt
  rw [ofTableau_B, dif_pos h,
    show (⟨(j : ℕ) + 1, h⟩ : Fin (n + 1)) = k from Fin.ext hk]

theorem ofTableau_B_last [Field R] (rk : RungeKutta (Fin (n + 1)) R) :
    (ofTableau rk).B (Fin.last n) = rk.b (Fin.last n) := by
  rw [ofTableau_B, dif_neg (by simp)]

theorem ofTableau_A_of_succ [Field R] (rk : RungeKutta (Fin (n + 1)) R)
    {j k : Fin (n + 1)} (hk : (j : ℕ) + 1 = (k : ℕ)) :
    (ofTableau rk).A k = (rk.b j - rk.A k j) / rk.b k := by
  have h : 0 < (k : ℕ) := by omega
  rw [ofTableau_A, dif_pos h,
    show (⟨(k : ℕ) - 1, by have := k.isLt; omega⟩ : Fin (n + 1)) = j from
      Fin.ext (show (k : ℕ) - 1 = (j : ℕ) by omega)]

end LowStorage

/-- **Bazavov's theorem, converse direction** (arXiv:2509.20599,
Theorem 3.1): an explicit tableau with nonvanishing weights satisfying the
compatibility condition is Williamson 2N. -/
theorem isWilliamson2N_of_bazavovCondition [Field R] {n : ℕ}
    {rk : RungeKutta (Fin (n + 1)) R} (hexp : IsExplicit rk)
    (hb : ∀ j, rk.b j ≠ 0) (hbaz : BazavovCondition rk) :
    IsWilliamson2N rk := by
  refine ⟨LowStorage.ofTableau rk, ?_⟩
  have hrecb : ∀ j k : Fin (n + 1), (j : ℕ) + 1 = (k : ℕ) →
      rk.b j = (LowStorage.ofTableau rk).B j +
        (LowStorage.ofTableau rk).A k * rk.b k := by
    intro j k hk
    rw [LowStorage.ofTableau_B_of_succ rk hk,
      LowStorage.ofTableau_A_of_succ rk hk, div_mul_cancel₀ _ (hb k)]
    ring
  have hrecA : ∀ i j k : Fin (n + 1), (j : ℕ) + 1 = (k : ℕ) → j < i →
      rk.A i j = (LowStorage.ofTableau rk).B j +
        (LowStorage.ofTableau rk).A k * rk.A i k := by
    intro i j k hk hji
    have hki : k ≤ i := by
      rw [Fin.lt_def] at hji
      rw [Fin.le_def]
      omega
    have h := hbaz i j k hk hki
    have h2 : (rk.b j - rk.A k j) / rk.b k * rk.A i k =
        rk.A i j - rk.A k j := by
      rw [div_mul_eq_mul_div, mul_comm (rk.b j - rk.A k j) (rk.A i k), h,
        mul_div_cancel_right₀ _ (hb k)]
    rw [LowStorage.ofTableau_B_of_succ rk hk,
      LowStorage.ofTableau_A_of_succ rk hk, h2]
    ring
  have hbagree : ∀ j, (LowStorage.ofTableau rk).toRK.b j = rk.b j := by
    intro j
    induction j using Fin.reverseInduction with
    | last => rw [LowStorage.toRK_b_last, LowStorage.ofTableau_B_last]
    | cast p ih =>
        have hk : ((p.castSucc : Fin (n + 1)) : ℕ) + 1 =
            ((p.succ : Fin (n + 1)) : ℕ) := by simp
        rw [LowStorage.toRK_b_succ _ hk, ih]
        exact (hrecb p.castSucc p.succ hk).symm
  have hAagree : ∀ i j, (LowStorage.ofTableau rk).toRK.A i j = rk.A i j := by
    intro i j
    induction j using Fin.reverseInduction with
    | last =>
        rw [LowStorage.toRK_A_of_le _ (Fin.le_last i),
          hexp i (Fin.last n) (Fin.le_last i)]
    | cast p ih =>
        by_cases hji : p.castSucc < i
        · have hk : ((p.castSucc : Fin (n + 1)) : ℕ) + 1 =
              ((p.succ : Fin (n + 1)) : ℕ) := by simp
          rw [LowStorage.toRK_A_of_lt _ hk hji, ih]
          exact (hrecA i p.castSucc p.succ hk hji).symm
        · rw [not_lt] at hji
          rw [LowStorage.toRK_A_of_le _ hji, hexp i p.castSucc hji]
  exact ext hAagree hbagree

/-- **Bazavov's characterisation of Williamson 2N schemes**
(arXiv:2509.20599, Theorem 3.1; Bazavov, Theorem 2): an explicit tableau
with nonvanishing weights is Williamson 2N if and only if it satisfies the
compatibility condition. -/
theorem isWilliamson2N_iff_bazavovCondition [Field R] {n : ℕ}
    {rk : RungeKutta (Fin (n + 1)) R} (hexp : IsExplicit rk)
    (hb : ∀ j, rk.b j ≠ 0) :
    IsWilliamson2N rk ↔ BazavovCondition rk :=
  ⟨IsWilliamson2N.bazavovCondition,
    isWilliamson2N_of_bazavovCondition hexp hb⟩

/-! ### Bazavov's commutator-free lift

A Williamson 2N scheme lifts to a commutator-free method by replacing the
register update `Y_l = Y_{l-1} + B_l δ_l` with the exponential action
`Y_l = Λ(exp(B_l δ_l), Y_{l-1})` (arXiv:2509.20599, equation (4)).
Unrolling the recurrence, the `l`-th exponential argument is
`V_l = Σ_j β_{l,j} K_j`. -/

namespace LowStorage

variable {s : ℕ} [CommRing R]

/-- Bazavov's commutator-free lift of a Williamson 2N scheme
(arXiv:2509.20599, equation (4)): stage `i` composes the exponentials
`exp(V_m)` for `m < i`, where `V_m = Σ_j β_{m,j} K_j`, and the step
composes all `s` of them. Each stage adds exactly one new exponential, so
the lift uses `s` exponentials per step in two registers. -/
noncomputable def toCommutatorFree (ls : LowStorage s R) :
    CommutatorFreeMethod (Fin s) R where
  stageExps i := ((List.finRange s).filter (fun m => m < i)).map
    fun m => ls.beta m
  stepExps := (List.finRange s).map fun m => ls.beta m

theorem toCommutatorFree_stageExps (ls : LowStorage s R) (i : Fin s) :
    ls.toCommutatorFree.stageExps i =
      ((List.finRange s).filter (fun m => m < i)).map fun m => ls.beta m :=
  rfl

theorem toCommutatorFree_stepExps (ls : LowStorage s R) :
    ls.toCommutatorFree.stepExps = (List.finRange s).map fun m => ls.beta m :=
  rfl

private theorem sum_map_filter_finRange {E : Type w} [AddCommMonoid E]
    (i : Fin s) (f : Fin s → E) :
    ((((List.finRange s).filter (fun m => m < i)).map f).sum) =
      ∑ m ∈ Finset.Iio i, f m := by
  have h1 : ∀ l : List (Fin s), (((l.filter (fun m => m < i)).map f).sum) =
      (l.map fun m => if m < i then f m else 0).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => by_cases h : a < i <;> simp [h, ih]
  rw [h1, ← Fin.sum_univ_def,
    show Finset.Iio i = Finset.univ.filter (fun m => m < i) from by
      ext m; simp,
    Finset.sum_filter]

end LowStorage

/-- The translation action of a module on itself: the "flat" exponential
map, under which commutator-free methods collapse to classical
Runge–Kutta schemes. -/
def _root_.BSeries.ExponentialAction.translation (E : Type w)
    [AddCommMonoid E] : ExponentialAction E E where
  act a y := y + a
  act_zero y := add_zero y

theorem _root_.BSeries.ExponentialAction.applyList_translation {E : Type w}
    [AddCommMonoid E] (as : List E) (y : E) :
    (ExponentialAction.translation E).applyList as y = y + as.sum := by
  induction as generalizing y with
  | nil => simp
  | cons a as ih =>
      rw [ExponentialAction.applyList_cons, ih, List.sum_cons, ← add_assoc]
      rfl

namespace LowStorage

variable {s : ℕ} [CommRing R] {E : Type w} [AddCommMonoid E] [Module R E]

/-- **On a flat space the Bazavov lift reproduces the Runge–Kutta stage
values**: composing the lift's stage exponentials under the translation
action yields the stage point of the induced Butcher tableau. -/
theorem toCommutatorFree_stagePoint_translation (ls : LowStorage s R)
    (K : Fin s → E) (i : Fin s) (y : E) :
    ls.toCommutatorFree.stagePoint (ExponentialAction.translation E) K i y =
      y + ∑ j, (toRK ls).A i j • K j := by
  rw [CommutatorFreeMethod.stagePoint,
    ExponentialAction.applyList_translation]
  congr 1
  rw [CommutatorFreeMethod.stageGenerators, toCommutatorFree_stageExps,
    List.map_map, sum_map_filter_finRange]
  simp only [Function.comp_apply, StageCombination.eval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toRK_A, Finset.sum_smul]

/-- **On a flat space the Bazavov lift collapses to the classical
Runge–Kutta step** (arXiv:2509.20599, Section 3): the commutator-free
step under the translation action is `y + Σ_j b_j K_j` for the induced
Butcher weights. -/
theorem toCommutatorFree_step_translation (ls : LowStorage s R)
    (K : Fin s → E) (y : E) :
    ls.toCommutatorFree.step (ExponentialAction.translation E) K y =
      y + ∑ j, (toRK ls).b j • K j := by
  rw [CommutatorFreeMethod.step, ExponentialAction.applyList_translation]
  congr 1
  rw [CommutatorFreeMethod.stepGenerators, toCommutatorFree_stepExps,
    List.map_map, ← Fin.sum_univ_def]
  simp only [Function.comp_apply, StageCombination.eval]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toRK_b, Finset.sum_smul]

end LowStorage

end RungeKutta

end BSeries
