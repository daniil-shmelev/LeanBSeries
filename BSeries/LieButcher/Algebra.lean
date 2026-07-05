/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.LieButcher.PreLie
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Linearised Pre-Lie Grafting

This file linearly extends planar pre-Lie grafting to finitely supported formal
sums of planar rooted trees.
-/

namespace BSeries

open HopfAlgebras

universe u v w

noncomputable section

open Classical

/-- Coefficients of a formal sum of basis vectors count list occurrences. -/
theorem sum_single_apply_count {ι : Type u} {R : Type v} [DecidableEq ι] [Semiring R]
    (xs : List ι) (a : ι) :
    (((xs.map fun x => Finsupp.single x (1 : R)).sum) a) = (xs.count a : R) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      by_cases h : x = a
      · subst h
        simp [ih, add_comm]
      · simp [h, ih]

theorem sum_single_eq_of_perm {ι : Type u} {R : Type v} [DecidableEq ι] [Semiring R]
    {xs ys : List ι} (h : xs.Perm ys) :
    (xs.map fun x => Finsupp.single x (1 : R)).sum =
      (ys.map fun x => Finsupp.single x (1 : R)).sum := by
  ext a
  simp [sum_single_apply_count, h.count_eq a]

private theorem finsupp_mapDomain_sum_single {ι : Type u} {κ : Type v} {R : Type w}
    [Semiring R] (f : ι → κ) :
    ∀ xs : List ι,
      Finsupp.mapDomain f ((xs.map fun x => Finsupp.single x (1 : R)).sum) =
        (xs.map fun x => Finsupp.single (f x) (1 : R)).sum
  | [] => by
      simp
  | x :: xs => by
      simp [finsupp_mapDomain_sum_single f xs, Finsupp.mapDomain_add]

private theorem rank_eq_of_mem_support_add {ι : Type u} {R : Type v}
    [AddMonoid R] (rank : ι → Nat) {x y : Finsupp ι R} {n : Nat}
    (hx : ∀ u ∈ x.support, rank u = n) (hy : ∀ u ∈ y.support, rank u = n)
    {u : ι} (hu : u ∈ (x + y).support) : rank u = n := by
  by_cases hux : u ∈ x.support
  · exact hx u hux
  · by_cases huy : u ∈ y.support
    · exact hy u huy
    · have hx0 : x u = 0 := by
        by_contra hxne
        exact hux ((Finsupp.mem_support_iff).2 hxne)
      have hy0 : y u = 0 := by
        by_contra hyne
        exact huy ((Finsupp.mem_support_iff).2 hyne)
      have hxy0 : (x + y) u = 0 := by
        simp [hx0, hy0]
      exact False.elim ((Finsupp.mem_support_iff.mp hu) hxy0)

private theorem rank_le_of_mem_support_add {ι : Type u} {R : Type v}
    [AddMonoid R] (rank : ι → Nat) {x y : Finsupp ι R} {n : Nat}
    (hx : ∀ u ∈ x.support, rank u ≤ n) (hy : ∀ u ∈ y.support, rank u ≤ n)
    {u : ι} (hu : u ∈ (x + y).support) : rank u ≤ n := by
  by_cases hux : u ∈ x.support
  · exact hx u hux
  · by_cases huy : u ∈ y.support
    · exact hy u huy
    · have hx0 : x u = 0 := by
        by_contra hxne
        exact hux ((Finsupp.mem_support_iff).2 hxne)
      have hy0 : y u = 0 := by
        by_contra hyne
        exact huy ((Finsupp.mem_support_iff).2 hyne)
      have hxy0 : (x + y) u = 0 := by
        simp [hx0, hy0]
      exact False.elim ((Finsupp.mem_support_iff.mp hu) hxy0)

private theorem rank_eq_of_mem_support_smul {ι : Type u} {R : Type v} {S : Type w}
    [Zero R] [SMulZeroClass S R] (rank : ι → Nat) (c : S) {x : Finsupp ι R}
    {n : Nat} (hx : ∀ u ∈ x.support, rank u = n) {u : ι}
    (hu : u ∈ (c • x).support) : rank u = n := by
  by_cases hux : u ∈ x.support
  · exact hx u hux
  · have hx0 : x u = 0 := by
      by_contra hxne
      exact hux ((Finsupp.mem_support_iff).2 hxne)
    have hcx0 : (c • x) u = 0 := by
      simp [hx0]
    exact False.elim ((Finsupp.mem_support_iff.mp hu) hcx0)

private theorem rank_le_of_mem_support_smul {ι : Type u} {R : Type v} {S : Type w}
    [Zero R] [SMulZeroClass S R] (rank : ι → Nat) (c : S) {x : Finsupp ι R}
    {n : Nat} (hx : ∀ u ∈ x.support, rank u ≤ n) {u : ι}
    (hu : u ∈ (c • x).support) : rank u ≤ n := by
  by_cases hux : u ∈ x.support
  · exact hx u hux
  · have hx0 : x u = 0 := by
      by_contra hxne
      exact hux ((Finsupp.mem_support_iff).2 hxne)
    have hcx0 : (c • x) u = 0 := by
      simp [hx0]
    exact False.elim ((Finsupp.mem_support_iff.mp hu) hcx0)

namespace PTree

open HopfAlgebras.PTree

/-- Finitely supported formal sums of planar rooted trees. -/
abbrev FreeModule (R : Type u) [Zero R] : Type u :=
  Finsupp PTree R

/-- A formal tree sum supported only on trees of order `n`. -/
def HomogeneousOfOrder {R : Type u} [Zero R] (x : FreeModule R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u = n

/-- A formal tree sum supported only on trees of order at most `n`. -/
def SupportedUpToOrder {R : Type u} [Zero R] (x : FreeModule R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u ≤ n

@[simp]
theorem homogeneousOfOrder_zero (R : Type u) [Zero R] (n : Nat) :
    HomogeneousOfOrder (0 : FreeModule R) n := by
  simp [HomogeneousOfOrder]

theorem homogeneousOfOrder_single (R : Type u) [Zero R] (s : PTree) (a : R) :
    HomogeneousOfOrder (Finsupp.single s a) (order s) := by
  intro u hu
  exact congrArg order ((Finsupp.mem_support_single u s a).mp hu).1

@[simp]
theorem supportedUpToOrder_zero (R : Type u) [Zero R] (n : Nat) :
    SupportedUpToOrder (0 : FreeModule R) n := by
  simp [SupportedUpToOrder]

theorem HomogeneousOfOrder.supportedUpToOrder {R : Type u} [Zero R]
    {x : FreeModule R} {n : Nat} (h : HomogeneousOfOrder x n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact le_of_eq (h u hu)

theorem SupportedUpToOrder.mono {R : Type u} [Zero R]
    {x : FreeModule R} {m n : Nat} (h : SupportedUpToOrder x m) (hmn : m ≤ n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact (h u hu).trans hmn

/-- Two formal tree sums have equal coefficients through order `n`. -/
def AgreeUpToOrder {R : Type u} [Zero R] (x y : FreeModule R) (n : Nat) : Prop :=
  ∀ u, order u ≤ n → x u = y u

theorem agreeUpToOrder_refl {R : Type u} [Zero R] (x : FreeModule R) (n : Nat) :
    AgreeUpToOrder x x n := by
  intro u hu
  rfl

theorem AgreeUpToOrder.symm {R : Type u} [Zero R]
    {x y : FreeModule R} {n : Nat} (h : AgreeUpToOrder x y n) :
    AgreeUpToOrder y x n := by
  intro u hu
  exact (h u hu).symm

theorem AgreeUpToOrder.trans {R : Type u} [Zero R]
    {x y z : FreeModule R} {n : Nat}
    (hxy : AgreeUpToOrder x y n) (hyz : AgreeUpToOrder y z n) :
    AgreeUpToOrder x z n := by
  intro u hu
  exact (hxy u hu).trans (hyz u hu)

theorem AgreeUpToOrder.mono {R : Type u} [Zero R]
    {x y : FreeModule R} {m n : Nat} (h : AgreeUpToOrder x y n) (hmn : m ≤ n) :
    AgreeUpToOrder x y m := by
  intro u hu
  exact h u (hu.trans hmn)

theorem agreeUpToOrder_all_iff_eq {R : Type u} [Zero R] (x y : FreeModule R) :
    (∀ n, AgreeUpToOrder x y n) ↔ x = y := by
  constructor
  · intro h
    ext u
    exact h (order u) u le_rfl
  · intro h n u hu
    rw [h]

theorem AgreeUpToOrder.eq_of_supportedUpToOrder {R : Type u} [Zero R]
    {x y : FreeModule R} {n : Nat} (h : AgreeUpToOrder x y n)
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    x = y := by
  ext u
  by_cases hu : order u ≤ n
  · exact h u hu
  · have hx0 : x u = 0 := by
      by_contra hxne
      exact hu (hx u ((Finsupp.mem_support_iff).2 hxne))
    have hy0 : y u = 0 := by
      by_contra hyne
      exact hu (hy u ((Finsupp.mem_support_iff).2 hyne))
    rw [hx0, hy0]

theorem HomogeneousOfOrder.add {R : Type u} [AddMonoid R]
    {x y : FreeModule R} {n : Nat}
    (hx : HomogeneousOfOrder x n) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (x + y) n := by
  intro u hu
  exact rank_eq_of_mem_support_add order hx hy hu

theorem SupportedUpToOrder.add {R : Type u} [AddMonoid R]
    {x y : FreeModule R} {n : Nat}
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (x + y) n := by
  intro u hu
  exact rank_le_of_mem_support_add order hx hy hu

theorem HomogeneousOfOrder.smul {S : Type v} {R : Type u} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule R} {n : Nat} (h : HomogeneousOfOrder x n) :
    HomogeneousOfOrder (c • x) n := by
  intro u hu
  exact rank_eq_of_mem_support_smul order c h hu

theorem SupportedUpToOrder.smul {S : Type v} {R : Type u} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule R} {n : Nat} (h : SupportedUpToOrder x n) :
    SupportedUpToOrder (c • x) n := by
  intro u hu
  exact rank_le_of_mem_support_smul order c h hu

theorem supportedUpToOrder_single_of_le (R : Type u) [Zero R]
    {s : PTree} {n : Nat} (a : R) (hs : order s ≤ n) :
    SupportedUpToOrder (Finsupp.single s a) n := by
  intro u hu
  rw [congrArg order ((Finsupp.mem_support_single u s a).mp hu).1]
  exact hs

/-- The formal sum of all planar grafts of `s` at one vertex of `t`. -/
def preLieVector (R : Type u) [Semiring R] (s t : PTree) : FreeModule R :=
  ((preLieGrafts s t).map fun u => Finsupp.single u (1 : R)).sum

theorem preLieVector_apply (R : Type u) [Semiring R] (s t u : PTree) :
    preLieVector R s t u = ((preLieGrafts s t).count u : R) := by
  classical
  exact sum_single_apply_count (R := R) (preLieGrafts s t) u

theorem preLieVector_apply_eq_zero_of_order_ne (R : Type u) [Semiring R]
    (s t u : PTree) (h : Not (order u = order s + order t)) :
    preLieVector R s t u = 0 := by
  rw [preLieVector_apply]
  have hnot : Not (List.Mem u (preLieGrafts s t)) := fun hu =>
    h (order_of_mem_preLieGrafts s hu)
  have hcount : (preLieGrafts s t).count u = 0 :=
    List.count_eq_zero_of_not_mem hnot
  simp [hcount]

theorem order_of_mem_support_preLieVector (R : Type u) [Semiring R]
    (s t u : PTree) (hu : Membership.mem (preLieVector R s t).support u) :
    order u = order s + order t := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hu)
    (preLieVector_apply_eq_zero_of_order_ne R s t u h)

theorem homogeneousOfOrder_preLieVector (R : Type u) [Semiring R] (s t : PTree) :
    HomogeneousOfOrder (preLieVector R s t) (order s + order t) := by
  intro u hu
  exact order_of_mem_support_preLieVector R s t u hu

theorem supportedUpToOrder_preLieVector (R : Type u) [Semiring R] (s t : PTree) :
    SupportedUpToOrder (preLieVector R s t) (order s + order t) :=
  (homogeneousOfOrder_preLieVector R s t).supportedUpToOrder

theorem mapDomain_sum_single {β : Type v} (R : Type u) [Semiring R]
    (f : PTree → β) :
    ∀ ts : List PTree,
      Finsupp.mapDomain f ((ts.map fun u => Finsupp.single u (1 : R)).sum) =
        ((ts.map fun u => Finsupp.single (f u) (1 : R)).sum)
  | [] => by
      simp
  | t :: ts => by
      simp [mapDomain_sum_single R f ts, Finsupp.mapDomain_add]

/-- Bilinear extension of planar pre-Lie grafting to formal tree sums. -/
def preLie (R : Type u) [Semiring R] (x y : FreeModule R) : FreeModule R :=
  x.sum fun s a =>
    y.sum fun t b =>
      (a * b) • preLieVector R s t

theorem preLie_apply (R : Type u) [Semiring R]
    (x y : FreeModule R) (u : PTree) :
    preLie R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * ((preLieGrafts s t).count u : R)) := by
  simp [preLie, preLieVector_apply]

theorem preLie_apply_eq_zero_of_forall_order_ne (R : Type u) [Semiring R]
    (x y : FreeModule R) (u : PTree)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    preLie R x y u = 0 := by
  rw [preLie_apply]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hcount : (preLieGrafts s t).count u = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hu
    exact h s hs t ht (order_of_mem_preLieGrafts s hu)
  simp [hcount]

theorem exists_order_eq_of_mem_support_preLie (R : Type u) [Semiring R]
    (x y : FreeModule R) (u : PTree) (hu : u ∈ (preLie R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : preLie R x y u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.preLie (R : Type u) [Semiring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.preLie (R : Type u) [Semiring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem preLie_zero_left (R : Type u) [Semiring R] (x : FreeModule R) :
    preLie R 0 x = 0 := by
  simp [preLie]

@[simp]
theorem preLie_zero_right (R : Type u) [Semiring R] (x : FreeModule R) :
    preLie R x 0 = 0 := by
  simp [preLie]

theorem preLie_add_left (R : Type u) [Semiring R]
    (x y z : FreeModule R) :
    preLie R (x + y) z = preLie R x z + preLie R y z := by
  classical
  rw [preLie, preLie, preLie]
  apply Finsupp.sum_add_index
  · intro s hs
    simp
  · intro s hs a b
    simp [add_mul, add_smul, Finsupp.sum_add]

theorem preLie_add_right (R : Type u) [Semiring R]
    (x y z : FreeModule R) :
    preLie R x (y + z) = preLie R x y + preLie R x z := by
  classical
  rw [preLie, preLie, preLie]
  calc
    x.sum (fun s a => (y + z).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum (fun t b => (a * b) • preLieVector R s t) +
            z.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          apply Finsupp.sum_add_index
          · intro t ht
            simp
          · intro t ht a b
            simp [mul_add, add_smul]
    _ = x.sum (fun s a => y.sum fun t b => (a * b) • preLieVector R s t) +
          x.sum (fun s a => z.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.sum_add]

theorem preLie_smul_left (R : Type u) [Semiring R]
    (c : R) (x y : FreeModule R) :
    preLie R (c • x) y = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  rw [Finsupp.sum_smul_index]
  · calc
      x.sum (fun s a => y.sum fun t b => ((c * a) * b) • preLieVector R s t) =
          x.sum (fun s a => c •
            y.sum (fun t b => (a * b) • preLieVector R s t)) := by
            apply Finsupp.sum_congr
            intro s hs
            rw [Finsupp.smul_sum]
            apply Finsupp.sum_congr
            intro t ht
            rw [smul_smul]
            rw [mul_assoc]
      _ = c • x.sum (fun s a =>
            y.sum fun t b => (a * b) • preLieVector R s t) := by
            rw [Finsupp.smul_sum]
  · intro s
    simp

theorem preLie_smul_right (R : Type u) [CommSemiring R]
    (c : R) (x y : FreeModule R) :
    preLie R x (c • y) = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  calc
    x.sum (fun s a => (c • y).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum fun t b => (a * (c * b)) • preLieVector R s t) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.sum_smul_index]
          · intro t
            simp
    _ = x.sum (fun s a => c •
          y.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.smul_sum]
          apply Finsupp.sum_congr
          intro t ht
          rw [smul_smul]
          congr 1
          rw [← mul_assoc, mul_comm (x s) c, mul_assoc]
    _ = c • x.sum (fun s a =>
          y.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.smul_sum]

theorem preLie_single_single (R : Type u) [Semiring R]
    (s t : PTree) (a b : R) :
    preLie R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t := by
  rw [preLie]
  rw [Finsupp.sum_single_index (h_zero := by
    rw [Finsupp.sum_single_index (h_zero := by rw [zero_mul, zero_smul])]
    rw [zero_mul, zero_smul])]
  rw [Finsupp.sum_single_index (h_zero := by rw [mul_zero, zero_smul])]

@[simp]
theorem preLie_single_single_one (R : Type u) [Semiring R]
    (s t : PTree) :
    preLie R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t := by
  rw [preLie_single_single]
  simp

/-- The commutator bracket induced by planar pre-Lie grafting. -/
def lieBracket (R : Type u) [Ring R] (x y : FreeModule R) : FreeModule R :=
  preLie R x y - preLie R y x

theorem lieBracket_apply (R : Type u) [Ring R]
    (x y : FreeModule R) (u : PTree) :
    lieBracket R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * ((preLieGrafts s t).count u : R)) -
      y.sum (fun s a =>
        x.sum fun t b => (a * b) * ((preLieGrafts s t).count u : R)) := by
  simp [lieBracket, preLie_apply]

theorem lieBracket_apply_eq_zero_of_forall_order_ne (R : Type u) [Ring R]
    (x y : FreeModule R) (u : PTree)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    lieBracket R x y u = 0 := by
  rw [lieBracket]
  have hxy : preLie R x y u = 0 :=
    preLie_apply_eq_zero_of_forall_order_ne R x y u h
  have hyx : preLie R y x u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro t ht s hs horder
    exact h s hs t ht (by simpa [Nat.add_comm] using horder)
  simp [hxy, hyx]

theorem exists_order_eq_of_mem_support_lieBracket (R : Type u) [Ring R]
    (x y : FreeModule R) (u : PTree) (hu : u ∈ (lieBracket R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : lieBracket R x y u = 0 := by
    apply lieBracket_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.lieBracket (R : Type u) [Ring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.lieBracket (R : Type u) [Ring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem lieBracket_zero_left (R : Type u) [Ring R] (x : FreeModule R) :
    lieBracket R 0 x = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_zero_right (R : Type u) [Ring R] (x : FreeModule R) :
    lieBracket R x 0 = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_self (R : Type u) [Ring R] (x : FreeModule R) :
    lieBracket R x x = 0 := by
  simp [lieBracket]

theorem lieBracket_skew (R : Type u) [Ring R] (x y : FreeModule R) :
    lieBracket R x y = -lieBracket R y x := by
  simp [lieBracket, sub_eq_add_neg, add_comm]

theorem lieBracket_add_left (R : Type u) [Ring R]
    (x y z : FreeModule R) :
    lieBracket R (x + y) z = lieBracket R x z + lieBracket R y z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_add_right (R : Type u) [Ring R]
    (x y z : FreeModule R) :
    lieBracket R x (y + z) = lieBracket R x y + lieBracket R x z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_smul_left (R : Type u) [CommRing R]
    (c : R) (x y : FreeModule R) :
    lieBracket R (c • x) y = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_smul_right (R : Type u) [CommRing R]
    (c : R) (x y : FreeModule R) :
    lieBracket R x (c • y) = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_single_single (R : Type u) [Ring R]
    (s t : PTree) (a b : R) :
    lieBracket R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t - (b * a) • preLieVector R t s := by
  simp [lieBracket, preLie_single_single]

@[simp]
theorem lieBracket_single_single_one (R : Type u) [Ring R]
    (s t : PTree) :
    lieBracket R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t - preLieVector R t s := by
  rw [lieBracket_single_single]
  simp

@[simp]
theorem preLieVector_bullet (R : Type u) [Semiring R] (s : PTree) :
    preLieVector R s bullet = Finsupp.single (.node [s]) (1 : R) := by
  simp [preLieVector]

end PTree

namespace RootedTree

open HopfAlgebras.RootedTree

/-- Finitely supported formal sums of non-planar rooted trees. -/
abbrev FreeModule (R : Type u) [Zero R] : Type u :=
  Finsupp RootedTree R

/-- A non-planar formal tree sum supported only on trees of order `n`. -/
def HomogeneousOfOrder {R : Type u} [Zero R] (x : FreeModule R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u = n

/-- A non-planar formal tree sum supported only on trees of order at most `n`. -/
def SupportedUpToOrder {R : Type u} [Zero R] (x : FreeModule R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u ≤ n

@[simp]
theorem homogeneousOfOrder_zero (R : Type u) [Zero R] (n : Nat) :
    HomogeneousOfOrder (0 : FreeModule R) n := by
  simp [HomogeneousOfOrder]

theorem homogeneousOfOrder_single (R : Type u) [Zero R] (s : RootedTree) (a : R) :
    HomogeneousOfOrder (Finsupp.single s a) (order s) := by
  intro u hu
  exact congrArg order ((Finsupp.mem_support_single u s a).mp hu).1

@[simp]
theorem supportedUpToOrder_zero (R : Type u) [Zero R] (n : Nat) :
    SupportedUpToOrder (0 : FreeModule R) n := by
  simp [SupportedUpToOrder]

theorem HomogeneousOfOrder.supportedUpToOrder {R : Type u} [Zero R]
    {x : FreeModule R} {n : Nat} (h : HomogeneousOfOrder x n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact le_of_eq (h u hu)

theorem SupportedUpToOrder.mono {R : Type u} [Zero R]
    {x : FreeModule R} {m n : Nat} (h : SupportedUpToOrder x m) (hmn : m ≤ n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact (h u hu).trans hmn

/-- Two non-planar formal tree sums have equal coefficients through order `n`. -/
def AgreeUpToOrder {R : Type u} [Zero R] (x y : FreeModule R) (n : Nat) : Prop :=
  ∀ u, order u ≤ n → x u = y u

theorem agreeUpToOrder_refl {R : Type u} [Zero R] (x : FreeModule R) (n : Nat) :
    AgreeUpToOrder x x n := by
  intro u hu
  rfl

theorem AgreeUpToOrder.symm {R : Type u} [Zero R]
    {x y : FreeModule R} {n : Nat} (h : AgreeUpToOrder x y n) :
    AgreeUpToOrder y x n := by
  intro u hu
  exact (h u hu).symm

theorem AgreeUpToOrder.trans {R : Type u} [Zero R]
    {x y z : FreeModule R} {n : Nat}
    (hxy : AgreeUpToOrder x y n) (hyz : AgreeUpToOrder y z n) :
    AgreeUpToOrder x z n := by
  intro u hu
  exact (hxy u hu).trans (hyz u hu)

theorem AgreeUpToOrder.mono {R : Type u} [Zero R]
    {x y : FreeModule R} {m n : Nat} (h : AgreeUpToOrder x y n) (hmn : m ≤ n) :
    AgreeUpToOrder x y m := by
  intro u hu
  exact h u (hu.trans hmn)

theorem agreeUpToOrder_all_iff_eq {R : Type u} [Zero R] (x y : FreeModule R) :
    (∀ n, AgreeUpToOrder x y n) ↔ x = y := by
  constructor
  · intro h
    ext u
    exact h (order u) u le_rfl
  · intro h n u hu
    rw [h]

theorem AgreeUpToOrder.eq_of_supportedUpToOrder {R : Type u} [Zero R]
    {x y : FreeModule R} {n : Nat} (h : AgreeUpToOrder x y n)
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    x = y := by
  ext u
  by_cases hu : order u ≤ n
  · exact h u hu
  · have hx0 : x u = 0 := by
      by_contra hxne
      exact hu (hx u ((Finsupp.mem_support_iff).2 hxne))
    have hy0 : y u = 0 := by
      by_contra hyne
      exact hu (hy u ((Finsupp.mem_support_iff).2 hyne))
    rw [hx0, hy0]

theorem HomogeneousOfOrder.add {R : Type u} [AddMonoid R]
    {x y : FreeModule R} {n : Nat}
    (hx : HomogeneousOfOrder x n) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (x + y) n := by
  intro u hu
  exact rank_eq_of_mem_support_add order hx hy hu

theorem SupportedUpToOrder.add {R : Type u} [AddMonoid R]
    {x y : FreeModule R} {n : Nat}
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (x + y) n := by
  intro u hu
  exact rank_le_of_mem_support_add order hx hy hu

theorem HomogeneousOfOrder.smul {S : Type w} {R : Type u} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule R} {n : Nat} (h : HomogeneousOfOrder x n) :
    HomogeneousOfOrder (c • x) n := by
  intro u hu
  exact rank_eq_of_mem_support_smul order c h hu

theorem SupportedUpToOrder.smul {S : Type w} {R : Type u} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule R} {n : Nat} (h : SupportedUpToOrder x n) :
    SupportedUpToOrder (c • x) n := by
  intro u hu
  exact rank_le_of_mem_support_smul order c h hu

theorem supportedUpToOrder_single_of_le (R : Type u) [Zero R]
    {s : RootedTree} {n : Nat} (a : R) (hs : order s ≤ n) :
    SupportedUpToOrder (Finsupp.single s a) n := by
  intro u hu
  rw [congrArg order ((Finsupp.mem_support_single u s a).mp hu).1]
  exact hs

def preLieVectorOfPTree (R : Type u) [Semiring R] (s t : PTree) : FreeModule R :=
  ((PTree.preLieGrafts s t).map fun u => Finsupp.single (RootedTree.ofPTree u) (1 : R)).sum

theorem preLieVectorOfPTree_apply (R : Type u) [Semiring R]
    (s t : PTree) (u : RootedTree) :
    preLieVectorOfPTree R s t u =
      (((PTree.preLieGrafts s t).map RootedTree.ofPTree).count u : R) := by
  classical
  simpa [preLieVectorOfPTree, List.map_map, Function.comp_def] using
    sum_single_apply_count (R := R)
      ((PTree.preLieGrafts s t).map RootedTree.ofPTree) u

theorem preLieVectorOfPTree_apply_eq_zero_of_order_ne (R : Type u) [Semiring R]
    (s t : PTree) (u : RootedTree)
    (h : ¬ order u = order (ofPTree s) + order (ofPTree t)) :
    preLieVectorOfPTree R s t u = 0 := by
  rw [preLieVectorOfPTree_apply]
  have hnot : ¬ u ∈ (PTree.preLieGrafts s t).map RootedTree.ofPTree := by
    intro hu
    rcases List.mem_map.mp hu with ⟨v, hv, hvu⟩
    apply h
    rw [← hvu]
    simpa [RootedTree.order_ofPTree] using PTree.order_of_mem_preLieGrafts s hv
  have hcount : ((PTree.preLieGrafts s t).map RootedTree.ofPTree).count u = 0 :=
    List.count_eq_zero_of_not_mem hnot
  simp [hcount]

theorem preLieVectorOfPTree_perm_left (R : Type u) [Semiring R]
    {s s' : PTree} (hs : PTree.Perm s s') (t : PTree) :
    preLieVectorOfPTree R s t = preLieVectorOfPTree R s' t :=
  by
    simpa [preLieVectorOfPTree, List.map_map, Function.comp_def] using
      sum_single_eq_of_perm (PTree.preLieGrafts_map_ofPTree_perm_left hs t)

theorem preLieVectorOfPTree_perm_right (R : Type u) [Semiring R]
    (s : PTree) {t t' : PTree} (ht : PTree.Perm t t') :
    preLieVectorOfPTree R s t = preLieVectorOfPTree R s t' :=
  by
    simpa [preLieVectorOfPTree, List.map_map, Function.comp_def] using
      sum_single_eq_of_perm (PTree.preLieGrafts_map_ofPTree_perm_right s ht)

/-- The formal sum of all non-planar grafts of one rooted tree at another. -/
def preLieVector (R : Type u) [Semiring R] (s t : RootedTree) : FreeModule R :=
  Quotient.liftOn s
    (fun s' =>
      Quotient.liftOn t
        (fun t' => preLieVectorOfPTree R s' t')
        (fun _ _ ht => preLieVectorOfPTree_perm_right R s' ht))
    (fun s₁ s₂ hs => by
      refine Quotient.inductionOn t ?_
      intro t'
      exact preLieVectorOfPTree_perm_left R hs t')

@[simp]
theorem preLieVector_ofPTree (R : Type u) [Semiring R] (s t : PTree) :
    preLieVector R (ofPTree s) (ofPTree t) = preLieVectorOfPTree R s t :=
  rfl

@[simp]
theorem mapDomain_ofPTree_preLieVector (R : Type u) [Semiring R] (s t : PTree) :
    Finsupp.mapDomain RootedTree.ofPTree (PTree.preLieVector R s t) =
      preLieVector R (ofPTree s) (ofPTree t) := by
  rw [preLieVector_ofPTree, PTree.preLieVector, preLieVectorOfPTree,
    PTree.mapDomain_sum_single]

theorem preLieVector_apply_eq_zero_of_order_ne (R : Type u) [Semiring R]
    (s t u : RootedTree) (h : ¬ order u = order s + order t) :
    preLieVector R s t u = 0 := by
  revert h
  refine Quotient.inductionOn s ?_
  intro s'
  refine Quotient.inductionOn t ?_
  intro t' h
  exact preLieVectorOfPTree_apply_eq_zero_of_order_ne R s' t' u h

theorem order_of_mem_support_preLieVector (R : Type u) [Semiring R]
    (s t u : RootedTree) (hu : u ∈ (preLieVector R s t).support) :
    order u = order s + order t := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hu)
    (preLieVector_apply_eq_zero_of_order_ne R s t u h)

theorem homogeneousOfOrder_preLieVector (R : Type u) [Semiring R]
    (s t : RootedTree) :
    HomogeneousOfOrder (preLieVector R s t) (order s + order t) := by
  intro u hu
  exact order_of_mem_support_preLieVector R s t u hu

theorem supportedUpToOrder_preLieVector (R : Type u) [Semiring R]
    (s t : RootedTree) :
    SupportedUpToOrder (preLieVector R s t) (order s + order t) :=
  (homogeneousOfOrder_preLieVector R s t).supportedUpToOrder

/-- Bilinear extension of non-planar pre-Lie grafting to formal tree sums. -/
def preLie (R : Type u) [Semiring R] (x y : FreeModule R) : FreeModule R :=
  x.sum fun s a =>
    y.sum fun t b =>
      (a * b) • preLieVector R s t

theorem preLie_apply (R : Type u) [Semiring R]
    (x y : FreeModule R) (u : RootedTree) :
    preLie R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * preLieVector R s t u) := by
  simp [preLie]

theorem preLie_apply_eq_zero_of_forall_order_ne (R : Type u) [Semiring R]
    (x y : FreeModule R) (u : RootedTree)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    preLie R x y u = 0 := by
  rw [preLie_apply]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hvector : preLieVector R s t u = 0 :=
    preLieVector_apply_eq_zero_of_order_ne R s t u (h s hs t ht)
  simp [hvector]

theorem exists_order_eq_of_mem_support_preLie (R : Type u) [Semiring R]
    (x y : FreeModule R) (u : RootedTree) (hu : u ∈ (preLie R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : preLie R x y u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.preLie (R : Type u) [Semiring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.preLie (R : Type u) [Semiring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem preLie_zero_left (R : Type u) [Semiring R] (x : FreeModule R) :
    preLie R 0 x = 0 := by
  simp [preLie]

@[simp]
theorem preLie_zero_right (R : Type u) [Semiring R] (x : FreeModule R) :
    preLie R x 0 = 0 := by
  simp [preLie]

theorem preLie_add_left (R : Type u) [Semiring R]
    (x y z : FreeModule R) :
    preLie R (x + y) z = preLie R x z + preLie R y z := by
  classical
  rw [preLie, preLie, preLie]
  apply Finsupp.sum_add_index
  · intro s hs
    simp
  · intro s hs a b
    simp [add_mul, add_smul, Finsupp.sum_add]

theorem preLie_add_right (R : Type u) [Semiring R]
    (x y z : FreeModule R) :
    preLie R x (y + z) = preLie R x y + preLie R x z := by
  classical
  rw [preLie, preLie, preLie]
  calc
    x.sum (fun s a => (y + z).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum (fun t b => (a * b) • preLieVector R s t) +
            z.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          apply Finsupp.sum_add_index
          · intro t ht
            simp
          · intro t ht a b
            simp [mul_add, add_smul]
    _ = x.sum (fun s a => y.sum fun t b => (a * b) • preLieVector R s t) +
          x.sum (fun s a => z.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.sum_add]

theorem preLie_smul_left (R : Type u) [Semiring R]
    (c : R) (x y : FreeModule R) :
    preLie R (c • x) y = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  rw [Finsupp.sum_smul_index]
  · calc
      x.sum (fun s a => y.sum fun t b => ((c * a) * b) • preLieVector R s t) =
          x.sum (fun s a => c •
            y.sum (fun t b => (a * b) • preLieVector R s t)) := by
            apply Finsupp.sum_congr
            intro s hs
            rw [Finsupp.smul_sum]
            apply Finsupp.sum_congr
            intro t ht
            rw [smul_smul]
            rw [mul_assoc]
      _ = c • x.sum (fun s a =>
            y.sum fun t b => (a * b) • preLieVector R s t) := by
            rw [Finsupp.smul_sum]
  · intro s
    simp

theorem preLie_smul_right (R : Type u) [CommSemiring R]
    (c : R) (x y : FreeModule R) :
    preLie R x (c • y) = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  calc
    x.sum (fun s a => (c • y).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum fun t b => (a * (c * b)) • preLieVector R s t) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.sum_smul_index]
          · intro t
            simp
    _ = x.sum (fun s a => c •
          y.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.smul_sum]
          apply Finsupp.sum_congr
          intro t ht
          rw [smul_smul]
          congr 1
          rw [← mul_assoc, mul_comm (x s) c, mul_assoc]
    _ = c • x.sum (fun s a =>
          y.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.smul_sum]

theorem preLie_single_single (R : Type u) [Semiring R]
    (s t : RootedTree) (a b : R) :
    preLie R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t := by
  rw [preLie]
  rw [Finsupp.sum_single_index (h_zero := by
    rw [Finsupp.sum_single_index (h_zero := by rw [zero_mul, zero_smul])]
    rw [zero_mul, zero_smul])]
  rw [Finsupp.sum_single_index (h_zero := by rw [mul_zero, zero_smul])]

@[simp]
theorem preLie_single_single_one (R : Type u) [Semiring R]
    (s t : RootedTree) :
    preLie R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t := by
  rw [preLie_single_single]
  simp

@[simp]
theorem mapDomain_ofPTree_preLie (R : Type u) [Semiring R]
    (x y : PTree.FreeModule R) :
    Finsupp.mapDomain RootedTree.ofPTree (PTree.preLie R x y) =
      preLie R (Finsupp.mapDomain RootedTree.ofPTree x)
        (Finsupp.mapDomain RootedTree.ofPTree y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [PTree.preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [preLie_add_left, hx₁, hx₂]
  | single s a =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [PTree.preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [PTree.preLie_single_single, Finsupp.mapDomain_smul,
            mapDomain_ofPTree_preLieVector, Finsupp.mapDomain_single,
            Finsupp.mapDomain_single, preLie_single_single]

/-- The commutator bracket induced by non-planar pre-Lie grafting. -/
def lieBracket (R : Type u) [Ring R] (x y : FreeModule R) : FreeModule R :=
  preLie R x y - preLie R y x

theorem lieBracket_apply (R : Type u) [Ring R]
    (x y : FreeModule R) (u : RootedTree) :
    lieBracket R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * preLieVector R s t u) -
      y.sum (fun s a =>
        x.sum fun t b => (a * b) * preLieVector R s t u) := by
  simp [lieBracket, preLie_apply]

theorem lieBracket_apply_eq_zero_of_forall_order_ne (R : Type u) [Ring R]
    (x y : FreeModule R) (u : RootedTree)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    lieBracket R x y u = 0 := by
  rw [lieBracket]
  have hxy : preLie R x y u = 0 :=
    preLie_apply_eq_zero_of_forall_order_ne R x y u h
  have hyx : preLie R y x u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro t ht s hs horder
    exact h s hs t ht (by simpa [Nat.add_comm] using horder)
  simp [hxy, hyx]

theorem exists_order_eq_of_mem_support_lieBracket (R : Type u) [Ring R]
    (x y : FreeModule R) (u : RootedTree) (hu : u ∈ (lieBracket R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : lieBracket R x y u = 0 := by
    apply lieBracket_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.lieBracket (R : Type u) [Ring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.lieBracket (R : Type u) [Ring R]
    {x y : FreeModule R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem lieBracket_zero_left (R : Type u) [Ring R] (x : FreeModule R) :
    lieBracket R 0 x = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_zero_right (R : Type u) [Ring R] (x : FreeModule R) :
    lieBracket R x 0 = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_self (R : Type u) [Ring R] (x : FreeModule R) :
    lieBracket R x x = 0 := by
  simp [lieBracket]

theorem lieBracket_skew (R : Type u) [Ring R] (x y : FreeModule R) :
    lieBracket R x y = -lieBracket R y x := by
  simp [lieBracket, sub_eq_add_neg, add_comm]

theorem lieBracket_add_left (R : Type u) [Ring R]
    (x y z : FreeModule R) :
    lieBracket R (x + y) z = lieBracket R x z + lieBracket R y z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_add_right (R : Type u) [Ring R]
    (x y z : FreeModule R) :
    lieBracket R x (y + z) = lieBracket R x y + lieBracket R x z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_smul_left (R : Type u) [CommRing R]
    (c : R) (x y : FreeModule R) :
    lieBracket R (c • x) y = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_smul_right (R : Type u) [CommRing R]
    (c : R) (x y : FreeModule R) :
    lieBracket R x (c • y) = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_single_single (R : Type u) [Ring R]
    (s t : RootedTree) (a b : R) :
    lieBracket R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t - (b * a) • preLieVector R t s := by
  simp [lieBracket, preLie_single_single]

@[simp]
theorem lieBracket_single_single_one (R : Type u) [Ring R]
    (s t : RootedTree) :
    lieBracket R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t - preLieVector R t s := by
  rw [lieBracket_single_single]
  simp

@[simp]
theorem mapDomain_ofPTree_lieBracket (R : Type u) [Ring R]
    (x y : PTree.FreeModule R) :
    Finsupp.mapDomain RootedTree.ofPTree (PTree.lieBracket R x y) =
      lieBracket R (Finsupp.mapDomain RootedTree.ofPTree x)
        (Finsupp.mapDomain RootedTree.ofPTree y) := by
  rw [PTree.lieBracket, lieBracket, Finsupp.mapDomain_sub,
    mapDomain_ofPTree_preLie, mapDomain_ofPTree_preLie]

end RootedTree

namespace PLTree

open HopfAlgebras.PLTree

variable {α : Type u}

/-- Finitely supported formal sums of labelled planar rooted trees. -/
abbrev FreeModule (α : Type u) (R : Type v) [Zero R] : Type (max u v) :=
  Finsupp (PLTree α) R

/-- A labelled formal tree sum supported only on trees of order `n`. -/
def HomogeneousOfOrder {R : Type v} [Zero R] (x : FreeModule α R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u = n

/-- A labelled formal tree sum supported only on trees of order at most `n`. -/
def SupportedUpToOrder {R : Type v} [Zero R] (x : FreeModule α R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u ≤ n

@[simp]
theorem homogeneousOfOrder_zero (R : Type v) [Zero R] (n : Nat) :
    HomogeneousOfOrder (0 : FreeModule α R) n := by
  simp [HomogeneousOfOrder]

theorem homogeneousOfOrder_single (R : Type v) [Zero R] (s : PLTree α) (a : R) :
    HomogeneousOfOrder (Finsupp.single s a) (order s) := by
  intro u hu
  exact congrArg order ((Finsupp.mem_support_single u s a).mp hu).1

@[simp]
theorem supportedUpToOrder_zero (R : Type v) [Zero R] (n : Nat) :
    SupportedUpToOrder (0 : FreeModule α R) n := by
  simp [SupportedUpToOrder]

theorem HomogeneousOfOrder.supportedUpToOrder {R : Type v} [Zero R]
    {x : FreeModule α R} {n : Nat} (h : HomogeneousOfOrder x n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact le_of_eq (h u hu)

theorem SupportedUpToOrder.mono {R : Type v} [Zero R]
    {x : FreeModule α R} {m n : Nat} (h : SupportedUpToOrder x m) (hmn : m ≤ n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact (h u hu).trans hmn

/-- Two labelled planar formal tree sums have equal coefficients through order `n`. -/
def AgreeUpToOrder {R : Type v} [Zero R]
    (x y : FreeModule α R) (n : Nat) : Prop :=
  ∀ u, order u ≤ n → x u = y u

theorem agreeUpToOrder_refl {R : Type v} [Zero R]
    (x : FreeModule α R) (n : Nat) :
    AgreeUpToOrder x x n := by
  intro u hu
  rfl

theorem AgreeUpToOrder.symm {R : Type v} [Zero R]
    {x y : FreeModule α R} {n : Nat} (h : AgreeUpToOrder x y n) :
    AgreeUpToOrder y x n := by
  intro u hu
  exact (h u hu).symm

theorem AgreeUpToOrder.trans {R : Type v} [Zero R]
    {x y z : FreeModule α R} {n : Nat}
    (hxy : AgreeUpToOrder x y n) (hyz : AgreeUpToOrder y z n) :
    AgreeUpToOrder x z n := by
  intro u hu
  exact (hxy u hu).trans (hyz u hu)

theorem AgreeUpToOrder.mono {R : Type v} [Zero R]
    {x y : FreeModule α R} {m n : Nat} (h : AgreeUpToOrder x y n)
    (hmn : m ≤ n) :
    AgreeUpToOrder x y m := by
  intro u hu
  exact h u (hu.trans hmn)

theorem agreeUpToOrder_all_iff_eq {R : Type v} [Zero R]
    (x y : FreeModule α R) :
    (∀ n, AgreeUpToOrder x y n) ↔ x = y := by
  constructor
  · intro h
    ext u
    exact h (order u) u le_rfl
  · intro h n u hu
    rw [h]

theorem AgreeUpToOrder.eq_of_supportedUpToOrder {R : Type v} [Zero R]
    {x y : FreeModule α R} {n : Nat} (h : AgreeUpToOrder x y n)
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    x = y := by
  ext u
  by_cases hu : order u ≤ n
  · exact h u hu
  · have hx0 : x u = 0 := by
      by_contra hxne
      exact hu (hx u ((Finsupp.mem_support_iff).2 hxne))
    have hy0 : y u = 0 := by
      by_contra hyne
      exact hu (hy u ((Finsupp.mem_support_iff).2 hyne))
    rw [hx0, hy0]

theorem HomogeneousOfOrder.add {R : Type v} [AddMonoid R]
    {x y : FreeModule α R} {n : Nat}
    (hx : HomogeneousOfOrder x n) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (x + y) n := by
  intro u hu
  exact rank_eq_of_mem_support_add order hx hy hu

theorem SupportedUpToOrder.add {R : Type v} [AddMonoid R]
    {x y : FreeModule α R} {n : Nat}
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (x + y) n := by
  intro u hu
  exact rank_le_of_mem_support_add order hx hy hu

theorem HomogeneousOfOrder.smul {S : Type w} {R : Type v} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule α R} {n : Nat} (h : HomogeneousOfOrder x n) :
    HomogeneousOfOrder (c • x) n := by
  intro u hu
  exact rank_eq_of_mem_support_smul order c h hu

theorem SupportedUpToOrder.smul {S : Type w} {R : Type v} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule α R} {n : Nat} (h : SupportedUpToOrder x n) :
    SupportedUpToOrder (c • x) n := by
  intro u hu
  exact rank_le_of_mem_support_smul order c h hu

theorem supportedUpToOrder_single_of_le (R : Type v) [Zero R]
    {s : PLTree α} {n : Nat} (a : R) (hs : order s ≤ n) :
    SupportedUpToOrder (Finsupp.single s a) n := by
  intro u hu
  rw [congrArg order ((Finsupp.mem_support_single u s a).mp hu).1]
  exact hs

/-- The formal sum of all labelled planar grafts of `s` at one vertex of `t`. -/
def preLieVector (R : Type v) [Semiring R] (s t : PLTree α) : FreeModule α R :=
  ((preLieGrafts s t).map fun u => Finsupp.single u (1 : R)).sum

theorem preLieVector_apply (R : Type v) [Semiring R] (s t u : PLTree α) :
    preLieVector R s t u = ((preLieGrafts s t).count u : R) := by
  classical
  exact sum_single_apply_count (R := R) (preLieGrafts s t) u

theorem preLieVector_apply_eq_zero_of_order_ne (R : Type v) [Semiring R]
    (s t u : PLTree α) (h : Not (order u = order s + order t)) :
    preLieVector R s t u = 0 := by
  rw [preLieVector_apply]
  have hnot : Not (List.Mem u (preLieGrafts s t)) := fun hu =>
    h (order_of_mem_preLieGrafts s hu)
  have hcount : (preLieGrafts s t).count u = 0 :=
    List.count_eq_zero_of_not_mem hnot
  simp [hcount]

theorem order_of_mem_support_preLieVector (R : Type v) [Semiring R]
    (s t u : PLTree α) (hu : Membership.mem (preLieVector R s t).support u) :
    order u = order s + order t := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hu)
    (preLieVector_apply_eq_zero_of_order_ne R s t u h)

theorem homogeneousOfOrder_preLieVector (R : Type v) [Semiring R] (s t : PLTree α) :
    HomogeneousOfOrder (preLieVector R s t) (order s + order t) := by
  intro u hu
  exact order_of_mem_support_preLieVector R s t u hu

theorem supportedUpToOrder_preLieVector (R : Type v) [Semiring R] (s t : PLTree α) :
    SupportedUpToOrder (preLieVector R s t) (order s + order t) :=
  (homogeneousOfOrder_preLieVector R s t).supportedUpToOrder

theorem mapDomain_sum_single {β : Type w} (R : Type v) [Semiring R]
    (f : PLTree α → β) :
    ∀ ts : List (PLTree α),
      Finsupp.mapDomain f ((ts.map fun u => Finsupp.single u (1 : R)).sum) =
        ((ts.map fun u => Finsupp.single (f u) (1 : R)).sum)
  | [] => by
      simp
  | t :: ts => by
      simp [mapDomain_sum_single R f ts, Finsupp.mapDomain_add]

/-- Bilinear extension of labelled planar pre-Lie grafting. -/
def preLie (R : Type v) [Semiring R]
    (x y : FreeModule α R) : FreeModule α R :=
  x.sum fun s a =>
    y.sum fun t b =>
      (a * b) • preLieVector R s t

theorem preLie_apply (R : Type v) [Semiring R]
    (x y : FreeModule α R) (u : PLTree α) :
    preLie R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * ((preLieGrafts s t).count u : R)) := by
  simp [preLie, preLieVector_apply]

theorem preLie_apply_eq_zero_of_forall_order_ne (R : Type v) [Semiring R]
    (x y : FreeModule α R) (u : PLTree α)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    preLie R x y u = 0 := by
  rw [preLie_apply]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hcount : (preLieGrafts s t).count u = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hu
    exact h s hs t ht (order_of_mem_preLieGrafts s hu)
  simp [hcount]

theorem exists_order_eq_of_mem_support_preLie (R : Type v) [Semiring R]
    (x y : FreeModule α R) (u : PLTree α) (hu : u ∈ (preLie R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : preLie R x y u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.preLie (R : Type v) [Semiring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.preLie (R : Type v) [Semiring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem preLie_zero_left (R : Type v) [Semiring R] (x : FreeModule α R) :
    preLie R 0 x = 0 := by
  simp [preLie]

@[simp]
theorem preLie_zero_right (R : Type v) [Semiring R] (x : FreeModule α R) :
    preLie R x 0 = 0 := by
  simp [preLie]

theorem preLie_add_left (R : Type v) [Semiring R]
    (x y z : FreeModule α R) :
    preLie R (x + y) z = preLie R x z + preLie R y z := by
  classical
  rw [preLie, preLie, preLie]
  apply Finsupp.sum_add_index
  · intro s hs
    simp
  · intro s hs a b
    simp [add_mul, add_smul, Finsupp.sum_add]

theorem preLie_add_right (R : Type v) [Semiring R]
    (x y z : FreeModule α R) :
    preLie R x (y + z) = preLie R x y + preLie R x z := by
  classical
  rw [preLie, preLie, preLie]
  calc
    x.sum (fun s a => (y + z).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum (fun t b => (a * b) • preLieVector R s t) +
            z.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          apply Finsupp.sum_add_index
          · intro t ht
            simp
          · intro t ht a b
            simp [mul_add, add_smul]
    _ = x.sum (fun s a => y.sum fun t b => (a * b) • preLieVector R s t) +
          x.sum (fun s a => z.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.sum_add]

theorem preLie_smul_left (R : Type v) [Semiring R]
    (c : R) (x y : FreeModule α R) :
    preLie R (c • x) y = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  rw [Finsupp.sum_smul_index]
  · calc
      x.sum (fun s a => y.sum fun t b => ((c * a) * b) • preLieVector R s t) =
          x.sum (fun s a => c •
            y.sum (fun t b => (a * b) • preLieVector R s t)) := by
            apply Finsupp.sum_congr
            intro s hs
            rw [Finsupp.smul_sum]
            apply Finsupp.sum_congr
            intro t ht
            rw [smul_smul]
            rw [mul_assoc]
      _ = c • x.sum (fun s a =>
            y.sum fun t b => (a * b) • preLieVector R s t) := by
            rw [Finsupp.smul_sum]
  · intro s
    simp

theorem preLie_smul_right (R : Type v) [CommSemiring R]
    (c : R) (x y : FreeModule α R) :
    preLie R x (c • y) = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  calc
    x.sum (fun s a => (c • y).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum fun t b => (a * (c * b)) • preLieVector R s t) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.sum_smul_index]
          · intro t
            simp
    _ = x.sum (fun s a => c •
          y.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.smul_sum]
          apply Finsupp.sum_congr
          intro t ht
          rw [smul_smul]
          congr 1
          rw [← mul_assoc, mul_comm (x s) c, mul_assoc]
    _ = c • x.sum (fun s a =>
          y.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.smul_sum]

theorem preLie_single_single (R : Type v) [Semiring R]
    (s t : PLTree α) (a b : R) :
    preLie R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t := by
  rw [preLie]
  rw [Finsupp.sum_single_index (h_zero := by
    rw [Finsupp.sum_single_index (h_zero := by rw [zero_mul, zero_smul])]
    rw [zero_mul, zero_smul])]
  rw [Finsupp.sum_single_index (h_zero := by rw [mul_zero, zero_smul])]

@[simp]
theorem preLie_single_single_one (R : Type v) [Semiring R]
    (s t : PLTree α) :
    preLie R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t := by
  rw [preLie_single_single]
  simp

/-- The commutator bracket induced by labelled planar pre-Lie grafting. -/
def lieBracket (R : Type v) [Ring R]
    (x y : FreeModule α R) : FreeModule α R :=
  preLie R x y - preLie R y x

theorem lieBracket_apply (R : Type v) [Ring R]
    (x y : FreeModule α R) (u : PLTree α) :
    lieBracket R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * ((preLieGrafts s t).count u : R)) -
      y.sum (fun s a =>
        x.sum fun t b => (a * b) * ((preLieGrafts s t).count u : R)) := by
  simp [lieBracket, preLie_apply]

theorem lieBracket_apply_eq_zero_of_forall_order_ne (R : Type v) [Ring R]
    (x y : FreeModule α R) (u : PLTree α)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    lieBracket R x y u = 0 := by
  rw [lieBracket]
  have hxy : preLie R x y u = 0 :=
    preLie_apply_eq_zero_of_forall_order_ne R x y u h
  have hyx : preLie R y x u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro t ht s hs horder
    exact h s hs t ht (by simpa [Nat.add_comm] using horder)
  simp [hxy, hyx]

theorem exists_order_eq_of_mem_support_lieBracket (R : Type v) [Ring R]
    (x y : FreeModule α R) (u : PLTree α) (hu : u ∈ (lieBracket R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : lieBracket R x y u = 0 := by
    apply lieBracket_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.lieBracket (R : Type v) [Ring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.lieBracket (R : Type v) [Ring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem lieBracket_zero_left (R : Type v) [Ring R] (x : FreeModule α R) :
    lieBracket R 0 x = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_zero_right (R : Type v) [Ring R] (x : FreeModule α R) :
    lieBracket R x 0 = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_self (R : Type v) [Ring R] (x : FreeModule α R) :
    lieBracket R x x = 0 := by
  simp [lieBracket]

theorem lieBracket_skew (R : Type v) [Ring R] (x y : FreeModule α R) :
    lieBracket R x y = -lieBracket R y x := by
  simp [lieBracket, sub_eq_add_neg, add_comm]

theorem lieBracket_add_left (R : Type v) [Ring R]
    (x y z : FreeModule α R) :
    lieBracket R (x + y) z = lieBracket R x z + lieBracket R y z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_add_right (R : Type v) [Ring R]
    (x y z : FreeModule α R) :
    lieBracket R x (y + z) = lieBracket R x y + lieBracket R x z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_smul_left (R : Type v) [CommRing R]
    (c : R) (x y : FreeModule α R) :
    lieBracket R (c • x) y = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_smul_right (R : Type v) [CommRing R]
    (c : R) (x y : FreeModule α R) :
    lieBracket R x (c • y) = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_single_single (R : Type v) [Ring R]
    (s t : PLTree α) (a b : R) :
    lieBracket R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t - (b * a) • preLieVector R t s := by
  simp [lieBracket, preLie_single_single]

@[simp]
theorem lieBracket_single_single_one (R : Type v) [Ring R]
    (s t : PLTree α) :
    lieBracket R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t - preLieVector R t s := by
  rw [lieBracket_single_single]
  simp

@[simp]
theorem erase_preLieVector (R : Type v) [Semiring R] (s t : PLTree α) :
    Finsupp.mapDomain erase (preLieVector R s t) =
      PTree.preLieVector R (erase s) (erase t) := by
  rw [preLieVector, PTree.preLieVector, mapDomain_sum_single]
  change
    ((preLieGrafts s t).map fun u => Finsupp.single (erase u) (1 : R)).sum =
      ((PTree.preLieGrafts (erase s) (erase t)).map fun u =>
        Finsupp.single u (1 : R)).sum
  have h :
      (List.map (fun u => Finsupp.single (erase u) (1 : R)) (preLieGrafts s t)) =
        (List.map (fun u => Finsupp.single u (1 : R))
          (PTree.preLieGrafts (erase s) (erase t))) := by
    calc
      List.map (fun u => Finsupp.single (erase u) (1 : R)) (preLieGrafts s t) =
          List.map (fun u => Finsupp.single u (1 : R))
            ((preLieGrafts s t).map erase) := by
            rw [List.map_map]
            rfl
      _ = List.map (fun u => Finsupp.single u (1 : R))
            (PTree.preLieGrafts (erase s) (erase t)) := by
            rw [erase_preLieGrafts]
  exact congrArg List.sum h

@[simp]
theorem map_preLieVector {β : Type w} (R : Type v) [Semiring R]
    (f : α → β) (s t : PLTree α) :
    Finsupp.mapDomain (map f) (preLieVector R s t) =
      preLieVector R (map f s) (map f t) := by
  rw [preLieVector, preLieVector, mapDomain_sum_single]
  change
    ((preLieGrafts s t).map fun u => Finsupp.single (map f u) (1 : R)).sum =
      ((preLieGrafts (map f s) (map f t)).map fun u => Finsupp.single u (1 : R)).sum
  have h :
      (List.map (fun u => Finsupp.single (map f u) (1 : R)) (preLieGrafts s t)) =
        (List.map (fun u => Finsupp.single u (1 : R))
          (preLieGrafts (map f s) (map f t))) := by
    calc
      List.map (fun u => Finsupp.single (map f u) (1 : R)) (preLieGrafts s t) =
          List.map (fun u => Finsupp.single u (1 : R))
            ((preLieGrafts s t).map (map f)) := by
            rw [List.map_map]
            rfl
      _ = List.map (fun u => Finsupp.single u (1 : R))
            (preLieGrafts (map f s) (map f t)) := by
            rw [map_preLieGrafts]
  exact congrArg List.sum h

@[simp]
theorem constLabel_preLieVector (R : Type v) [Semiring R]
    (a : α) (s t : PTree) :
    Finsupp.mapDomain (constLabel a) (PTree.preLieVector R s t) =
      preLieVector R (constLabel a s) (constLabel a t) := by
  rw [PTree.preLieVector, preLieVector, PTree.mapDomain_sum_single]
  change
    ((PTree.preLieGrafts s t).map fun u => Finsupp.single (constLabel a u) (1 : R)).sum =
      ((preLieGrafts (constLabel a s) (constLabel a t)).map fun u =>
        Finsupp.single u (1 : R)).sum
  have h :
      (List.map (fun u => Finsupp.single (constLabel a u) (1 : R))
          (PTree.preLieGrafts s t)) =
        (List.map (fun u => Finsupp.single u (1 : R))
          (preLieGrafts (constLabel a s) (constLabel a t))) := by
    calc
      List.map (fun u => Finsupp.single (constLabel a u) (1 : R))
          (PTree.preLieGrafts s t) =
          List.map (fun u => Finsupp.single u (1 : R))
            ((PTree.preLieGrafts s t).map (constLabel a)) := by
            rw [List.map_map]
            rfl
      _ = List.map (fun u => Finsupp.single u (1 : R))
            (preLieGrafts (constLabel a s) (constLabel a t)) := by
            rw [constLabel_preLieGrafts]
  exact congrArg List.sum h

@[simp]
theorem erase_preLie (R : Type v) [Semiring R]
    (x y : FreeModule α R) :
    Finsupp.mapDomain erase (preLie R x y) =
      PTree.preLie R (Finsupp.mapDomain erase x) (Finsupp.mapDomain erase y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [PTree.preLie_add_left, hx₁, hx₂]
  | single s a =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [PTree.preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [preLie_single_single, Finsupp.mapDomain_smul, erase_preLieVector,
            Finsupp.mapDomain_single, Finsupp.mapDomain_single, PTree.preLie_single_single]

@[simp]
theorem map_preLie {β : Type w} (R : Type v) [Semiring R]
    (f : α → β) (x y : FreeModule α R) :
    Finsupp.mapDomain (map f) (preLie R x y) =
      preLie R (Finsupp.mapDomain (map f) x)
        (Finsupp.mapDomain (map f) y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [preLie_add_left, hx₁, hx₂]
  | single s a =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [preLie_single_single, Finsupp.mapDomain_smul, map_preLieVector,
            Finsupp.mapDomain_single, Finsupp.mapDomain_single, preLie_single_single]

@[simp]
theorem constLabel_preLie (R : Type v) [Semiring R]
    (a : α) (x y : PTree.FreeModule R) :
    Finsupp.mapDomain (constLabel a) (PTree.preLie R x y) =
      preLie R (Finsupp.mapDomain (constLabel a) x)
        (Finsupp.mapDomain (constLabel a) y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [PTree.preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [preLie_add_left, hx₁, hx₂]
  | single s aₛ =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [PTree.preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [PTree.preLie_single_single, Finsupp.mapDomain_smul, constLabel_preLieVector,
            Finsupp.mapDomain_single, Finsupp.mapDomain_single, preLie_single_single]

@[simp]
theorem erase_lieBracket (R : Type v) [Ring R]
    (x y : FreeModule α R) :
    Finsupp.mapDomain erase (lieBracket R x y) =
      PTree.lieBracket R (Finsupp.mapDomain erase x)
        (Finsupp.mapDomain erase y) := by
  rw [lieBracket, PTree.lieBracket, Finsupp.mapDomain_sub, erase_preLie, erase_preLie]

@[simp]
theorem map_lieBracket {β : Type w} (R : Type v) [Ring R]
    (f : α → β) (x y : FreeModule α R) :
    Finsupp.mapDomain (map f) (lieBracket R x y) =
      lieBracket R (Finsupp.mapDomain (map f) x)
        (Finsupp.mapDomain (map f) y) := by
  rw [lieBracket, lieBracket, Finsupp.mapDomain_sub, map_preLie, map_preLie]

@[simp]
theorem constLabel_lieBracket (R : Type v) [Ring R]
    (a : α) (x y : PTree.FreeModule R) :
    Finsupp.mapDomain (constLabel a) (PTree.lieBracket R x y) =
      lieBracket R (Finsupp.mapDomain (constLabel a) x)
        (Finsupp.mapDomain (constLabel a) y) := by
  rw [PTree.lieBracket, lieBracket, Finsupp.mapDomain_sub,
    constLabel_preLie, constLabel_preLie]

end PLTree

namespace LRootedTree

open HopfAlgebras.LRootedTree

variable {α : Type u}

/-- Finitely supported formal sums of non-planar labelled rooted trees. -/
abbrev FreeModule (α : Type u) (R : Type v) [Zero R] : Type (max u v) :=
  Finsupp (LRootedTree α) R

/-- A non-planar labelled formal tree sum supported only on trees of order `n`. -/
def HomogeneousOfOrder {R : Type v} [Zero R] (x : FreeModule α R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u = n

/-- A non-planar labelled formal tree sum supported only on trees of order at most `n`. -/
def SupportedUpToOrder {R : Type v} [Zero R] (x : FreeModule α R) (n : Nat) : Prop :=
  ∀ u ∈ x.support, order u ≤ n

@[simp]
theorem homogeneousOfOrder_zero (R : Type v) [Zero R] (n : Nat) :
    HomogeneousOfOrder (0 : FreeModule α R) n := by
  simp [HomogeneousOfOrder]

theorem homogeneousOfOrder_single (R : Type v) [Zero R] (s : LRootedTree α) (a : R) :
    HomogeneousOfOrder (Finsupp.single s a) (order s) := by
  intro u hu
  exact congrArg order ((Finsupp.mem_support_single u s a).mp hu).1

@[simp]
theorem supportedUpToOrder_zero (R : Type v) [Zero R] (n : Nat) :
    SupportedUpToOrder (0 : FreeModule α R) n := by
  simp [SupportedUpToOrder]

theorem HomogeneousOfOrder.supportedUpToOrder {R : Type v} [Zero R]
    {x : FreeModule α R} {n : Nat} (h : HomogeneousOfOrder x n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact le_of_eq (h u hu)

theorem SupportedUpToOrder.mono {R : Type v} [Zero R]
    {x : FreeModule α R} {m n : Nat} (h : SupportedUpToOrder x m) (hmn : m ≤ n) :
    SupportedUpToOrder x n := by
  intro u hu
  exact (h u hu).trans hmn

/-- Two non-planar labelled formal tree sums have equal coefficients through order `n`. -/
def AgreeUpToOrder {R : Type v} [Zero R]
    (x y : FreeModule α R) (n : Nat) : Prop :=
  ∀ u, order u ≤ n → x u = y u

theorem agreeUpToOrder_refl {R : Type v} [Zero R]
    (x : FreeModule α R) (n : Nat) :
    AgreeUpToOrder x x n := by
  intro u hu
  rfl

theorem AgreeUpToOrder.symm {R : Type v} [Zero R]
    {x y : FreeModule α R} {n : Nat} (h : AgreeUpToOrder x y n) :
    AgreeUpToOrder y x n := by
  intro u hu
  exact (h u hu).symm

theorem AgreeUpToOrder.trans {R : Type v} [Zero R]
    {x y z : FreeModule α R} {n : Nat}
    (hxy : AgreeUpToOrder x y n) (hyz : AgreeUpToOrder y z n) :
    AgreeUpToOrder x z n := by
  intro u hu
  exact (hxy u hu).trans (hyz u hu)

theorem AgreeUpToOrder.mono {R : Type v} [Zero R]
    {x y : FreeModule α R} {m n : Nat} (h : AgreeUpToOrder x y n)
    (hmn : m ≤ n) :
    AgreeUpToOrder x y m := by
  intro u hu
  exact h u (hu.trans hmn)

theorem agreeUpToOrder_all_iff_eq {R : Type v} [Zero R]
    (x y : FreeModule α R) :
    (∀ n, AgreeUpToOrder x y n) ↔ x = y := by
  constructor
  · intro h
    ext u
    exact h (order u) u le_rfl
  · intro h n u hu
    rw [h]

theorem AgreeUpToOrder.eq_of_supportedUpToOrder {R : Type v} [Zero R]
    {x y : FreeModule α R} {n : Nat} (h : AgreeUpToOrder x y n)
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    x = y := by
  ext u
  by_cases hu : order u ≤ n
  · exact h u hu
  · have hx0 : x u = 0 := by
      by_contra hxne
      exact hu (hx u ((Finsupp.mem_support_iff).2 hxne))
    have hy0 : y u = 0 := by
      by_contra hyne
      exact hu (hy u ((Finsupp.mem_support_iff).2 hyne))
    rw [hx0, hy0]

theorem HomogeneousOfOrder.add {R : Type v} [AddMonoid R]
    {x y : FreeModule α R} {n : Nat}
    (hx : HomogeneousOfOrder x n) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (x + y) n := by
  intro u hu
  exact rank_eq_of_mem_support_add order hx hy hu

theorem SupportedUpToOrder.add {R : Type v} [AddMonoid R]
    {x y : FreeModule α R} {n : Nat}
    (hx : SupportedUpToOrder x n) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (x + y) n := by
  intro u hu
  exact rank_le_of_mem_support_add order hx hy hu

theorem HomogeneousOfOrder.smul {S : Type w} {R : Type v} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule α R} {n : Nat} (h : HomogeneousOfOrder x n) :
    HomogeneousOfOrder (c • x) n := by
  intro u hu
  exact rank_eq_of_mem_support_smul order c h hu

theorem SupportedUpToOrder.smul {S : Type w} {R : Type v} [Zero R] [SMulZeroClass S R]
    (c : S) {x : FreeModule α R} {n : Nat} (h : SupportedUpToOrder x n) :
    SupportedUpToOrder (c • x) n := by
  intro u hu
  exact rank_le_of_mem_support_smul order c h hu

theorem supportedUpToOrder_single_of_le (R : Type v) [Zero R]
    {s : LRootedTree α} {n : Nat} (a : R) (hs : order s ≤ n) :
    SupportedUpToOrder (Finsupp.single s a) n := by
  intro u hu
  rw [congrArg order ((Finsupp.mem_support_single u s a).mp hu).1]
  exact hs

def preLieVectorOfPLTree (R : Type v) [Semiring R]
    (s t : PLTree α) : FreeModule α R :=
  ((PLTree.preLieGrafts s t).map fun u => Finsupp.single (LRootedTree.ofPLTree u) (1 : R)).sum

theorem preLieVectorOfPLTree_apply (R : Type v) [Semiring R]
    (s t : PLTree α) (u : LRootedTree α) :
    preLieVectorOfPLTree R s t u =
      (((PLTree.preLieGrafts s t).map LRootedTree.ofPLTree).count u : R) := by
  classical
  simpa [preLieVectorOfPLTree, List.map_map, Function.comp_def] using
    sum_single_apply_count (R := R)
      ((PLTree.preLieGrafts s t).map LRootedTree.ofPLTree) u

theorem preLieVectorOfPLTree_apply_eq_zero_of_order_ne (R : Type v) [Semiring R]
    (s t : PLTree α) (u : LRootedTree α)
    (h : ¬ order u = order (ofPLTree s) + order (ofPLTree t)) :
    preLieVectorOfPLTree R s t u = 0 := by
  rw [preLieVectorOfPLTree_apply]
  have hnot : ¬ u ∈ (PLTree.preLieGrafts s t).map LRootedTree.ofPLTree := by
    intro hu
    rcases List.mem_map.mp hu with ⟨v, hv, hvu⟩
    apply h
    rw [← hvu]
    simpa [LRootedTree.order_ofPLTree] using PLTree.order_of_mem_preLieGrafts s hv
  have hcount : ((PLTree.preLieGrafts s t).map LRootedTree.ofPLTree).count u = 0 :=
    List.count_eq_zero_of_not_mem hnot
  simp [hcount]

theorem preLieVectorOfPLTree_perm_left (R : Type v) [Semiring R]
    {s s' : PLTree α} (hs : PLTree.Perm s s') (t : PLTree α) :
    preLieVectorOfPLTree R s t = preLieVectorOfPLTree R s' t :=
  by
    simpa [preLieVectorOfPLTree, List.map_map, Function.comp_def] using
      sum_single_eq_of_perm (PLTree.preLieGrafts_map_ofPLTree_perm_left hs t)

theorem preLieVectorOfPLTree_perm_right (R : Type v) [Semiring R]
    (s : PLTree α) {t t' : PLTree α} (ht : PLTree.Perm t t') :
    preLieVectorOfPLTree R s t = preLieVectorOfPLTree R s t' :=
  by
    simpa [preLieVectorOfPLTree, List.map_map, Function.comp_def] using
      sum_single_eq_of_perm (PLTree.preLieGrafts_map_ofPLTree_perm_right s ht)

/-- The formal sum of all non-planar labelled grafts of one tree at another. -/
def preLieVector (R : Type v) [Semiring R]
    (s t : LRootedTree α) : FreeModule α R :=
  Quotient.liftOn s
    (fun s' =>
      Quotient.liftOn t
        (fun t' => preLieVectorOfPLTree R s' t')
        (fun _ _ ht => preLieVectorOfPLTree_perm_right R s' ht))
    (fun s₁ s₂ hs => by
      refine Quotient.inductionOn t ?_
      intro t'
      exact preLieVectorOfPLTree_perm_left R hs t')

@[simp]
theorem preLieVector_ofPLTree (R : Type v) [Semiring R]
    (s t : PLTree α) :
    preLieVector R (ofPLTree s) (ofPLTree t) = preLieVectorOfPLTree R s t :=
  rfl

@[simp]
theorem mapDomain_ofPLTree_preLieVector (R : Type v) [Semiring R]
    (s t : PLTree α) :
    Finsupp.mapDomain LRootedTree.ofPLTree (PLTree.preLieVector R s t) =
      preLieVector R (ofPLTree s) (ofPLTree t) := by
  rw [preLieVector_ofPLTree, PLTree.preLieVector, preLieVectorOfPLTree,
    PLTree.mapDomain_sum_single]

@[simp]
theorem erase_preLieVector (R : Type v) [Semiring R]
    (s t : LRootedTree α) :
    Finsupp.mapDomain LRootedTree.erase (preLieVector R s t) =
      RootedTree.preLieVector R (erase s) (erase t) := by
  refine Quotient.inductionOn₂ s t ?_
  intro s t
  change
    Finsupp.mapDomain LRootedTree.erase
        (preLieVector R (LRootedTree.ofPLTree s) (LRootedTree.ofPLTree t)) =
      RootedTree.preLieVector R (RootedTree.ofPTree (PLTree.erase s))
        (RootedTree.ofPTree (PLTree.erase t))
  rw [preLieVector_ofPLTree, RootedTree.preLieVector_ofPTree]
  rw [preLieVectorOfPLTree, RootedTree.preLieVectorOfPTree]
  have hmap :
      Finsupp.mapDomain LRootedTree.erase
          (((PLTree.preLieGrafts s t).map
            (fun u => Finsupp.single (LRootedTree.ofPLTree u) (1 : R))).sum) =
        ((PLTree.preLieGrafts s t).map
          (fun u => Finsupp.single (RootedTree.ofPTree (PLTree.erase u)) (1 : R))).sum := by
    simpa [List.map_map, Function.comp_def] using
      (finsupp_mapDomain_sum_single (R := R)
        (LRootedTree.erase : LRootedTree α → RootedTree)
        ((PLTree.preLieGrafts s t).map LRootedTree.ofPLTree))
  rw [hmap]
  exact congrArg List.sum <| by
    calc
      List.map
          (fun u => Finsupp.single (RootedTree.ofPTree (PLTree.erase u)) (1 : R))
          (PLTree.preLieGrafts s t) =
          List.map (fun u => Finsupp.single (RootedTree.ofPTree u) (1 : R))
            ((PLTree.preLieGrafts s t).map PLTree.erase) := by
            rw [List.map_map]
            rfl
      _ = List.map (fun u => Finsupp.single (RootedTree.ofPTree u) (1 : R))
            (PTree.preLieGrafts (PLTree.erase s) (PLTree.erase t)) := by
            rw [PLTree.erase_preLieGrafts]

@[simp]
theorem map_preLieVector {β : Type w} (R : Type v) [Semiring R]
    (f : α → β) (s t : LRootedTree α) :
    Finsupp.mapDomain (LRootedTree.map f) (preLieVector R s t) =
      preLieVector R (map f s) (map f t) := by
  refine Quotient.inductionOn₂ s t ?_
  intro s t
  change
    Finsupp.mapDomain (LRootedTree.map f)
        (preLieVector R (LRootedTree.ofPLTree s) (LRootedTree.ofPLTree t)) =
      preLieVector R (LRootedTree.ofPLTree (PLTree.map f s))
        (LRootedTree.ofPLTree (PLTree.map f t))
  rw [preLieVector_ofPLTree, preLieVector_ofPLTree]
  rw [preLieVectorOfPLTree, preLieVectorOfPLTree]
  have hmap :
      Finsupp.mapDomain (LRootedTree.map f)
          (((PLTree.preLieGrafts s t).map
            (fun u => Finsupp.single (LRootedTree.ofPLTree u) (1 : R))).sum) =
        ((PLTree.preLieGrafts s t).map
          (fun u => Finsupp.single (LRootedTree.ofPLTree (PLTree.map f u)) (1 : R))).sum := by
    simpa [List.map_map, Function.comp_def] using
      (finsupp_mapDomain_sum_single (R := R)
        (LRootedTree.map f : LRootedTree α → LRootedTree β)
        ((PLTree.preLieGrafts s t).map LRootedTree.ofPLTree))
  rw [hmap]
  exact congrArg List.sum <| by
    calc
      List.map
          (fun u => Finsupp.single (LRootedTree.ofPLTree (PLTree.map f u)) (1 : R))
          (PLTree.preLieGrafts s t) =
          List.map (fun u => Finsupp.single (LRootedTree.ofPLTree u) (1 : R))
            ((PLTree.preLieGrafts s t).map (PLTree.map f)) := by
            rw [List.map_map]
            rfl
      _ = List.map (fun u => Finsupp.single (LRootedTree.ofPLTree u) (1 : R))
            (PLTree.preLieGrafts (PLTree.map f s) (PLTree.map f t)) := by
            rw [PLTree.map_preLieGrafts]

@[simp]
theorem constLabel_preLieVector (R : Type v) [Semiring R]
    (a : α) (s t : RootedTree) :
    Finsupp.mapDomain (LRootedTree.constLabel a) (RootedTree.preLieVector R s t) =
      preLieVector R (constLabel a s) (constLabel a t) := by
  refine Quotient.inductionOn₂ s t ?_
  intro s t
  change
    Finsupp.mapDomain (LRootedTree.constLabel a)
        (RootedTree.preLieVector R (RootedTree.ofPTree s) (RootedTree.ofPTree t)) =
      preLieVector R (LRootedTree.ofPLTree (PLTree.constLabel a s))
        (LRootedTree.ofPLTree (PLTree.constLabel a t))
  rw [RootedTree.preLieVector_ofPTree, preLieVector_ofPLTree]
  rw [RootedTree.preLieVectorOfPTree, preLieVectorOfPLTree]
  have hmap :
      Finsupp.mapDomain (LRootedTree.constLabel a)
          (((PTree.preLieGrafts s t).map
            (fun u => Finsupp.single (RootedTree.ofPTree u) (1 : R))).sum) =
        ((PTree.preLieGrafts s t).map
          (fun u => Finsupp.single (LRootedTree.ofPLTree (PLTree.constLabel a u))
            (1 : R))).sum := by
    simpa [List.map_map, Function.comp_def] using
      (finsupp_mapDomain_sum_single (R := R)
        (LRootedTree.constLabel a : RootedTree → LRootedTree α)
        ((PTree.preLieGrafts s t).map RootedTree.ofPTree))
  rw [hmap]
  exact congrArg List.sum <| by
    calc
      List.map
          (fun u =>
            Finsupp.single (LRootedTree.ofPLTree (PLTree.constLabel a u)) (1 : R))
          (PTree.preLieGrafts s t) =
          List.map (fun u => Finsupp.single (LRootedTree.ofPLTree u) (1 : R))
            ((PTree.preLieGrafts s t).map (PLTree.constLabel a)) := by
            rw [List.map_map]
            rfl
      _ = List.map (fun u => Finsupp.single (LRootedTree.ofPLTree u) (1 : R))
            (PLTree.preLieGrafts (PLTree.constLabel a s) (PLTree.constLabel a t)) := by
            rw [PLTree.constLabel_preLieGrafts]

theorem preLieVector_apply_eq_zero_of_order_ne (R : Type v) [Semiring R]
    (s t u : LRootedTree α) (h : ¬ order u = order s + order t) :
    preLieVector R s t u = 0 := by
  revert h
  refine Quotient.inductionOn s ?_
  intro s'
  refine Quotient.inductionOn t ?_
  intro t' h
  exact preLieVectorOfPLTree_apply_eq_zero_of_order_ne R s' t' u h

theorem order_of_mem_support_preLieVector (R : Type v) [Semiring R]
    (s t u : LRootedTree α) (hu : u ∈ (preLieVector R s t).support) :
    order u = order s + order t := by
  by_contra h
  exact (Finsupp.mem_support_iff.mp hu)
    (preLieVector_apply_eq_zero_of_order_ne R s t u h)

theorem homogeneousOfOrder_preLieVector (R : Type v) [Semiring R]
    (s t : LRootedTree α) :
    HomogeneousOfOrder (preLieVector R s t) (order s + order t) := by
  intro u hu
  exact order_of_mem_support_preLieVector R s t u hu

theorem supportedUpToOrder_preLieVector (R : Type v) [Semiring R]
    (s t : LRootedTree α) :
    SupportedUpToOrder (preLieVector R s t) (order s + order t) :=
  (homogeneousOfOrder_preLieVector R s t).supportedUpToOrder

/-- Bilinear extension of non-planar labelled pre-Lie grafting to formal tree sums. -/
def preLie (R : Type v) [Semiring R]
    (x y : FreeModule α R) : FreeModule α R :=
  x.sum fun s a =>
    y.sum fun t b =>
      (a * b) • preLieVector R s t

theorem preLie_apply (R : Type v) [Semiring R]
    (x y : FreeModule α R) (u : LRootedTree α) :
    preLie R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * preLieVector R s t u) := by
  simp [preLie]

theorem preLie_apply_eq_zero_of_forall_order_ne (R : Type v) [Semiring R]
    (x y : FreeModule α R) (u : LRootedTree α)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    preLie R x y u = 0 := by
  rw [preLie_apply]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro s hs
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro t ht
  have hvector : preLieVector R s t u = 0 :=
    preLieVector_apply_eq_zero_of_order_ne R s t u (h s hs t ht)
  simp [hvector]

theorem exists_order_eq_of_mem_support_preLie (R : Type v) [Semiring R]
    (x y : FreeModule α R) (u : LRootedTree α) (hu : u ∈ (preLie R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : preLie R x y u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.preLie (R : Type v) [Semiring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.preLie (R : Type v) [Semiring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (preLie R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_preLie R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem preLie_zero_left (R : Type v) [Semiring R] (x : FreeModule α R) :
    preLie R 0 x = 0 := by
  simp [preLie]

@[simp]
theorem preLie_zero_right (R : Type v) [Semiring R] (x : FreeModule α R) :
    preLie R x 0 = 0 := by
  simp [preLie]

theorem preLie_add_left (R : Type v) [Semiring R]
    (x y z : FreeModule α R) :
    preLie R (x + y) z = preLie R x z + preLie R y z := by
  classical
  rw [preLie, preLie, preLie]
  apply Finsupp.sum_add_index
  · intro s hs
    simp
  · intro s hs a b
    simp [add_mul, add_smul, Finsupp.sum_add]

theorem preLie_add_right (R : Type v) [Semiring R]
    (x y z : FreeModule α R) :
    preLie R x (y + z) = preLie R x y + preLie R x z := by
  classical
  rw [preLie, preLie, preLie]
  calc
    x.sum (fun s a => (y + z).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum (fun t b => (a * b) • preLieVector R s t) +
            z.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          apply Finsupp.sum_add_index
          · intro t ht
            simp
          · intro t ht a b
            simp [mul_add, add_smul]
    _ = x.sum (fun s a => y.sum fun t b => (a * b) • preLieVector R s t) +
          x.sum (fun s a => z.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.sum_add]

theorem preLie_smul_left (R : Type v) [Semiring R]
    (c : R) (x y : FreeModule α R) :
    preLie R (c • x) y = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  rw [Finsupp.sum_smul_index]
  · calc
      x.sum (fun s a => y.sum fun t b => ((c * a) * b) • preLieVector R s t) =
          x.sum (fun s a => c •
            y.sum (fun t b => (a * b) • preLieVector R s t)) := by
            apply Finsupp.sum_congr
            intro s hs
            rw [Finsupp.smul_sum]
            apply Finsupp.sum_congr
            intro t ht
            rw [smul_smul]
            rw [mul_assoc]
      _ = c • x.sum (fun s a =>
            y.sum fun t b => (a * b) • preLieVector R s t) := by
            rw [Finsupp.smul_sum]
  · intro s
    simp

theorem preLie_smul_right (R : Type v) [CommSemiring R]
    (c : R) (x y : FreeModule α R) :
    preLie R x (c • y) = c • preLie R x y := by
  classical
  rw [preLie, preLie]
  calc
    x.sum (fun s a => (c • y).sum fun t b => (a * b) • preLieVector R s t) =
        x.sum (fun s a =>
          y.sum fun t b => (a * (c * b)) • preLieVector R s t) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.sum_smul_index]
          · intro t
            simp
    _ = x.sum (fun s a => c •
          y.sum (fun t b => (a * b) • preLieVector R s t)) := by
          apply Finsupp.sum_congr
          intro s hs
          rw [Finsupp.smul_sum]
          apply Finsupp.sum_congr
          intro t ht
          rw [smul_smul]
          congr 1
          rw [← mul_assoc, mul_comm (x s) c, mul_assoc]
    _ = c • x.sum (fun s a =>
          y.sum fun t b => (a * b) • preLieVector R s t) := by
          rw [Finsupp.smul_sum]

theorem preLie_single_single (R : Type v) [Semiring R]
    (s t : LRootedTree α) (a b : R) :
    preLie R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t := by
  rw [preLie]
  rw [Finsupp.sum_single_index (h_zero := by
    rw [Finsupp.sum_single_index (h_zero := by rw [zero_mul, zero_smul])]
    rw [zero_mul, zero_smul])]
  rw [Finsupp.sum_single_index (h_zero := by rw [mul_zero, zero_smul])]

@[simp]
theorem preLie_single_single_one (R : Type v) [Semiring R]
    (s t : LRootedTree α) :
    preLie R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t := by
  rw [preLie_single_single]
  simp

@[simp]
theorem mapDomain_ofPLTree_preLie (R : Type v) [Semiring R]
    (x y : PLTree.FreeModule α R) :
    Finsupp.mapDomain LRootedTree.ofPLTree (PLTree.preLie R x y) =
      preLie R (Finsupp.mapDomain LRootedTree.ofPLTree x)
        (Finsupp.mapDomain LRootedTree.ofPLTree y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [PLTree.preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [preLie_add_left, hx₁, hx₂]
  | single s a =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [PLTree.preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [PLTree.preLie_single_single, Finsupp.mapDomain_smul,
            mapDomain_ofPLTree_preLieVector, Finsupp.mapDomain_single,
            Finsupp.mapDomain_single, preLie_single_single]

@[simp]
theorem erase_preLie (R : Type v) [Semiring R]
    (x y : FreeModule α R) :
    Finsupp.mapDomain LRootedTree.erase (preLie R x y) =
      RootedTree.preLie R (Finsupp.mapDomain LRootedTree.erase x)
        (Finsupp.mapDomain LRootedTree.erase y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [RootedTree.preLie_add_left, hx₁, hx₂]
  | single s a =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [RootedTree.preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [preLie_single_single, Finsupp.mapDomain_smul, erase_preLieVector,
            Finsupp.mapDomain_single, Finsupp.mapDomain_single,
            RootedTree.preLie_single_single]

@[simp]
theorem map_preLie {β : Type w} (R : Type v) [Semiring R]
    (f : α → β) (x y : FreeModule α R) :
    Finsupp.mapDomain (LRootedTree.map f) (preLie R x y) =
      preLie R (Finsupp.mapDomain (LRootedTree.map f) x)
        (Finsupp.mapDomain (LRootedTree.map f) y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [preLie_add_left, hx₁, hx₂]
  | single s a =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [preLie_single_single, Finsupp.mapDomain_smul, map_preLieVector,
            Finsupp.mapDomain_single, Finsupp.mapDomain_single, preLie_single_single]

@[simp]
theorem constLabel_preLie (R : Type v) [Semiring R]
    (a : α) (x y : RootedTree.FreeModule R) :
    Finsupp.mapDomain (LRootedTree.constLabel a) (RootedTree.preLie R x y) =
      preLie R (Finsupp.mapDomain (LRootedTree.constLabel a) x)
        (Finsupp.mapDomain (LRootedTree.constLabel a) y) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero =>
      simp
  | add x₁ x₂ hx₁ hx₂ =>
      rw [RootedTree.preLie_add_left]
      rw [Finsupp.mapDomain_add]
      rw [Finsupp.mapDomain_add]
      rw [preLie_add_left, hx₁, hx₂]
  | single s aₛ =>
      induction y using Finsupp.induction_linear with
      | zero =>
          simp
      | add y₁ y₂ hy₁ hy₂ =>
          rw [RootedTree.preLie_add_right]
          rw [Finsupp.mapDomain_add]
          rw [Finsupp.mapDomain_add]
          rw [preLie_add_right, hy₁, hy₂]
      | single t b =>
          rw [RootedTree.preLie_single_single, Finsupp.mapDomain_smul,
            constLabel_preLieVector, Finsupp.mapDomain_single,
            Finsupp.mapDomain_single, preLie_single_single]

/-- The commutator bracket induced by non-planar labelled pre-Lie grafting. -/
def lieBracket (R : Type v) [Ring R]
    (x y : FreeModule α R) : FreeModule α R :=
  preLie R x y - preLie R y x

theorem lieBracket_apply (R : Type v) [Ring R]
    (x y : FreeModule α R) (u : LRootedTree α) :
    lieBracket R x y u =
      x.sum (fun s a =>
        y.sum fun t b => (a * b) * preLieVector R s t u) -
      y.sum (fun s a =>
        x.sum fun t b => (a * b) * preLieVector R s t u) := by
  simp [lieBracket, preLie_apply]

theorem lieBracket_apply_eq_zero_of_forall_order_ne (R : Type v) [Ring R]
    (x y : FreeModule α R) (u : LRootedTree α)
    (h : ∀ s ∈ x.support, ∀ t ∈ y.support, ¬ order u = order s + order t) :
    lieBracket R x y u = 0 := by
  rw [lieBracket]
  have hxy : preLie R x y u = 0 :=
    preLie_apply_eq_zero_of_forall_order_ne R x y u h
  have hyx : preLie R y x u = 0 := by
    apply preLie_apply_eq_zero_of_forall_order_ne
    intro t ht s hs horder
    exact h s hs t ht (by simpa [Nat.add_comm] using horder)
  simp [hxy, hyx]

theorem exists_order_eq_of_mem_support_lieBracket (R : Type v) [Ring R]
    (x y : FreeModule α R) (u : LRootedTree α) (hu : u ∈ (lieBracket R x y).support) :
    ∃ s ∈ x.support, ∃ t ∈ y.support, order u = order s + order t := by
  by_contra h
  have hzero : lieBracket R x y u = 0 := by
    apply lieBracket_apply_eq_zero_of_forall_order_ne
    intro s hs t ht horder
    exact h ⟨s, hs, t, ht, horder⟩
  exact (Finsupp.mem_support_iff.mp hu) hzero

theorem HomogeneousOfOrder.lieBracket (R : Type v) [Ring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : HomogeneousOfOrder x m) (hy : HomogeneousOfOrder y n) :
    HomogeneousOfOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder, hx s hs, hy t ht]

theorem SupportedUpToOrder.lieBracket (R : Type v) [Ring R]
    {x y : FreeModule α R} {m n : Nat}
    (hx : SupportedUpToOrder x m) (hy : SupportedUpToOrder y n) :
    SupportedUpToOrder (lieBracket R x y) (m + n) := by
  intro u hu
  rcases exists_order_eq_of_mem_support_lieBracket R x y u hu with
    ⟨s, hs, t, ht, horder⟩
  rw [horder]
  exact Nat.add_le_add (hx s hs) (hy t ht)

@[simp]
theorem lieBracket_zero_left (R : Type v) [Ring R] (x : FreeModule α R) :
    lieBracket R 0 x = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_zero_right (R : Type v) [Ring R] (x : FreeModule α R) :
    lieBracket R x 0 = 0 := by
  simp [lieBracket]

@[simp]
theorem lieBracket_self (R : Type v) [Ring R] (x : FreeModule α R) :
    lieBracket R x x = 0 := by
  simp [lieBracket]

theorem lieBracket_skew (R : Type v) [Ring R] (x y : FreeModule α R) :
    lieBracket R x y = -lieBracket R y x := by
  simp [lieBracket, sub_eq_add_neg]

theorem lieBracket_add_left (R : Type v) [Ring R]
    (x y z : FreeModule α R) :
    lieBracket R (x + y) z = lieBracket R x z + lieBracket R y z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_add_right (R : Type v) [Ring R]
    (x y z : FreeModule α R) :
    lieBracket R x (y + z) = lieBracket R x y + lieBracket R x z := by
  rw [lieBracket, lieBracket, lieBracket, preLie_add_left, preLie_add_right]
  abel

theorem lieBracket_smul_left (R : Type v) [CommRing R]
    (c : R) (x y : FreeModule α R) :
    lieBracket R (c • x) y = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_smul_right (R : Type v) [CommRing R]
    (c : R) (x y : FreeModule α R) :
    lieBracket R x (c • y) = c • lieBracket R x y := by
  simp [lieBracket, preLie_smul_left, preLie_smul_right, smul_sub]

theorem lieBracket_single_single (R : Type v) [Ring R]
    (s t : LRootedTree α) (a b : R) :
    lieBracket R (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • preLieVector R s t - (b * a) • preLieVector R t s := by
  simp [lieBracket, preLie_single_single]

@[simp]
theorem lieBracket_single_single_one (R : Type v) [Ring R]
    (s t : LRootedTree α) :
    lieBracket R (Finsupp.single s (1 : R)) (Finsupp.single t (1 : R)) =
      preLieVector R s t - preLieVector R t s := by
  rw [lieBracket_single_single]
  simp

@[simp]
theorem mapDomain_ofPLTree_lieBracket (R : Type v) [Ring R]
    (x y : PLTree.FreeModule α R) :
    Finsupp.mapDomain LRootedTree.ofPLTree (PLTree.lieBracket R x y) =
      lieBracket R (Finsupp.mapDomain LRootedTree.ofPLTree x)
        (Finsupp.mapDomain LRootedTree.ofPLTree y) := by
  rw [PLTree.lieBracket, lieBracket, Finsupp.mapDomain_sub,
    mapDomain_ofPLTree_preLie, mapDomain_ofPLTree_preLie]

@[simp]
theorem erase_lieBracket (R : Type v) [Ring R]
    (x y : FreeModule α R) :
    Finsupp.mapDomain LRootedTree.erase (lieBracket R x y) =
      RootedTree.lieBracket R (Finsupp.mapDomain LRootedTree.erase x)
        (Finsupp.mapDomain LRootedTree.erase y) := by
  rw [lieBracket, RootedTree.lieBracket, Finsupp.mapDomain_sub,
    erase_preLie, erase_preLie]

@[simp]
theorem map_lieBracket {β : Type w} (R : Type v) [Ring R]
    (f : α → β) (x y : FreeModule α R) :
    Finsupp.mapDomain (LRootedTree.map f) (lieBracket R x y) =
      lieBracket R (Finsupp.mapDomain (LRootedTree.map f) x)
        (Finsupp.mapDomain (LRootedTree.map f) y) := by
  rw [lieBracket, lieBracket, Finsupp.mapDomain_sub, map_preLie, map_preLie]

@[simp]
theorem constLabel_lieBracket (R : Type v) [Ring R]
    (a : α) (x y : RootedTree.FreeModule R) :
    Finsupp.mapDomain (LRootedTree.constLabel a) (RootedTree.lieBracket R x y) =
      lieBracket R (Finsupp.mapDomain (LRootedTree.constLabel a) x)
        (Finsupp.mapDomain (LRootedTree.constLabel a) y) := by
  rw [RootedTree.lieBracket, lieBracket, Finsupp.mapDomain_sub,
    constLabel_preLie, constLabel_preLie]

end LRootedTree

end

end BSeries
