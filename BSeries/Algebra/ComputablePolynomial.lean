/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Computable polynomials

Mathlib's `Polynomial` is noncomputable (it is `Finsupp`-based), which
rules out `native_decide` verification of identities in polynomial or
rational-function coefficients. This file provides `CPoly K`, a computable
polynomial ring over a `DecidableEq` commutative ring, as trimmed
coefficient lists (little-endian, no trailing zeros).

The ring axioms are not proven from scratch: the coefficient-list
operations are transported along the injective evaluation
`CPoly.toPoly : CPoly K → Polynomial K` via `Function.Injective.commRing`.

The intended use is the generic-parameter verification of order
conditions for the parametric `EES(2,5;x)` family: with a computable
fraction field of `CPoly ℚ` the symbolic identities of
arXiv:2509.20599, Theorem E.1, become `native_decide` checks.
-/

namespace BSeries

universe u

variable {K : Type u} [CommRing K] [DecidableEq K]

/-- Trailing-zero-free little-endian coefficient lists. -/
def CPoly (K : Type u) [Zero K] [DecidableEq K] : Type u :=
  {l : List K // l.getLast? ≠ some 0}

namespace CPoly

/-- Remove trailing zeros. -/
def trim {L : Type u} [Zero L] [DecidableEq L] (l : List L) : List L :=
  (l.reverse.dropWhile (· == 0)).reverse

theorem getLast?_trim {K : Type u} [Zero K] [DecidableEq K] (l : List K) :
    (trim l).getLast? ≠ some (0 : K) := by
  rw [trim, List.getLast?_reverse]
  intro h
  have h1 := List.head?_dropWhile_not (fun x : K => x == 0) l.reverse
  rw [h] at h1
  simp at h1

/-! ### Raw coefficient-list operations -/

/-- Pointwise addition (little-endian, ragged). -/
def rawAdd : List K → List K → List K
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: rawAdd l m

/-- Negation. -/
def rawNeg (l : List K) : List K :=
  l.map Neg.neg

/-- Convolution product. -/
def rawMul : List K → List K → List K
  | [], _ => []
  | a :: l, m => rawAdd (m.map (a * ·)) (0 :: rawMul l m)

/-- Interpret a coefficient list as a polynomial. -/
noncomputable def toPolyList : List K → Polynomial K
  | [] => 0
  | a :: l => Polynomial.C a + Polynomial.X * toPolyList l

omit [DecidableEq K] in
@[simp]
theorem toPolyList_nil : toPolyList ([] : List K) = 0 :=
  rfl

omit [DecidableEq K] in
@[simp]
theorem toPolyList_cons (a : K) (l : List K) :
    toPolyList (a :: l) = Polynomial.C a + Polynomial.X * toPolyList l :=
  rfl

omit [DecidableEq K] in
theorem toPolyList_rawAdd :
    ∀ l m : List K, toPolyList (rawAdd l m) = toPolyList l + toPolyList m
  | [], m => by rw [rawAdd, toPolyList_nil, zero_add]
  | a :: l, [] => by rw [rawAdd, toPolyList_nil, add_zero]
  | a :: l, b :: m => by
      rw [rawAdd, toPolyList_cons, toPolyList_cons, toPolyList_cons,
        toPolyList_rawAdd l m, map_add, mul_add]
      ring

omit [DecidableEq K] in
theorem toPolyList_rawNeg :
    ∀ l : List K, toPolyList (rawNeg l) = -toPolyList l
  | [] => by rw [rawNeg, List.map_nil, toPolyList_nil, neg_zero]
  | a :: l => by
      rw [rawNeg, List.map_cons, toPolyList_cons, ← rawNeg,
        toPolyList_rawNeg l, toPolyList_cons, map_neg]
      ring

omit [DecidableEq K] in
theorem toPolyList_map_mul (c : K) :
    ∀ l : List K,
      toPolyList (l.map (c * ·)) = Polynomial.C c * toPolyList l
  | [] => by rw [List.map_nil, toPolyList_nil, mul_zero]
  | a :: l => by
      rw [List.map_cons, toPolyList_cons, toPolyList_cons,
        toPolyList_map_mul c l, map_mul]
      ring

omit [DecidableEq K] in
theorem toPolyList_rawMul :
    ∀ l m : List K, toPolyList (rawMul l m) = toPolyList l * toPolyList m
  | [], m => by rw [rawMul, toPolyList_nil, zero_mul]
  | a :: l, m => by
      rw [rawMul, toPolyList_rawAdd, toPolyList_map_mul, toPolyList_cons,
        toPolyList_rawMul l m, toPolyList_cons, map_zero]
      ring

omit [DecidableEq K] in
theorem toPolyList_append_zero :
    ∀ l : List K, toPolyList (l ++ [0]) = toPolyList l
  | [] => by
      rw [List.nil_append, toPolyList_cons, toPolyList_nil, map_zero,
        mul_zero, add_zero]
  | a :: l => by
      rw [List.cons_append, toPolyList_cons, toPolyList_cons,
        toPolyList_append_zero l]

omit [DecidableEq K] in
private theorem coeff_zero_aux (a : K) (p : Polynomial K) :
    (Polynomial.C a + Polynomial.X * p).coeff 0 = a := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, add_zero]

omit [DecidableEq K] in
private theorem coeff_succ_aux (a : K) (p : Polynomial K) (n : ℕ) :
    (Polynomial.C a + Polynomial.X * p).coeff (n + 1) = p.coeff n := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C,
    if_neg (Nat.succ_ne_zero n), Polynomial.coeff_X_mul, zero_add]

/-- Interpret a trimmed coefficient list as a polynomial. -/
noncomputable def toPoly (p : CPoly K) : Polynomial K :=
  toPolyList p.1

theorem toPolyList_trim (l : List K) :
    toPolyList (trim l) = toPolyList l := by
  rw [trim]
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
      rw [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.nil_append,
        List.dropWhile_cons]
      by_cases ha : a = 0
      · rw [if_pos (by simp [ha]), ha, toPolyList_append_zero]
        exact ih
      · rw [if_neg (by simp [ha]), List.reverse_cons, List.reverse_reverse]

omit [DecidableEq K] in
private theorem toPolyList_injective_trimmed :
    ∀ (l m : List K), l.getLast? ≠ some 0 → m.getLast? ≠ some 0 →
      toPolyList l = toPolyList m → l = m
  | [], [], _, _, _ => rfl
  | [], b :: m, _, hm, h => by
      exfalso
      rw [toPolyList_nil, toPolyList_cons] at h
      have hb : b = 0 := by
        have h0 := congrArg (fun p => Polynomial.coeff p 0) h.symm
        rw [coeff_zero_aux] at h0
        simpa using h0
      have hm2 : toPolyList m = 0 := by
        refine Polynomial.ext fun n => ?_
        have h3 := congrArg (fun p => Polynomial.coeff p (n + 1)) h.symm
        rw [coeff_succ_aux] at h3
        simpa using h3
      have hnil : m = [] := by
        refine toPolyList_injective_trimmed m [] ?_ (by simp)
          (by rw [hm2, toPolyList_nil])
        intro hc
        rcases List.getLast?_eq_some_iff.1 hc with ⟨m2, rfl⟩
        rw [← List.cons_append, List.getLast?_concat] at hm
        exact hm rfl
      subst hnil
      rw [List.getLast?_singleton] at hm
      exact hm (by rw [hb])
  | a :: l, [], hl, _, h => by
      exfalso
      rw [toPolyList_nil, toPolyList_cons] at h
      have ha : a = 0 := by
        have h0 := congrArg (fun p => Polynomial.coeff p 0) h
        rw [coeff_zero_aux] at h0
        simpa using h0
      have hl3 : toPolyList l = 0 := by
        refine Polynomial.ext fun n => ?_
        have h3 := congrArg (fun p => Polynomial.coeff p (n + 1)) h
        rw [coeff_succ_aux] at h3
        simpa using h3
      have hnil : l = [] := by
        refine toPolyList_injective_trimmed l [] ?_ (by simp)
          (by rw [hl3, toPolyList_nil])
        intro hc
        rcases List.getLast?_eq_some_iff.1 hc with ⟨l2, rfl⟩
        rw [← List.cons_append, List.getLast?_concat] at hl
        exact hl rfl
      subst hnil
      rw [List.getLast?_singleton] at hl
      exact hl (by rw [ha])
  | a :: l, b :: m, hl, hm, h => by
      rw [toPolyList_cons, toPolyList_cons] at h
      have hab : a = b := by
        have h0 := congrArg (fun p => Polynomial.coeff p 0) h
        rw [coeff_zero_aux, coeff_zero_aux] at h0
        exact h0
      have hlm : toPolyList l = toPolyList m := by
        refine Polynomial.ext fun n => ?_
        have h3 := congrArg (fun p => Polynomial.coeff p (n + 1)) h
        rw [coeff_succ_aux, coeff_succ_aux] at h3
        exact h3
      have hl2 : l.getLast? ≠ some 0 := by
        cases l with
        | nil => simp
        | cons c l2 => rwa [List.getLast?_cons_cons] at hl
      have hm2 : m.getLast? ≠ some 0 := by
        cases m with
        | nil => simp
        | cons c m2 => rwa [List.getLast?_cons_cons] at hm
      rw [hab, toPolyList_injective_trimmed l m hl2 hm2 hlm]
  termination_by l m => l.length + m.length
  decreasing_by
    all_goals
      simp only [List.length_cons, List.length_nil]
      omega

theorem toPoly_injective : Function.Injective (toPoly (K := K)) :=
  fun p q h => Subtype.ext (toPolyList_injective_trimmed _ _ p.2 q.2 h)

/-! ### Ring structure by injective transfer -/

/-- Constant polynomials. -/
def C (c : K) : CPoly K := ⟨trim [c], getLast?_trim _⟩

theorem toPoly_C (c : K) : toPoly (C c) = Polynomial.C c := by
  show toPolyList (trim [c]) = _
  rw [toPolyList_trim, toPolyList_cons, toPolyList_nil, mul_zero, add_zero]

instance : Zero (CPoly K) := ⟨⟨[], by simp⟩⟩
instance : One (CPoly K) := ⟨C 1⟩
instance : Add (CPoly K) :=
  ⟨fun p q => ⟨trim (rawAdd p.1 q.1), getLast?_trim _⟩⟩
instance : Mul (CPoly K) :=
  ⟨fun p q => ⟨trim (rawMul p.1 q.1), getLast?_trim _⟩⟩
instance : Neg (CPoly K) :=
  ⟨fun p => ⟨trim (rawNeg p.1), getLast?_trim _⟩⟩

instance : DecidableEq (CPoly K) := fun p q =>
  decidable_of_iff (p.1 = q.1) Subtype.ext_iff.symm

theorem toPoly_zero : toPoly (0 : CPoly K) = 0 :=
  rfl

theorem toPoly_one : toPoly (1 : CPoly K) = 1 := by
  rw [show (1 : CPoly K) = C 1 from rfl, toPoly_C, map_one]

theorem toPoly_add (p q : CPoly K) :
    toPoly (p + q) = toPoly p + toPoly q := by
  show toPolyList (trim (rawAdd p.1 q.1)) = _
  rw [toPolyList_trim, toPolyList_rawAdd]
  rfl

theorem toPoly_mul (p q : CPoly K) :
    toPoly (p * q) = toPoly p * toPoly q := by
  show toPolyList (trim (rawMul p.1 q.1)) = _
  rw [toPolyList_trim, toPolyList_rawMul]
  rfl

theorem toPoly_neg (p : CPoly K) : toPoly (-p) = -toPoly p := by
  show toPolyList (trim (rawNeg p.1)) = _
  rw [toPolyList_trim, toPolyList_rawNeg]
  rfl

/-- The commutative ring structure: axioms transported from
`Polynomial K` through the injection, data fully computable. -/
instance : CommRing (CPoly K) :=
  CommRing.ofMinimalAxioms
    (fun a b c => toPoly_injective (by
      rw [toPoly_add, toPoly_add, toPoly_add, toPoly_add, add_assoc]))
    (fun a => toPoly_injective (by
      rw [toPoly_add, toPoly_zero, zero_add]))
    (fun a => toPoly_injective (by
      rw [toPoly_add, toPoly_neg, toPoly_zero, neg_add_cancel]))
    (fun a b c => toPoly_injective (by
      rw [toPoly_mul, toPoly_mul, toPoly_mul, toPoly_mul, mul_assoc]))
    (fun a b => toPoly_injective (by
      rw [toPoly_mul, toPoly_mul, mul_comm]))
    (fun a => toPoly_injective (by
      rw [toPoly_mul, toPoly_one, one_mul]))
    (fun a b c => toPoly_injective (by
      rw [toPoly_mul, toPoly_add, toPoly_add, toPoly_mul, toPoly_mul,
        mul_add]))

/-- `toPoly` as a ring homomorphism. -/
noncomputable def toPolyHom : CPoly K →+* Polynomial K where
  toFun := toPoly
  map_one' := toPoly_one
  map_mul' := toPoly_mul
  map_zero' := toPoly_zero
  map_add' := toPoly_add

/-- The polynomial variable. -/
def X : CPoly K := ⟨trim [0, 1], getLast?_trim _⟩

theorem toPoly_X : toPoly (X : CPoly K) = Polynomial.X := by
  show toPolyList (trim [0, 1]) = _
  rw [toPolyList_trim, toPolyList_cons, toPolyList_cons, toPolyList_nil,
    mul_zero, add_zero, map_zero, map_one, zero_add, mul_one]

/-- No zero divisors, transported along the injection. -/
instance [IsDomain K] : IsDomain (CPoly K) :=
  Function.Injective.isDomain toPolyHom toPoly_injective

/-! ### Unverified division and gcd

Polynomial long division and the Euclidean algorithm, for use as
*runtime-checked reductions*: callers verify the defining equations by a
decidable guard, so no correctness theory is needed here. -/

section DivGcd

variable {L : Type u} [Field L] [DecidableEq L]

/-- One pass of polynomial long division (fuelled; little-endian). -/
def rawDivModAux (q : List L) : ℕ → List L → List L × List L
  | 0, r => ([], r)
  | fuel + 1, r =>
      let r' := trim r
      if r'.length < q.length ∨ q.length = 0 then ([], r')
      else
        let c := (r'.getLast?.getD 0) / (q.getLast?.getD 0)
        let shift := r'.length - q.length
        let sub := rawAdd r' (rawNeg (List.replicate shift 0 ++
          q.map (c * ·)))
        let dr := rawDivModAux q fuel (trim sub)
        (rawAdd (List.replicate shift 0 ++ [c]) dr.1, dr.2)

/-- Quotient and remainder of polynomial division (unverified). -/
def rawDivMod (p q : List L) : List L × List L :=
  rawDivModAux (trim q) (p.length + 1) p

/-- Euclidean gcd, normalised to be monic (unverified). -/
def rawGcd : ℕ → List L → List L → List L
  | 0, p, _ => trim p
  | fuel + 1, p, q =>
      let q' := trim q
      if q'.isEmpty then
        let p' := trim p
        p'.map ((p'.getLast?.getD 1)⁻¹ * ·)
      else rawGcd fuel q' (rawDivMod (trim p) q').2

/-- Monic gcd of two computable polynomials (unverified). -/
def cGcd (p q : CPoly L) : CPoly L :=
  ⟨trim (rawGcd (p.1.length + q.1.length + 2) p.1 q.1), getLast?_trim _⟩

/-- Quotient of polynomial division (unverified). -/
def cDiv (p q : CPoly L) : CPoly L :=
  ⟨trim (rawDivMod p.1 q.1).1, getLast?_trim _⟩

end DivGcd

end CPoly

end BSeries
