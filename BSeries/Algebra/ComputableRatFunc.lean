/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Algebra.ComputablePolynomial
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Tactic.LinearCombination

/-!
# A computable field of rational functions

`CRatFunc K` is the fraction field of the computable polynomial ring
`CPoly K`, realised as a quotient of numerator/denominator pairs by the
cross-multiplication relation. All field operations and equality are
computable, so identities of rational functions in a **generic
parameter** `X` can be verified by `native_decide`.

Sums and products reduce their result by an *unverified* polynomial gcd
whose defining equations are checked by a decidable guard
(`CRatFunc.reducePair`), so the reduction requires no gcd correctness
theory while keeping intermediate degrees small.

This is the engine behind the symbolic verification of the parametric
`EES(2,5;x)` and `EES(2,7;x)` order conditions (arXiv:2507.21006,
Section 8; arXiv:2509.20599, Theorems E.1–E.2): instantiating a family
at `x := X : CRatFunc ℚ` proves its order conditions at the generic
parameter, i.e. as identities of rational functions.
-/

namespace BSeries

universe u

variable {K : Type u} [Field K] [DecidableEq K]

instance : Nontrivial (CPoly K) :=
  ⟨⟨0, 1, fun h => by
    have h2 := congrArg CPoly.toPoly h
    rw [CPoly.toPoly_zero, CPoly.toPoly_one] at h2
    exact zero_ne_one h2⟩⟩

/-- Fraction representatives: a numerator and a nonzero denominator. -/
abbrev PreRatFunc (K : Type u) [Field K] [DecidableEq K] : Type u :=
  CPoly K × {q : CPoly K // q ≠ 0}

/-- The cross-multiplication equivalence on fraction representatives. -/
instance ratFuncSetoid (K : Type u) [Field K] [DecidableEq K] :
    Setoid (PreRatFunc K) where
  r a b := a.1 * b.2.1 = b.1 * a.2.1
  iseqv := by
    refine ⟨fun a => rfl, fun h => h.symm, ?_⟩
    intro a b c hab hbc
    have hb := b.2.2
    apply mul_left_cancel₀ hb
    calc b.2.1 * (a.1 * c.2.1) = (a.1 * b.2.1) * c.2.1 := by ring
      _ = (b.1 * a.2.1) * c.2.1 := by rw [hab]
      _ = (b.1 * c.2.1) * a.2.1 := by ring
      _ = (c.1 * b.2.1) * a.2.1 := by rw [hbc]
      _ = b.2.1 * (c.1 * a.2.1) := by ring

/-- The computable field of rational functions over `K`. -/
@[reducible]
def CRatFunc (K : Type u) [Field K] [DecidableEq K] : Type u :=
  Quotient (ratFuncSetoid K)

namespace CRatFunc

/-- Build a rational function from a raw representative pair. -/
def mk (p : CPoly K) (q : CPoly K) (hq : q ≠ 0) : CRatFunc K :=
  Quotient.mk (ratFuncSetoid K) (p, ⟨q, hq⟩)

theorem mk_eq_mk {p₁ q₁ p₂ q₂ : CPoly K} {h₁ : q₁ ≠ 0} {h₂ : q₂ ≠ 0} :
    mk p₁ q₁ h₁ = mk p₂ q₂ h₂ ↔ p₁ * q₂ = p₂ * q₁ :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

instance : DecidableEq (CRatFunc K) := fun x y =>
  Quotient.recOnSubsingleton₂ x y fun a b =>
    decidable_of_iff (a.1 * b.2.1 = b.1 * a.2.1)
      ⟨fun h => Quotient.sound h, fun h => Quotient.exact h⟩

instance : Zero (CRatFunc K) := ⟨mk 0 1 one_ne_zero⟩
instance : One (CRatFunc K) := ⟨mk 1 1 one_ne_zero⟩

/-! ### Reduction by a runtime-checked gcd -/

/-- Cancel the (unverified) gcd of numerator and denominator; the guard
checks the defining equations of the division, so the result represents
the same fraction with no gcd correctness theory required. -/
def reducePair (a : PreRatFunc K) : PreRatFunc K :=
  if h : CPoly.cDiv a.1 (CPoly.cGcd a.1 a.2.1) * CPoly.cGcd a.1 a.2.1 =
      a.1 ∧
      CPoly.cDiv a.2.1 (CPoly.cGcd a.1 a.2.1) * CPoly.cGcd a.1 a.2.1 =
      a.2.1 then
    (CPoly.cDiv a.1 (CPoly.cGcd a.1 a.2.1),
      ⟨CPoly.cDiv a.2.1 (CPoly.cGcd a.1 a.2.1), fun hz => a.2.2 (by
        rw [← h.2, hz, zero_mul])⟩)
  else a

theorem reducePair_equiv (a : PreRatFunc K) : reducePair a ≈ a := by
  rw [reducePair]
  split
  next h =>
    show CPoly.cDiv a.1 (CPoly.cGcd a.1 a.2.1) * a.2.1 =
      a.1 * CPoly.cDiv a.2.1 (CPoly.cGcd a.1 a.2.1)
    linear_combination CPoly.cDiv a.2.1 (CPoly.cGcd a.1 a.2.1) * h.1 -
      CPoly.cDiv a.1 (CPoly.cGcd a.1 a.2.1) * h.2
  next =>
    show a.1 * a.2.1 = a.1 * a.2.1
    rfl

/-! ### Arithmetic -/

/-- Raw sum of representatives. -/
def addPair (a b : PreRatFunc K) : PreRatFunc K :=
  (a.1 * b.2.1 + b.1 * a.2.1, ⟨a.2.1 * b.2.1, mul_ne_zero a.2.2 b.2.2⟩)

/-- Raw product of representatives. -/
def mulPair (a b : PreRatFunc K) : PreRatFunc K :=
  (a.1 * b.1, ⟨a.2.1 * b.2.1, mul_ne_zero a.2.2 b.2.2⟩)

/-- Raw negation of a representative. -/
def negPair (a : PreRatFunc K) : PreRatFunc K :=
  (-a.1, a.2)

private theorem addPair_wd {a a' b b' : PreRatFunc K}
    (ha : a ≈ a') (hb : b ≈ b') : addPair a b ≈ addPair a' b' := by
  show (a.1 * b.2.1 + b.1 * a.2.1) * (a'.2.1 * b'.2.1) =
    (a'.1 * b'.2.1 + b'.1 * a'.2.1) * (a.2.1 * b.2.1)
  have ha' : a.1 * a'.2.1 = a'.1 * a.2.1 := ha
  have hb' : b.1 * b'.2.1 = b'.1 * b.2.1 := hb
  linear_combination (b.2.1 * b'.2.1) * ha' + (a.2.1 * a'.2.1) * hb'

private theorem mulPair_wd {a a' b b' : PreRatFunc K}
    (ha : a ≈ a') (hb : b ≈ b') : mulPair a b ≈ mulPair a' b' := by
  show (a.1 * b.1) * (a'.2.1 * b'.2.1) = (a'.1 * b'.1) * (a.2.1 * b.2.1)
  have ha' : a.1 * a'.2.1 = a'.1 * a.2.1 := ha
  have hb' : b.1 * b'.2.1 = b'.1 * b.2.1 := hb
  linear_combination (b.1 * b'.2.1) * ha' + (a'.1 * a.2.1) * hb'

private theorem negPair_wd {a a' : PreRatFunc K} (ha : a ≈ a') :
    negPair a ≈ negPair a' := by
  show -a.1 * a'.2.1 = -a'.1 * a.2.1
  have ha' : a.1 * a'.2.1 = a'.1 * a.2.1 := ha
  linear_combination -ha'

instance : Add (CRatFunc K) :=
  ⟨fun x y =>
    Quotient.liftOn₂ x y
      (fun a b => Quotient.mk (ratFuncSetoid K) (reducePair (addPair a b)))
      (fun a b a' b' ha hb =>
        Quotient.sound
          (Setoid.trans (reducePair_equiv (addPair a b))
            (Setoid.trans (addPair_wd ha hb)
              (Setoid.symm (reducePair_equiv (addPair a' b'))))))⟩

instance : Mul (CRatFunc K) :=
  ⟨fun x y =>
    Quotient.liftOn₂ x y
      (fun a b => Quotient.mk (ratFuncSetoid K) (reducePair (mulPair a b)))
      (fun a b a' b' ha hb =>
        Quotient.sound
          (Setoid.trans (reducePair_equiv (mulPair a b))
            (Setoid.trans (mulPair_wd ha hb)
              (Setoid.symm (reducePair_equiv (mulPair a' b'))))))⟩

instance : Neg (CRatFunc K) :=
  ⟨fun x =>
    Quotient.liftOn x
      (fun a => Quotient.mk (ratFuncSetoid K) (negPair a))
      (fun _ _ ha => Quotient.sound (negPair_wd ha))⟩

/-- A fraction is zero iff its numerator is zero. -/
theorem mk_eq_zero {p q : CPoly K} {hq : q ≠ 0} :
    mk p q hq = 0 ↔ p = 0 := by
  rw [show (0 : CRatFunc K) = mk 0 1 one_ne_zero from rfl, mk_eq_mk]
  constructor
  · intro h
    rwa [mul_one, zero_mul] at h
  · intro h
    rw [h, mul_one, zero_mul]

instance : Inv (CRatFunc K) :=
  ⟨fun x =>
    Quotient.liftOn x
      (fun a => if h : a.1 = 0 then (0 : CRatFunc K) else mk a.2.1 a.1 h)
      (by
        intro a a' ha
        have ha' : a.1 * a'.2.1 = a'.1 * a.2.1 := ha
        by_cases h : a.1 = 0
        · have h' : a'.1 = 0 := by
            have h2 : a'.1 * a.2.1 = 0 := by rw [← ha', h, zero_mul]
            rcases mul_eq_zero.1 h2 with h3 | h3
            · exact h3
            · exact absurd h3 a.2.2
          rw [dif_pos h, dif_pos h']
        · have h' : a'.1 ≠ 0 := by
            intro h2
            rw [h2, zero_mul] at ha'
            rcases mul_eq_zero.1 ha' with h3 | h3
            · exact h h3
            · exact absurd h3 a'.2.2
          rw [dif_neg h, dif_neg h']
          refine Quotient.sound ?_
          show a.2.1 * a'.1 = a'.2.1 * a.1
          linear_combination -ha')⟩

theorem inv_mk {p q : CPoly K} (hq : q ≠ 0) (hp : p ≠ 0) :
    (mk p q hq)⁻¹ = mk q p hp := by
  show dite _ _ _ = _
  rw [dif_neg hp]

private theorem add_raw (a b : PreRatFunc K) :
    (Quotient.mk (ratFuncSetoid K) a : CRatFunc K) +
      (Quotient.mk (ratFuncSetoid K) b : CRatFunc K) =
      Quotient.mk (ratFuncSetoid K) (addPair a b) :=
  Quotient.sound (reducePair_equiv (addPair a b))

private theorem mul_raw (a b : PreRatFunc K) :
    (Quotient.mk (ratFuncSetoid K) a : CRatFunc K) *
      (Quotient.mk (ratFuncSetoid K) b : CRatFunc K) =
      Quotient.mk (ratFuncSetoid K) (mulPair a b) :=
  Quotient.sound (reducePair_equiv (mulPair a b))

private theorem neg_raw (a : PreRatFunc K) :
    -(Quotient.mk (ratFuncSetoid K) a : CRatFunc K) =
      Quotient.mk (ratFuncSetoid K) (negPair a) :=
  rfl

/-- The field structure: all axioms are cross-multiplication identities
in the computable polynomial domain `CPoly K`. -/
instance field : Field (CRatFunc K) :=
  Field.ofMinimalAxioms (CRatFunc K)
    (fun x y z => by
      induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
      induction z using Quotient.inductionOn with | _ c =>
      rw [add_raw, add_raw, add_raw, add_raw]
      refine Quotient.sound ?_
      show ((a.1 * b.2.1 + b.1 * a.2.1) * c.2.1 + c.1 * (a.2.1 * b.2.1)) *
          (a.2.1 * (b.2.1 * c.2.1)) =
        (a.1 * (b.2.1 * c.2.1) + (b.1 * c.2.1 + c.1 * b.2.1) * a.2.1) *
          (a.2.1 * b.2.1 * c.2.1)
      ring)
    (fun x => by
      induction x using Quotient.inductionOn with | _ a =>
      rw [show (0 : CRatFunc K) =
        Quotient.mk (ratFuncSetoid K) (0, ⟨1, one_ne_zero⟩) from rfl,
        add_raw]
      refine Quotient.sound ?_
      show (0 * a.2.1 + a.1 * 1) * a.2.1 = a.1 * (1 * a.2.1)
      ring)
    (fun x => by
      induction x using Quotient.inductionOn with | _ a =>
      rw [show (0 : CRatFunc K) =
        Quotient.mk (ratFuncSetoid K) (0, ⟨1, one_ne_zero⟩) from rfl,
        neg_raw, add_raw]
      refine Quotient.sound ?_
      show (-a.1 * a.2.1 + a.1 * a.2.1) * 1 = 0 * (a.2.1 * a.2.1)
      ring)
    (fun x y z => by
      induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
      induction z using Quotient.inductionOn with | _ c =>
      rw [mul_raw, mul_raw, mul_raw, mul_raw]
      refine Quotient.sound ?_
      show (a.1 * b.1 * c.1) * (a.2.1 * (b.2.1 * c.2.1)) =
        (a.1 * (b.1 * c.1)) * (a.2.1 * b.2.1 * c.2.1)
      ring)
    (fun x y => by
      induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
      rw [mul_raw, mul_raw]
      refine Quotient.sound ?_
      show (a.1 * b.1) * (b.2.1 * a.2.1) = (b.1 * a.1) * (a.2.1 * b.2.1)
      ring)
    (fun x => by
      induction x using Quotient.inductionOn with | _ a =>
      rw [show (1 : CRatFunc K) =
        Quotient.mk (ratFuncSetoid K) (1, ⟨1, one_ne_zero⟩) from rfl,
        mul_raw]
      refine Quotient.sound ?_
      show (1 * a.1) * a.2.1 = a.1 * (1 * a.2.1)
      ring)
    (fun x hx => by
      induction x using Quotient.inductionOn with | _ a =>
      have ha : a.1 ≠ 0 := fun h => by
        refine hx ?_
        rw [show (Quotient.mk (ratFuncSetoid K) a : CRatFunc K) =
          mk a.1 a.2.1 a.2.2 from rfl]
        exact mk_eq_zero.2 h
      rw [show (Quotient.mk (ratFuncSetoid K) a : CRatFunc K) =
        mk a.1 a.2.1 a.2.2 from rfl, inv_mk a.2.2 ha, mk, mk, mul_raw,
        show (1 : CRatFunc K) =
          Quotient.mk (ratFuncSetoid K) (1, ⟨1, one_ne_zero⟩) from rfl]
      refine Quotient.sound ?_
      show (a.1 * a.2.1) * 1 = 1 * (a.2.1 * a.1)
      ring)
    (by
      show ((0 : CRatFunc K))⁻¹ = 0
      show (if h : (0 : CPoly K) = 0 then (0 : CRatFunc K)
        else mk (1 : CPoly K) (0 : CPoly K) h) = 0
      rw [dif_pos rfl])
    (fun x y z => by
      induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
      induction z using Quotient.inductionOn with | _ c =>
      rw [add_raw, mul_raw, mul_raw, mul_raw, add_raw]
      refine Quotient.sound ?_
      show (a.1 * (b.1 * c.2.1 + c.1 * b.2.1)) *
          (a.2.1 * b.2.1 * (a.2.1 * c.2.1)) =
        (a.1 * b.1 * (a.2.1 * c.2.1) + a.1 * c.1 * (a.2.1 * b.2.1)) *
          (a.2.1 * (b.2.1 * c.2.1))
      ring)
    ⟨0, 1, by
      intro h
      have h2 := mk_eq_mk.1 h
      rw [zero_mul, one_mul] at h2
      exact zero_ne_one h2⟩

/-- The generic parameter. -/
def X : CRatFunc K := mk CPoly.X 1 one_ne_zero

/-- Embed a constant. -/
def C (c : K) : CRatFunc K := mk (CPoly.C c) 1 one_ne_zero

/-- The embedding of polynomials, as a ring homomorphism. -/
def ofPoly : CPoly K →+* CRatFunc K where
  toFun p := mk p 1 one_ne_zero
  map_one' := rfl
  map_mul' p q := by
    rw [show (mk p 1 one_ne_zero : CRatFunc K) * mk q 1 one_ne_zero =
      Quotient.mk (ratFuncSetoid K)
        (mulPair (p, ⟨1, one_ne_zero⟩) (q, ⟨1, one_ne_zero⟩)) from
      mul_raw _ _]
    refine Quotient.sound ?_
    show (p * q) * (1 * 1) = (p * q) * 1
    ring
  map_zero' := rfl
  map_add' p q := by
    rw [show (mk p 1 one_ne_zero : CRatFunc K) + mk q 1 one_ne_zero =
      Quotient.mk (ratFuncSetoid K)
        (addPair (p, ⟨1, one_ne_zero⟩) (q, ⟨1, one_ne_zero⟩)) from
      add_raw _ _]
    refine Quotient.sound ?_
    show (p + q) * (1 * 1) = (p * 1 + q * 1) * 1
    ring

theorem ofPoly_injective : Function.Injective (ofPoly (K := K)) := by
  intro p q h
  have h2 : p * 1 = q * 1 := mk_eq_mk.1 h
  rwa [mul_one, mul_one] at h2

instance [CharZero K] : CharZero (CPoly K) :=
  ⟨fun m n h => by
    have h2 := congrArg CPoly.toPoly h
    rw [show CPoly.toPoly ((m : ℕ) : CPoly K) = ((m : ℕ) : Polynomial K)
        from map_natCast CPoly.toPolyHom m,
      show CPoly.toPoly ((n : ℕ) : CPoly K) = ((n : ℕ) : Polynomial K)
        from map_natCast CPoly.toPolyHom n] at h2
    exact Nat.cast_injective h2⟩

instance [CharZero K] : CharZero (CRatFunc K) :=
  ⟨fun m n h => by
    have h2 : (ofPoly (m : CPoly K) : CRatFunc K) = ofPoly (n : CPoly K) := by
      rw [map_natCast ofPoly, map_natCast ofPoly]
      exact h
    exact Nat.cast_injective (ofPoly_injective h2)⟩

instance [CharZero K] : Invertible (2 : CRatFunc K) :=
  invertibleOfNonzero (by
    have h : ((2 : ℕ) : CRatFunc K) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)
    exact_mod_cast h)

end CRatFunc

end BSeries
