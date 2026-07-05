/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Field.MinimalAxioms

/-!
# A computable model of ℚ(√2)

The quadratic field `ℚ(√2)` as pairs `(a, b) ↔ a + b√2`, with fully
computable field operations and decidable equality, so that order
conditions of Runge–Kutta schemes with `√2` in their coefficients (the
`EES(2,7;x)` family of arXiv:2507.21006, Section 8) can be
machine-checked by `native_decide`.
-/

namespace BSeries

/-- The quadratic field `ℚ(√2)` as pairs `(a, b) ↔ a + b√2`. -/
@[ext]
structure Qsqrt2 where
  a : ℚ
  b : ℚ
deriving DecidableEq

namespace Qsqrt2

instance : Zero Qsqrt2 := ⟨⟨0, 0⟩⟩
instance : One Qsqrt2 := ⟨⟨1, 0⟩⟩
instance : Add Qsqrt2 := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg Qsqrt2 := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Mul Qsqrt2 :=
  ⟨fun x y => ⟨x.a * y.a + 2 * x.b * y.b, x.a * y.b + x.b * y.a⟩⟩
instance : Inv Qsqrt2 :=
  ⟨fun x => ⟨x.a / (x.a ^ 2 - 2 * x.b ^ 2),
    -x.b / (x.a ^ 2 - 2 * x.b ^ 2)⟩⟩

@[simp] theorem zero_a : (0 : Qsqrt2).a = 0 := rfl
@[simp] theorem zero_b : (0 : Qsqrt2).b = 0 := rfl
@[simp] theorem one_a : (1 : Qsqrt2).a = 1 := rfl
@[simp] theorem one_b : (1 : Qsqrt2).b = 0 := rfl
@[simp] theorem add_a (x y : Qsqrt2) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Qsqrt2) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : Qsqrt2) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : Qsqrt2) : (-x).b = -x.b := rfl
@[simp] theorem mul_a (x y : Qsqrt2) :
    (x * y).a = x.a * y.a + 2 * x.b * y.b := rfl
@[simp] theorem mul_b (x y : Qsqrt2) :
    (x * y).b = x.a * y.b + x.b * y.a := rfl
@[simp] theorem inv_a (x : Qsqrt2) :
    x⁻¹.a = x.a / (x.a ^ 2 - 2 * x.b ^ 2) := rfl
@[simp] theorem inv_b (x : Qsqrt2) :
    x⁻¹.b = -x.b / (x.a ^ 2 - 2 * x.b ^ 2) := rfl

/-- No rational square root of two. -/
theorem sq_ne_two (q : ℚ) : q ^ 2 ≠ 2 := by
  intro h
  have h1 : ((q : ℝ)) ^ 2 = 2 := by exact_mod_cast h
  have h2 : Real.sqrt 2 = |(q : ℝ)| := by
    rw [← h1, Real.sqrt_sq_eq_abs]
  refine irrational_sqrt_two ⟨|q|, ?_⟩
  rw [h2]
  push_cast
  rfl

/-- The field norm `a² - 2b²` vanishes only at zero. -/
theorem norm_ne_zero {x : Qsqrt2} (hx : x ≠ 0) :
    x.a ^ 2 - 2 * x.b ^ 2 ≠ 0 := by
  intro h
  by_cases hb : x.b = 0
  · have ha : x.a = 0 := by
      have : x.a ^ 2 = 0 := by rw [hb] at h; linarith [sq_nonneg x.a]
      exact pow_eq_zero_iff (by norm_num) |>.1 this
    exact hx (Qsqrt2.ext ha hb)
  · refine sq_ne_two (x.a / x.b) ?_
    field_simp
    linarith

instance field : Field Qsqrt2 :=
  Field.ofMinimalAxioms Qsqrt2
    (fun x y z => by ext <;> simp <;> ring)
    (fun x => by ext <;> simp)
    (fun x => by ext <;> simp)
    (fun x y z => by ext <;> simp <;> ring)
    (fun x y => by ext <;> simp <;> ring)
    (fun x => by ext <;> simp)
    (fun x hx => by
      have hN := norm_ne_zero hx
      ext <;> simp <;> field_simp <;> ring)
    (by ext <;> simp)
    (fun x y z => by ext <;> simp <;> ring)
    ⟨0, 1, by
      intro h
      have := congrArg Qsqrt2.a h
      simp at this⟩

theorem natCast_def : ∀ n : ℕ, (n : Qsqrt2) = ⟨(n : ℚ), 0⟩
  | 0 => rfl
  | n + 1 => by
      have h : ((n + 1 : ℕ) : Qsqrt2) = ((n : ℕ) : Qsqrt2) + 1 :=
        Nat.cast_succ n
      rw [h, natCast_def n]
      ext <;> push_cast <;> simp

instance : CharZero Qsqrt2 := by
  refine ⟨fun m n h => ?_⟩
  rw [natCast_def, natCast_def] at h
  have h2 := congrArg Qsqrt2.a h
  simp only at h2
  exact_mod_cast h2

instance : Invertible (2 : Qsqrt2) := by
  refine invertibleOfNonzero ?_
  intro h
  have h2 : ((2 : ℕ) : Qsqrt2) = 0 := by exact_mod_cast h
  rw [natCast_def] at h2
  have := congrArg Qsqrt2.a h2
  norm_num at this

/-- The square root of two. -/
def sqrt2 : Qsqrt2 := ⟨0, 1⟩

@[simp]
theorem sqrt2_mul_self : sqrt2 * sqrt2 = 2 := by
  have h : (2 : Qsqrt2) = ⟨(2 : ℚ), 0⟩ := by exact_mod_cast natCast_def 2
  rw [h]
  ext <;> simp [sqrt2]

end Qsqrt2

end BSeries
