/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.LabelledConvolution

/-!
# Butcher Group Operations

This file exposes the convolution monoids on unit-constant B-series and
labelled B-series through named `UnitSeries` aliases.
-/

namespace BSeries

open HopfAlgebras

universe u v

namespace Series

/-- Unit-constant B-series, the coefficient families underlying the Butcher group. -/
abbrev UnitSeries (R : Type u) [One R] : Type u :=
  {a : Series R // HasUnitConstant a}

namespace UnitSeries

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- The unit-constant B-series determined by a forest-algebra character. -/
def ofCharacter (χ : ForestAlgebra.Character R) : UnitSeries R :=
  (Series.characterEquiv (R := R)).symm χ

/-- The forest-algebra character determined by a unit-constant B-series. -/
def toCharacter (a : UnitSeries R) : ForestAlgebra.Character R :=
  Series.characterEquiv a

/-- The identity unit-constant B-series. -/
def one (R : Type u) [CommSemiring R] : UnitSeries R :=
  1

/-- Convolution product of unit-constant B-series. -/
def mul (a b : UnitSeries R) : UnitSeries R :=
  a * b

/-- Unit-constant B-series are multiplicatively equivalent to characters. -/
def characterMulEquiv : UnitSeries R ≃* ForestAlgebra.Character R :=
  Series.characterMulEquiv

@[simp]
theorem val_ofCharacter (χ : ForestAlgebra.Character R) :
    (ofCharacter χ).1 = Series.ofCharacter χ :=
  rfl

@[simp]
theorem toCharacter_ofCharacter (χ : ForestAlgebra.Character R) :
    toCharacter (ofCharacter χ) = χ :=
  (Series.characterEquiv (R := R)).apply_symm_apply χ

@[simp]
theorem ofCharacter_toCharacter (a : UnitSeries R) :
    ofCharacter (toCharacter a) = a :=
  (Series.characterEquiv (R := R)).symm_apply_apply a

@[simp]
theorem one_eq_one :
    one R = (1 : UnitSeries R) :=
  rfl

@[simp]
theorem mul_eq_mul (a b : UnitSeries R) :
    mul a b = a * b :=
  rfl

@[simp]
theorem val_one :
    ((1 : UnitSeries R) : Series R) = Series.unit R :=
  rfl

@[simp]
theorem val_mul (a b : UnitSeries R) :
    ((a * b : UnitSeries R) : Series R) = Series.convolution a.1 b.1 :=
  rfl

@[simp]
theorem toCharacter_one :
    toCharacter (1 : UnitSeries R) = ForestAlgebra.Character.unit R := by
  change Series.characterEquiv (1 : UnitSeries R) = ForestAlgebra.Character.unit R
  exact Series.characterEquiv_unit (R := R)

@[simp]
theorem toCharacter_mul (a b : UnitSeries R) :
    toCharacter (a * b) =
      ForestAlgebra.Character.convolution (toCharacter a) (toCharacter b) := by
  simp [toCharacter]

theorem toCharacter_injective :
    Function.Injective (toCharacter : UnitSeries R → ForestAlgebra.Character R) := by
  intro a b h
  exact (Series.characterEquiv (R := R)).injective h

theorem ext_toCharacter {a b : UnitSeries R} (h : toCharacter a = toCharacter b) :
    a = b :=
  toCharacter_injective h

end

noncomputable section

variable {R : Type u} [CommRing R]

/-- The antipode-composed linear functional inverse associated to a unit-constant B-series. -/
def inverseLinearFunctional (a : UnitSeries R) :
    ForestAlgebra.LinearFunctional R :=
  ForestAlgebra.Character.inverseLinearFunctional (toCharacter a)

theorem convolution_inverseLinearFunctional_left (a : UnitSeries R) :
    ForestAlgebra.LinearFunctional.convolution (inverseLinearFunctional a)
        (ForestAlgebra.LinearFunctional.ofCharacter (toCharacter a)) =
      ForestAlgebra.LinearFunctional.counit R :=
  ForestAlgebra.Character.convolution_inverseLinearFunctional_left (toCharacter a)

theorem convolution_inverseLinearFunctional_right (a : UnitSeries R) :
    ForestAlgebra.LinearFunctional.convolution
        (ForestAlgebra.LinearFunctional.ofCharacter (toCharacter a))
        (inverseLinearFunctional a) =
      ForestAlgebra.LinearFunctional.counit R :=
  ForestAlgebra.Character.convolution_inverseLinearFunctional_right (toCharacter a)

theorem mul_left_cancel {a b c : UnitSeries R}
    (h : a * b = a * c) : b = c := by
  apply ext_toCharacter
  have hχ := congrArg (toCharacter (R := R)) h
  rw [toCharacter_mul, toCharacter_mul] at hχ
  exact ForestAlgebra.Character.convolution_left_cancel hχ

theorem mul_right_cancel {a b c : UnitSeries R}
    (h : b * a = c * a) : b = c := by
  apply ext_toCharacter
  have hχ := congrArg (toCharacter (R := R)) h
  rw [toCharacter_mul, toCharacter_mul] at hχ
  exact ForestAlgebra.Character.convolution_right_cancel hχ

theorem mul_left_cancel_iff (a b c : UnitSeries R) :
    a * b = a * c ↔ b = c := by
  constructor
  · exact mul_left_cancel
  · intro h
    rw [h]

theorem mul_right_cancel_iff (a b c : UnitSeries R) :
    b * a = c * a ↔ b = c := by
  constructor
  · exact mul_right_cancel
  · intro h
    rw [h]

end

end UnitSeries

end Series

namespace LSeries

/-- Unit-constant labelled B-series. -/
abbrev UnitSeries (α : Type u) (R : Type v) [One R] : Type (max u v) :=
  {a : LSeries α R // HasUnitConstant a}

namespace UnitSeries

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- The unit-constant labelled B-series determined by a labelled forest character. -/
def ofCharacter (χ : LForestAlgebra.Character α R) : UnitSeries α R :=
  (LSeries.characterEquiv (α := α) (R := R)).symm χ

/-- The labelled forest character determined by a unit-constant labelled B-series. -/
def toCharacter (a : UnitSeries α R) : LForestAlgebra.Character α R :=
  LSeries.characterEquiv a

/-- The identity unit-constant labelled B-series. -/
def one (α : Type u) (R : Type v) [CommSemiring R] : UnitSeries α R :=
  1

/-- Convolution product of unit-constant labelled B-series. -/
def mul (a b : UnitSeries α R) : UnitSeries α R :=
  a * b

/-- Unit-constant labelled B-series are multiplicatively equivalent to characters. -/
def characterMulEquiv : UnitSeries α R ≃* LForestAlgebra.Character α R :=
  LSeries.characterMulEquiv

@[simp]
theorem val_ofCharacter (χ : LForestAlgebra.Character α R) :
    (ofCharacter χ).1 = LSeries.ofCharacter χ :=
  rfl

@[simp]
theorem toCharacter_ofCharacter (χ : LForestAlgebra.Character α R) :
    toCharacter (ofCharacter χ) = χ :=
  (LSeries.characterEquiv (α := α) (R := R)).apply_symm_apply χ

@[simp]
theorem ofCharacter_toCharacter (a : UnitSeries α R) :
    ofCharacter (toCharacter a) = a :=
  (LSeries.characterEquiv (α := α) (R := R)).symm_apply_apply a

@[simp]
theorem one_eq_one :
    one α R = (1 : UnitSeries α R) :=
  rfl

@[simp]
theorem mul_eq_mul (a b : UnitSeries α R) :
    mul a b = a * b :=
  rfl

@[simp]
theorem val_one :
    ((1 : UnitSeries α R) : LSeries α R) = LSeries.unit α R :=
  rfl

@[simp]
theorem val_mul (a b : UnitSeries α R) :
    ((a * b : UnitSeries α R) : LSeries α R) = LSeries.convolution a.1 b.1 :=
  rfl

@[simp]
theorem toCharacter_one :
    toCharacter (1 : UnitSeries α R) = LForestAlgebra.Character.unit α R := by
  change LSeries.characterEquiv (1 : UnitSeries α R) = LForestAlgebra.Character.unit α R
  exact LSeries.characterEquiv_unit (α := α) (R := R)

@[simp]
theorem toCharacter_mul (a b : UnitSeries α R) :
    toCharacter (a * b) =
      LForestAlgebra.Character.convolution (toCharacter a) (toCharacter b) := by
  simp [toCharacter]

theorem toCharacter_injective :
    Function.Injective (toCharacter : UnitSeries α R → LForestAlgebra.Character α R) := by
  intro a b h
  exact (LSeries.characterEquiv (α := α) (R := R)).injective h

theorem ext_toCharacter {a b : UnitSeries α R} (h : toCharacter a = toCharacter b) :
    a = b :=
  toCharacter_injective h

end

noncomputable section

variable {α : Type u} {R : Type v} [CommRing R]

/-- The antipode-composed linear functional inverse associated to a unit-constant labelled B-series. -/
def inverseLinearFunctional (a : UnitSeries α R) :
    LForestAlgebra.LinearFunctional α R :=
  LForestAlgebra.Character.inverseLinearFunctional (toCharacter a)

theorem convolution_inverseLinearFunctional_left (a : UnitSeries α R) :
    LForestAlgebra.LinearFunctional.convolution (inverseLinearFunctional a)
        (LForestAlgebra.LinearFunctional.ofCharacter (toCharacter a)) =
      LForestAlgebra.LinearFunctional.counit α R :=
  LForestAlgebra.Character.convolution_inverseLinearFunctional_left (toCharacter a)

theorem convolution_inverseLinearFunctional_right (a : UnitSeries α R) :
    LForestAlgebra.LinearFunctional.convolution
        (LForestAlgebra.LinearFunctional.ofCharacter (toCharacter a))
        (inverseLinearFunctional a) =
      LForestAlgebra.LinearFunctional.counit α R :=
  LForestAlgebra.Character.convolution_inverseLinearFunctional_right (toCharacter a)

theorem mul_left_cancel {a b c : UnitSeries α R}
    (h : a * b = a * c) : b = c := by
  apply ext_toCharacter
  have hχ := congrArg (toCharacter (α := α) (R := R)) h
  rw [toCharacter_mul, toCharacter_mul] at hχ
  exact LForestAlgebra.Character.convolution_left_cancel hχ

theorem mul_right_cancel {a b c : UnitSeries α R}
    (h : b * a = c * a) : b = c := by
  apply ext_toCharacter
  have hχ := congrArg (toCharacter (α := α) (R := R)) h
  rw [toCharacter_mul, toCharacter_mul] at hχ
  exact LForestAlgebra.Character.convolution_right_cancel hχ

theorem mul_left_cancel_iff (a b c : UnitSeries α R) :
    a * b = a * c ↔ b = c := by
  constructor
  · exact mul_left_cancel
  · intro h
    rw [h]

theorem mul_right_cancel_iff (a b c : UnitSeries α R) :
    b * a = c * a ↔ b = c := by
  constructor
  · exact mul_right_cancel
  · intro h
    rw [h]

end

end UnitSeries

end LSeries

end BSeries
