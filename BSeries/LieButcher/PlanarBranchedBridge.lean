/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.LieButcher.Series
import RoughPaths.Branched.Planar

/-!
# Lie group integrators as discrete planarly branched rough paths

The bridge between Lie–Butcher series and planarly branched rough paths
(`RoughPaths.PlanarBranchedRoughPath`): the discrete flow of a Lie group
integrator — the convolution powers of its exponential LS-series — has
shuffle-character increments satisfying Chen's identity for the
Grossman–Larson convolution on ordered times. These are exactly the
defining fields of a planarly branched rough path, sampled along a mesh.
-/

namespace BSeries

open HopfAlgebras RoughPaths

universe u

variable {R : Type u} [CommSemiring R]

namespace LSSeries

/-- Convolution powers of an LS-series: the discrete flow of the
integrator. -/
noncomputable def pow (α : LSSeries R) : ℕ → LSSeries R
  | 0 => PlanarForestAlgebra.counitCoeff (R := R)
  | n + 1 => (pow α n).compose α

@[simp]
theorem pow_zero (α : LSSeries R) :
    α.pow 0 = PlanarForestAlgebra.counitCoeff (R := R) :=
  rfl

theorem pow_succ (α : LSSeries R) (n : ℕ) :
    α.pow (n + 1) = (α.pow n).compose α :=
  rfl

/-- Convolution powers of an exponential series are exponential: every
step of the discrete flow is a Lie group element. -/
theorem pow_isExponential {α : LSSeries R} (hα : IsExponential α) :
    ∀ n : ℕ, IsExponential (α.pow n)
  | 0 => PlanarBranchedRoughPath.counitCoeff_isShuffleCharacter
  | n + 1 => (pow_isExponential hα n).compose hα

/-- The discrete flow property: powers add under composition. -/
theorem pow_add (α : LSSeries R) (a b : ℕ) :
    α.pow (a + b) = (α.pow a).compose (α.pow b) := by
  induction b with
  | zero =>
      funext ω
      exact (PlanarForest.mkwConvolution_counit_right (α.pow a) ω).symm
  | succ b ih =>
      have h1 : α.pow (a + (b + 1)) = (α.pow (a + b)).compose α := rfl
      rw [h1, ih]
      funext ω
      exact PlanarForest.mkwConvolution_assoc (α.pow a) (α.pow b) α ω

end LSSeries

/-- **Chen's identity for the discrete flow** of a Lie group integrator:
the ordered-time increments `α^{t-s}` compose under the Grossman–Larson
convolution, exactly the `chen` field of a
`RoughPaths.PlanarBranchedRoughPath`. -/
example {α : LSSeries R} (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    α.pow (c - a) = (α.pow (b - a)).compose (α.pow (c - b)) := by
  rw [← LSSeries.pow_add]
  congr 1
  omega

/-- **Shuffle-character increments**: every increment of the discrete
flow is a shuffle character, the `isShuffleCharacter` field of a
planarly branched rough path. -/
example {α : LSSeries R} (hα : LSSeries.IsExponential α) (s t : ℕ) :
    PlanarForest.IsShuffleCharacter (α.pow (t - s)) :=
  LSSeries.pow_isExponential hα (t - s)

end BSeries
