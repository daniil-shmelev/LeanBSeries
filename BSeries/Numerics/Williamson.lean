/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Williamson.Bazavov
import BSeries.Numerics.Williamson.Subdiagonal
import BSeries.Numerics.Williamson.CommutatorFree

/-!
# Williamson two-register Runge–Kutta schemes

The shared coefficient definitions are in `Williamson.Basic`, and the division-free reconstruction criterion is in `Williamson.Reconstruction`. Two complementary sufficient conditions recover the coefficients: `Williamson.Bazavov` assumes nonzero output weights, while `Williamson.Subdiagonal` assumes nonzero subdiagonal entries and final weight. `Williamson.CommutatorFree` provides the corresponding Lie-group lift.
-/
