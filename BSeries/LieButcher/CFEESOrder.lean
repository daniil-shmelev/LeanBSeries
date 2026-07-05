/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.LieButcher.CommutatorFreeOrder
import BSeries.Numerics.EES27

/-!
# Lie–Butcher order theorems for CF-EES(2,5;x) and CF-EES(2,7;x)

The order theorems of arXiv:2509.20599, Theorems E.1 and E.2, for the
commutator-free lifts of the parametric `EES` families, verified **at
the generic parameter**: over the computable rational-function fields
`CRatFunc ℚ` and `CRatFunc Qsqrt2` the planar order and antisymmetric
order conditions become identities of rational functions in the family
parameter, checked by `native_decide` through the memoised evaluator
`LowStorage.fastMethodChar`.

The symbolic character values are cross-validated against Table 6 of
arXiv:2509.20599: e.g. on the planar cherry the `CF-EES(2,5;x)`
character equals `(2x-5)/(32(x-1))` as a rational function.

This file is a leaf module so that the native evaluations never block
edits to the general theory.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

open LowStorage CRatFunc

/-! ### CF-EES(2,5;X): Theorem E.1 at the generic parameter -/

/-- The materialised generic low-storage data of `EES(2,5;X)` (top-level
constant: evaluated once per process). -/
def ees25Xls : LowStorage 3 (CRatFunc ℚ) :=
  (ees25LowStorage (X : CRatFunc ℚ)).materialize

set_option maxHeartbeats 2000000 in
/-- All decidable checks in one `native_decide` (each invocation compiles
the full closure natively, so they are consolidated). -/
private theorem cfEES25_checks :
    ((X : CRatFunc ℚ) ≠ 1 ∧ 2 * (X : CRatFunc ℚ) ≠ 1 ∧
      2 * (X : CRatFunc ℚ) ≠ -1 ∧ (2 : CRatFunc ℚ) ≠ 0) ∧
    (fastMethodChar ees25Xls [PTree.cherry] =
        (2 * X - 5) / (32 * (X - 1)) ∧
      fastMethodChar ees25Xls [PTree.chain3] = 1 / 8) ∧
    fastMethodChar ees25Xls [PTree.cherry] ≠
      ((PTree.treeFactorial PTree.cherry : ℕ) : CRatFunc ℚ)⁻¹ ∧
    (∀ τ ∈ (List.range 6).flatMap PTree.treesOfOrder,
      LSSeries.symmetricDefect (fastMethodChar ees25Xls) [τ] = 0) ∧
    LSSeries.symmetricDefect (fastMethodChar ees25Xls)
      [PTree.tallTree 5] ≠ 0 := by
  native_decide

private theorem fast25 :
    methodChar (ees25LowStorage (X : CRatFunc ℚ)) =
      fastMethodChar ees25Xls := by
  rw [ees25Xls, LowStorage.materialize_eq, fastMethodChar_eq]

/-- Cross-validation against arXiv:2509.20599, Table 6, **as an identity
of rational functions**: on the planar cherry the `CF-EES(2,5;x)`
character equals `(2x-5)/(32(x-1))`. -/
theorem methodChar_cfEES25_cherry_generic :
    methodChar (ees25LowStorage (X : CRatFunc ℚ)) [PTree.cherry] =
      (2 * X - 5) / (32 * (X - 1)) := by
  rw [fast25]
  exact cfEES25_checks.2.1.1

/-- Cross-validation against arXiv:2509.20599, Table 6: on the
three-chain the character equals `1/8`, independently of the
parameter. -/
theorem methodChar_cfEES25_chain3_generic :
    methodChar (ees25LowStorage (X : CRatFunc ℚ)) [PTree.chain3] =
      1 / 8 := by
  rw [fast25]
  exact cfEES25_checks.2.1.2

/-- **`CF-EES(2,5;X)` has planar order two at the generic parameter**
(arXiv:2509.20599, Theorem E.1(1)); this is an instance of the symbolic
statement `hasPlanarOrder_two_cfEES25`. -/
theorem hasPlanarOrder_two_cfEES25_generic :
    LSSeries.HasPlanarOrder
      (methodChar (ees25LowStorage (X : CRatFunc ℚ))) 2 :=
  hasPlanarOrder_two_cfEES25 cfEES25_checks.1.1 cfEES25_checks.1.2.1
    cfEES25_checks.1.2.2.1 cfEES25_checks.1.2.2.2

/-- `CF-EES(2,5;X)` does not have planar order three: the cherry value
`(2X-5)/(32(X-1))` differs from `1/3` as a rational function. -/
theorem not_hasPlanarOrder_three_cfEES25_generic :
    ¬ LSSeries.HasPlanarOrder
      (methodChar (ees25LowStorage (X : CRatFunc ℚ))) 3 := by
  rw [fast25]
  intro h
  exact cfEES25_checks.2.2.1 (h PTree.cherry (by decide))

/-- **`CF-EES(2,5;X)` has antisymmetric order five at the generic
parameter** (arXiv:2509.20599, Theorem E.1(2)): the symmetric defect of
its LB character vanishes on all planar trees of order at most five, as
identities of rational functions in the parameter. -/
theorem hasPlanarAntisymOrder_five_cfEES25_generic :
    LSSeries.HasPlanarAntisymOrder
      (methodChar (ees25LowStorage (X : CRatFunc ℚ))) 5 := by
  rw [fast25]
  intro τ hτ
  have hmem : τ ∈ (List.range 6).flatMap PTree.treesOfOrder := by
    refine List.mem_flatMap.2 ⟨PTree.order τ, ?_, PTree.mem_treesOfOrder τ⟩
    exact List.mem_range.2 (by omega)
  exact cfEES25_checks.2.2.2.1 τ hmem

/-- `CF-EES(2,5;X)` does not have antisymmetric order six: the six-chain
is a witness at the generic parameter. -/
theorem not_hasPlanarAntisymOrder_six_cfEES25_generic :
    ¬ LSSeries.HasPlanarAntisymOrder
      (methodChar (ees25LowStorage (X : CRatFunc ℚ))) 6 := by
  rw [fast25]
  intro h
  exact cfEES25_checks.2.2.2.2
    (h (PTree.tallTree 5) (by rw [PTree.order_tallTree]))

/-! ### CF-EES(2,7;(2-√2)/4): Theorem E.2 at the representative -/

set_option maxHeartbeats 2000000 in
/-- All decidable checks in one `native_decide`. -/
private theorem cfEES27_checks :
    (∀ τ ∈ (List.range 3).flatMap PTree.treesOfOrder,
      fastMethodChar ees27rLowStorage [τ] *
        (PTree.treeFactorial τ : Qsqrt2) = 1) ∧
    fastMethodChar ees27rLowStorage [PTree.cherry] ≠
      ((PTree.treeFactorial PTree.cherry : ℕ) : Qsqrt2)⁻¹ ∧
    (∀ τ ∈ (List.range 8).flatMap PTree.treesOfOrder,
      LSSeries.symmetricDefect
        (fastMethodChar ees27rLowStorage) [τ] = 0) ∧
    LSSeries.symmetricDefect (fastMethodChar ees27rLowStorage)
      [PTree.tallTree 7] ≠ 0 := by
  native_decide

private theorem fast27 :
    methodChar (ees27LowStorage Qsqrt2.sqrt2 x27) =
      fastMethodChar ees27rLowStorage := by
  rw [ees27rLowStorage, LowStorage.materialize_eq, fastMethodChar_eq]

/-- **`CF-EES(2,7;(2-√2)/4)` has planar order two** (arXiv:2509.20599,
Theorem E.2). -/
theorem hasPlanarOrder_two_cfEES27 :
    LSSeries.HasPlanarOrder
      (methodChar (ees27LowStorage Qsqrt2.sqrt2 x27)) 2 := by
  rw [fast27]
  intro τ hτ
  have hmem : τ ∈ (List.range 3).flatMap PTree.treesOfOrder := by
    refine List.mem_flatMap.2 ⟨PTree.order τ, ?_, PTree.mem_treesOfOrder τ⟩
    exact List.mem_range.2 (by omega)
  exact eq_inv_of_mul_eq_one_left (cfEES27_checks.1 τ hmem)

/-- `CF-EES(2,7;(2-√2)/4)` does not have planar order three. -/
theorem not_hasPlanarOrder_three_cfEES27 :
    ¬ LSSeries.HasPlanarOrder
      (methodChar (ees27LowStorage Qsqrt2.sqrt2 x27)) 3 := by
  rw [fast27]
  intro h
  exact cfEES27_checks.2.1 (h PTree.cherry (by decide))

/-- **`CF-EES(2,7;(2-√2)/4)` has antisymmetric order seven**
(arXiv:2509.20599, Theorem E.2): the symmetric defect of its LB
character vanishes on all `197` planar trees of order at most seven. -/
theorem hasPlanarAntisymOrder_seven_cfEES27 :
    LSSeries.HasPlanarAntisymOrder
      (methodChar (ees27LowStorage Qsqrt2.sqrt2 x27)) 7 := by
  rw [fast27]
  intro τ hτ
  have hmem : τ ∈ (List.range 8).flatMap PTree.treesOfOrder := by
    refine List.mem_flatMap.2 ⟨PTree.order τ, ?_, PTree.mem_treesOfOrder τ⟩
    exact List.mem_range.2 (by omega)
  exact cfEES27_checks.2.2.1 τ hmem

/-- `CF-EES(2,7;(2-√2)/4)` does not have antisymmetric order eight. -/
theorem not_hasPlanarAntisymOrder_eight_cfEES27 :
    ¬ LSSeries.HasPlanarAntisymOrder
      (methodChar (ees27LowStorage Qsqrt2.sqrt2 x27)) 8 := by
  rw [fast27]
  intro h
  exact cfEES27_checks.2.2.2
    (h (PTree.tallTree 7) (by rw [PTree.order_tallTree]))

end RungeKutta

end BSeries
