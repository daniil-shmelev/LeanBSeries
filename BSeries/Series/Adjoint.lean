/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.AntipodeMultiplicative
import BSeries.Series.Convolution

/-!
# Adjoint Characters and Odd/Even Characters

This file formalizes the Hopf-algebraic structure of the adjoint of a B-series
method, following Shmelev, Ebrahimi-Fard, Tapia & Salvi, *Explicit and
Effectively Symmetric Runge-Kutta Methods* (arXiv:2507.21006), Sections 4-5.

The canonical involution of the forest algebra sends a forest `τ` to
`(-1)^{|τ|} τ`. The adjoint of a B-series character `ψ` is
`ψ*(τ) = (-1)^{|τ|} ψ(S τ)`, which is the convolution inverse of the involuted
character (Theorem 4.2 of the paper). A B-series method is symmetric exactly
when its character is *odd* in the sense of Aguiar-Bergeron-Sottile, while
*even* characters correspond to antisymmetric methods (Corollary 4.3).

## Main definitions

* `ForestAlgebra.gradingInvolution` - the involution `τ ↦ (-1)^{|τ|} τ`
* `ForestAlgebra.LinearFunctional.compGradingInvolution` - composition with
  the involution, which intertwines convolution
* `ForestAlgebra.Character.involution` - the induced involution of characters
* `ForestAlgebra.Character.adjoint` - the adjoint of a B-series character
* `ForestAlgebra.Character.IsEven`, `ForestAlgebra.Character.IsOdd`
* `ForestAlgebra.Character.isOdd_iff_adjoint_eq` - a method is symmetric,
  i.e. equal to its adjoint, if and only if its character is odd
-/

namespace BSeries

open HopfAlgebras

universe u

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

noncomputable section

variable {R : Type u}

private def gradingInvolutionMonoidHom (R : Type u) [CommRing R] :
    Multiplicative RootedForest →* ForestAlgebra R where
  toFun φ :=
    ((-1 : R) ^ RootedForest.order (Multiplicative.toAdd φ)) •
      ofForest (R := R) (Multiplicative.toAdd φ)
  map_one' := by
    change ((-1 : R) ^ RootedForest.order 0) • ofForest (R := R) 0 = 1
    simp [RootedForest.order_zero]
  map_mul' φ ψ := by
    change
      ((-1 : R) ^
          RootedForest.order (Multiplicative.toAdd φ + Multiplicative.toAdd ψ)) •
        ofForest (R := R) (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) = _
    rw [RootedForest.order_add, pow_add, ofForest_add, smul_mul_smul_comm]

/-- The canonical grading involution `τ ↦ (-1)^{|τ|} τ` of the forest algebra
(arXiv:2507.21006, Definition 4.1). -/
def gradingInvolution (R : Type u) [CommRing R] :
    ForestAlgebra R →ₐ[R] ForestAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestAlgebra R) RootedForest)
    (gradingInvolutionMonoidHom R)

@[simp]
theorem gradingInvolution_ofForest [CommRing R] (φ : RootedForest) :
    gradingInvolution R (ofForest φ) =
      ((-1 : R) ^ RootedForest.order φ) • ofForest φ := by
  simp [gradingInvolution, ofForest, gradingInvolutionMonoidHom]

@[simp]
theorem gradingInvolution_gradingInvolution [CommRing R] (x : ForestAlgebra R) :
    gradingInvolution R (gradingInvolution R x) = x := by
  refine AddMonoidAlgebra.induction_on (x := x)
    (p := fun y => gradingInvolution R (gradingInvolution R y) = y) ?_ ?_ ?_
  · intro φ
    change
      gradingInvolution R (gradingInvolution R (ofForest (R := R) φ)) =
        ofForest (R := R) φ
    rw [gradingInvolution_ofForest, map_smul, gradingInvolution_ofForest,
      smul_smul, ← pow_add, Even.neg_one_pow ⟨RootedForest.order φ, rfl⟩,
      one_smul]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

namespace LinearFunctional

open HopfAlgebras.ForestAlgebra.LinearFunctional

/-- Compose a linear functional with the grading involution. -/
def compGradingInvolution [CommRing R] (f : LinearFunctional R) :
    LinearFunctional R :=
  f.comp (gradingInvolution R).toLinearMap

@[simp]
theorem compGradingInvolution_ofForest [CommRing R]
    (f : LinearFunctional R) (φ : RootedForest) :
    compGradingInvolution f (ofForest (R := R) φ) =
      ((-1 : R) ^ RootedForest.order φ) * f (ofForest (R := R) φ) := by
  change f (gradingInvolution R (ofForest (R := R) φ)) = _
  rw [gradingInvolution_ofForest, map_smul, smul_eq_mul]

@[simp]
theorem compGradingInvolution_compGradingInvolution [CommRing R]
    (f : LinearFunctional R) :
    compGradingInvolution (compGradingInvolution f) = f := by
  apply LinearMap.ext
  intro x
  change f (gradingInvolution R (gradingInvolution R x)) = f x
  rw [gradingInvolution_gradingInvolution]

@[simp]
theorem compAntipode_ofForest [CommRing R]
    (f : LinearFunctional R) (φ : RootedForest) :
    compAntipode f (ofForest (R := R) φ) =
      f (RootedForest.antipode (R := R) φ) := by
  change f (antipode (R := R) (ofForest (R := R) φ)) = _
  rw [antipode_ofForest]

/-- Composition with the grading involution intertwines convolution, since
every term of the BCK coproduct preserves the total order grading. -/
theorem convolution_compGradingInvolution [CommRing R]
    (f g : LinearFunctional R) :
    convolution (compGradingInvolution f) (compGradingInvolution g) =
      compGradingInvolution (convolution f g) := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on (x := x)
    (p := fun y =>
      convolution (compGradingInvolution f) (compGradingInvolution g) y =
        compGradingInvolution (convolution f g) y) ?_ ?_ ?_
  · intro φ
    change
      convolution (compGradingInvolution f) (compGradingInvolution g)
          (ofForest (R := R) φ) =
        compGradingInvolution (convolution f g) (ofForest (R := R) φ)
    simp only [convolution_ofForest, compGradingInvolution_ofForest]
    rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    apply List.map_congr_left
    intro term hterm
    have horder := RootedForest.coproductTerms_order hterm
    rw [← horder, pow_add]
    ring
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

end LinearFunctional

namespace Character

open HopfAlgebras.ForestAlgebra.Character

/-- The canonical involution of characters: `ζ̄(τ) = (-1)^{|τ|} ζ(τ)`
(arXiv:2507.21006, Section 4). -/
def involution [CommRing R] (χ : Character R) : Character R :=
  χ.comp (gradingInvolution R)

@[simp]
theorem involution_evalForest [CommRing R] (χ : Character R)
    (φ : RootedForest) :
    (involution χ).evalForest φ =
      ((-1 : R) ^ RootedForest.order φ) * χ.evalForest φ := by
  change χ (gradingInvolution R (ofForest (R := R) φ)) = _
  rw [gradingInvolution_ofForest, map_smul, smul_eq_mul]
  rfl

@[simp]
theorem ofCharacter_involution [CommRing R] (χ : Character R) :
    LinearFunctional.ofCharacter (involution χ) =
      LinearFunctional.compGradingInvolution (LinearFunctional.ofCharacter χ) :=
  rfl

@[simp]
theorem involution_involution [CommRing R] (χ : Character R) :
    involution (involution χ) = χ := by
  apply Character.ext
  intro φ
  rw [involution_evalForest, involution_evalForest, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨RootedForest.order φ, rfl⟩, one_mul]

@[simp]
theorem involution_unit [CommRing R] : involution (unit R) = unit R := by
  apply Character.ext
  intro φ
  rw [involution_evalForest, unit_evalForest]
  classical
  by_cases hφ : φ = 0
  · subst hφ
    simp [RootedForest.order_zero]
  · rw [counitCoeff_ne_zero hφ, mul_zero]

/-- The involution of characters is multiplicative with respect to
convolution: `(ζξ)‾ = ζ̄ ξ̄` (arXiv:2507.21006, Section 4). -/
theorem involution_convolution [CommRing R] (χ ψ : Character R) :
    involution (convolution χ ψ) = convolution (involution χ) (involution ψ) := by
  apply linearFunctional_ofCharacter_injective
  simp only [ofCharacter_involution, linearFunctional_ofCharacter_convolution,
    LinearFunctional.convolution_compGradingInvolution]

/-- The adjoint of a B-series character `ψ`, as a linear functional:
`ψ*(τ) = (-1)^{|τ|} ψ(S τ)` (arXiv:2507.21006, Theorem 4.2). The adjoint
B-series method `Ψ*` has elementary weights `ψ*`. -/
def adjoint [CommRing R] (χ : Character R) : LinearFunctional R :=
  LinearFunctional.compGradingInvolution
    (LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ))

/-- The adjoint character evaluates as `ψ*(τ) = (-1)^{|τ|} ψ(S τ)`. -/
@[simp]
theorem adjoint_ofForest [CommRing R] (χ : Character R) (φ : RootedForest) :
    adjoint χ (ofForest (R := R) φ) =
      ((-1 : R) ^ RootedForest.order φ) *
        χ (RootedForest.antipode (R := R) φ) := by
  rw [adjoint, LinearFunctional.compGradingInvolution_ofForest,
    LinearFunctional.compAntipode_ofForest]
  rfl

/-- The adjoint is a left convolution inverse of the involuted character:
`ψ* ψ̄ = e` (arXiv:2507.21006, proof of Theorem 4.2). -/
theorem convolution_adjoint_left [CommRing R] (χ : Character R) :
    LinearFunctional.convolution (adjoint χ)
        (LinearFunctional.ofCharacter (involution χ)) =
      LinearFunctional.ofCharacter (unit R) := by
  rw [adjoint, ofCharacter_involution,
    LinearFunctional.convolution_compGradingInvolution,
    linearFunctional_convolution_compAntipode_ofCharacter_left χ,
    ← ofCharacter_involution, involution_unit]

/-- The adjoint is a right convolution inverse of the involuted character:
`ψ̄ ψ* = e` (arXiv:2507.21006, proof of Theorem 4.2). -/
theorem convolution_adjoint_right [CommRing R] (χ : Character R) :
    LinearFunctional.convolution
        (LinearFunctional.ofCharacter (involution χ)) (adjoint χ) =
      LinearFunctional.ofCharacter (unit R) := by
  rw [adjoint, ofCharacter_involution,
    LinearFunctional.convolution_compGradingInvolution,
    linearFunctional_convolution_compAntipode_ofCharacter_right χ,
    ← ofCharacter_involution, involution_unit]

/-- A character is even if it is fixed by the canonical involution. Even
characters correspond to antisymmetric methods (arXiv:2507.21006, §5). -/
def IsEven [CommRing R] (χ : Character R) : Prop :=
  involution χ = χ

/-- A character is odd if its involution equals its convolution inverse
`ζ ∘ S`. Odd characters correspond to symmetric B-series methods
(arXiv:2507.21006, Corollary 4.3). -/
def IsOdd [CommRing R] (χ : Character R) : Prop :=
  LinearFunctional.ofCharacter (involution χ) =
    LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ)

theorem isEven_unit [CommRing R] : IsEven (unit R) :=
  involution_unit

theorem isOdd_unit [CommRing R] : IsOdd (unit R) := by
  rw [IsOdd, involution_unit, linearFunctional_ofCharacter_unit]
  apply LinearMap.ext
  intro x
  exact (counit_antipode (R := R) x).symm

/-- A B-series method equals its adjoint if and only if its character is odd:
symmetric B-series methods are exactly the odd characters
(arXiv:2507.21006, Corollary 4.3). -/
theorem isOdd_iff_adjoint_eq [CommRing R] (χ : Character R) :
    IsOdd χ ↔ adjoint χ = LinearFunctional.ofCharacter χ := by
  constructor
  · intro h
    rw [adjoint, ← h, ofCharacter_involution,
      LinearFunctional.compGradingInvolution_compGradingInvolution]
  · intro h
    have h' := congrArg LinearFunctional.compGradingInvolution h
    rw [adjoint, LinearFunctional.compGradingInvolution_compGradingInvolution]
      at h'
    rw [IsOdd, ofCharacter_involution, h']

end Character

/-- Convolution inverses of linear functionals are unique. -/
theorem LinearFunctional.convolution_inverse_unique [CommRing R]
    {f g g' : LinearFunctional R}
    (hg : LinearFunctional.convolution g f = LinearFunctional.counit R)
    (hg' : LinearFunctional.convolution f g' = LinearFunctional.counit R) :
    g = g' :=
  calc g = LinearFunctional.convolution g (LinearFunctional.counit R) :=
        (LinearFunctional.convolution_counit_right g).symm
    _ = LinearFunctional.convolution g (LinearFunctional.convolution f g') := by
        rw [hg']
    _ = LinearFunctional.convolution (LinearFunctional.convolution g f) g' :=
        (LinearFunctional.convolution_assoc g f g').symm
    _ = LinearFunctional.convolution (LinearFunctional.counit R) g' := by
        rw [hg]
    _ = g' := LinearFunctional.convolution_counit_left g'

namespace Character

open HopfAlgebras.ForestAlgebra.Character

theorem convolution_adjoint_left' [CommRing R] (χ : Character R) :
    LinearFunctional.convolution (adjoint χ)
        (LinearFunctional.ofCharacter (involution χ)) =
      LinearFunctional.counit R := by
  rw [convolution_adjoint_left, linearFunctional_ofCharacter_unit]

theorem convolution_adjoint_right' [CommRing R] (χ : Character R) :
    LinearFunctional.convolution
        (LinearFunctional.ofCharacter (involution χ)) (adjoint χ) =
      LinearFunctional.counit R := by
  rw [convolution_adjoint_right, linearFunctional_ofCharacter_unit]

/-- The adjoint is the unique convolution inverse of the involuted
character. -/
theorem adjoint_unique [CommRing R] {χ : Character R}
    {g : LinearFunctional R}
    (hg : LinearFunctional.convolution g
        (LinearFunctional.ofCharacter (involution χ)) =
      LinearFunctional.counit R) :
    g = adjoint χ :=
  LinearFunctional.convolution_inverse_unique hg (convolution_adjoint_right' χ)

/-- The adjoint reverses composition: `(Ψ Φ)* = Φ* Ψ*`
(the B-series analogue of Hairer-Norsett-Wanner II.8, adjoint of a
composition). -/
theorem adjoint_convolution [CommRing R] (χ ψ : Character R) :
    adjoint (convolution χ ψ) =
      LinearFunctional.convolution (adjoint ψ) (adjoint χ) := by
  refine (adjoint_unique ?_).symm
  rw [involution_convolution, linearFunctional_ofCharacter_convolution,
    ← LinearFunctional.convolution_assoc,
    LinearFunctional.convolution_assoc (adjoint ψ) (adjoint χ)
      (LinearFunctional.ofCharacter (involution χ)),
    convolution_adjoint_left' χ, LinearFunctional.convolution_counit_right,
    convolution_adjoint_left' ψ]

/-- Even characters are closed under convolution: antisymmetric methods form
a subgroup of the Butcher group (arXiv:2507.21006, Section 5). -/
theorem IsEven.convolution [CommRing R] {χ ψ : Character R}
    (hχ : IsEven χ) (hψ : IsEven ψ) : IsEven (Character.convolution χ ψ) := by
  rw [IsEven, involution_convolution, hχ, hψ]

/-- The adjoint of an even (antisymmetric) character is its convolution
inverse `ζ ∘ S`. -/
theorem IsEven.adjoint_eq [CommRing R] {χ : Character R} (h : IsEven χ) :
    adjoint χ =
      LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ) := by
  refine LinearFunctional.convolution_inverse_unique
    (f := LinearFunctional.ofCharacter (involution χ))
    (convolution_adjoint_left' χ) ?_
  rw [h]
  rw [LinearFunctional.compAntipode_ofCharacter_eq_compRightAntipode,
    LinearFunctional.convolution_compRightAntipode_ofCharacter_right]

/-- The adjoint of an odd (symmetric) character is the character itself. -/
theorem IsOdd.adjoint_eq [CommRing R] {χ : Character R} (h : IsOdd χ) :
    adjoint χ = LinearFunctional.ofCharacter χ :=
  (isOdd_iff_adjoint_eq χ).1 h

/--
The canonical symmetric composition: for any character `ψ`, the composition
`Ψ* ∘ Ψ` of a method with its adjoint is symmetric. In group form, the
involution of `ψ ψ*` is its convolution inverse
(arXiv:2507.21006, Section 5).
-/
theorem convolution_involution_adjoint_convolution [CommRing R]
    (χ : Character R) :
    LinearFunctional.convolution
        (LinearFunctional.compGradingInvolution
          (LinearFunctional.convolution (adjoint χ)
            (LinearFunctional.ofCharacter χ)))
        (LinearFunctional.convolution (adjoint χ)
          (LinearFunctional.ofCharacter χ)) =
      LinearFunctional.counit R := by
  have hinv : LinearFunctional.compGradingInvolution (adjoint χ) =
      LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ) := by
    rw [adjoint, LinearFunctional.compGradingInvolution_compGradingInvolution]
  rw [← LinearFunctional.convolution_compGradingInvolution, hinv,
    ← ofCharacter_involution,
    LinearFunctional.convolution_assoc,
    ← LinearFunctional.convolution_assoc
      (LinearFunctional.ofCharacter (involution χ)) (adjoint χ)
      (LinearFunctional.ofCharacter χ),
    convolution_adjoint_right' χ, LinearFunctional.convolution_counit_left,
    LinearFunctional.convolution_compAntipode_ofCharacter_left]

/-- The adjoint of a B-series character as a bona fide character, using that
the BCK antipode is an algebra morphism. -/
def adjointCharacter [CommRing R] (χ : Character R) : Character R :=
  (χ.comp (antipodeAlgHom R)).comp (gradingInvolution R)

@[simp]
theorem ofCharacter_adjointCharacter [CommRing R] (χ : Character R) :
    LinearFunctional.ofCharacter (adjointCharacter χ) = adjoint χ :=
  rfl

/-- `ψ*(τ) = (-1)^{|τ|} ψ(S τ)` at the character level
(arXiv:2507.21006, Theorem 4.2). -/
@[simp]
theorem adjointCharacter_evalForest [CommRing R] (χ : Character R)
    (φ : RootedForest) :
    (adjointCharacter χ).evalForest φ =
      ((-1 : R) ^ RootedForest.order φ) *
        χ (RootedForest.antipode (R := R) φ) := by
  have h := adjoint_ofForest χ φ
  rw [← ofCharacter_adjointCharacter] at h
  exact h

/-- The adjoint character is a right inverse of the involuted character in
the character group. -/
theorem convolution_involution_adjointCharacter [CommRing R]
    (χ : Character R) :
    convolution (involution χ) (adjointCharacter χ) = unit R := by
  apply linearFunctional_ofCharacter_injective
  rw [linearFunctional_ofCharacter_convolution, ofCharacter_adjointCharacter,
    convolution_adjoint_right, linearFunctional_ofCharacter_unit]

/-- The adjoint character is a left inverse of the involuted character in
the character group. -/
theorem convolution_adjointCharacter_involution [CommRing R]
    (χ : Character R) :
    convolution (adjointCharacter χ) (involution χ) = unit R := by
  apply linearFunctional_ofCharacter_injective
  rw [linearFunctional_ofCharacter_convolution, ofCharacter_adjointCharacter,
    convolution_adjoint_left, linearFunctional_ofCharacter_unit]

/-- The convolution inverse of a character, as a character: `χ ∘ S`, using
that the BCK antipode is an algebra morphism. -/
def inverseCharacter [CommRing R] (χ : Character R) : Character R :=
  χ.comp (antipodeAlgHom R)

@[simp]
theorem ofCharacter_inverseCharacter [CommRing R] (χ : Character R) :
    LinearFunctional.ofCharacter (inverseCharacter χ) =
      LinearFunctional.compAntipode (LinearFunctional.ofCharacter χ) :=
  rfl

/-- The adjoint character is the involution of the inverse character. -/
theorem adjointCharacter_eq_involution_inverseCharacter [CommRing R]
    (χ : Character R) :
    adjointCharacter χ = involution (inverseCharacter χ) :=
  rfl

theorem convolution_inverseCharacter_left [CommRing R] (χ : Character R) :
    convolution (inverseCharacter χ) χ = unit R := by
  apply linearFunctional_ofCharacter_injective
  rw [linearFunctional_ofCharacter_convolution, ofCharacter_inverseCharacter,
    LinearFunctional.convolution_compAntipode_ofCharacter_left,
    linearFunctional_ofCharacter_unit]

theorem convolution_inverseCharacter_right [CommRing R] (χ : Character R) :
    convolution χ (inverseCharacter χ) = unit R := by
  apply linearFunctional_ofCharacter_injective
  rw [linearFunctional_ofCharacter_convolution, ofCharacter_inverseCharacter,
    LinearFunctional.compAntipode_ofCharacter_eq_compRightAntipode,
    LinearFunctional.convolution_compRightAntipode_ofCharacter_right,
    linearFunctional_ofCharacter_unit]

/-- Convolution inverses of characters are unique. -/
theorem convolution_inverse_unique [CommRing R] {χ ψ ψ' : Character R}
    (h : convolution ψ χ = unit R) (h' : convolution χ ψ' = unit R) :
    ψ = ψ' :=
  calc ψ = convolution ψ (unit R) := (convolution_unit_right ψ).symm
    _ = convolution ψ (convolution χ ψ') := by rw [h']
    _ = convolution (convolution ψ χ) ψ' := (convolution_assoc ψ χ ψ').symm
    _ = convolution (unit R) ψ' := by rw [h]
    _ = ψ' := convolution_unit_left ψ'

/-- Inversion of characters reverses convolution. -/
theorem inverseCharacter_convolution [CommRing R] (χ ψ : Character R) :
    inverseCharacter (convolution χ ψ) =
      convolution (inverseCharacter ψ) (inverseCharacter χ) := by
  refine convolution_inverse_unique
    (convolution_inverseCharacter_left (convolution χ ψ)) ?_
  rw [← convolution_assoc, convolution_assoc χ ψ (inverseCharacter ψ),
    convolution_inverseCharacter_right ψ, convolution_unit_right,
    convolution_inverseCharacter_right χ]

/-- Inversion of characters is involutive. -/
@[simp]
theorem inverseCharacter_inverseCharacter [CommRing R] (χ : Character R) :
    inverseCharacter (inverseCharacter χ) = χ :=
  convolution_inverse_unique
    (convolution_inverseCharacter_left (inverseCharacter χ))
    (convolution_inverseCharacter_left χ)

/-- Inversion commutes with the canonical involution. -/
theorem inverseCharacter_involution [CommRing R] (χ : Character R) :
    inverseCharacter (involution χ) = involution (inverseCharacter χ) := by
  refine convolution_inverse_unique
    (convolution_inverseCharacter_left (involution χ)) ?_
  rw [← involution_convolution, convolution_inverseCharacter_right,
    involution_unit]

/-- The involution of the adjoint character is the inverse character. -/
theorem involution_adjointCharacter [CommRing R] (χ : Character R) :
    involution (adjointCharacter χ) = inverseCharacter χ := by
  rw [adjointCharacter_eq_involution_inverseCharacter, involution_involution]

/-- The inverse of the adjoint character is the involution. -/
theorem inverseCharacter_adjointCharacter [CommRing R] (χ : Character R) :
    inverseCharacter (adjointCharacter χ) = involution χ := by
  rw [adjointCharacter_eq_involution_inverseCharacter,
    inverseCharacter_involution, inverseCharacter_inverseCharacter]

/-- The adjoint is an involution on B-series methods: `ψ** = ψ`
(arXiv:2507.21006, Section 4). -/
@[simp]
theorem adjointCharacter_adjointCharacter [CommRing R] (χ : Character R) :
    adjointCharacter (adjointCharacter χ) = χ := by
  rw [adjointCharacter_eq_involution_inverseCharacter (adjointCharacter χ),
    inverseCharacter_adjointCharacter, involution_involution]

/-- The canonical symmetric composition `ψ* ψ` is an odd character
(arXiv:2507.21006, Section 5). -/
theorem isOdd_convolution_adjointCharacter [CommRing R] (ψ : Character R) :
    IsOdd (convolution (adjointCharacter ψ) ψ) := by
  have h : involution (convolution (adjointCharacter ψ) ψ) =
      inverseCharacter (convolution (adjointCharacter ψ) ψ) := by
    rw [involution_convolution, involution_adjointCharacter,
      inverseCharacter_convolution, inverseCharacter_adjointCharacter]
  unfold IsOdd
  rw [h]
  rfl

/-- A B-series method is symmetric iff its character equals its adjoint
character (arXiv:2507.21006, Corollary 4.3, character form). -/
theorem isOdd_iff_adjointCharacter_eq [CommRing R] (χ : Character R) :
    IsOdd χ ↔ adjointCharacter χ = χ := by
  rw [isOdd_iff_adjoint_eq]
  constructor
  · intro h
    apply linearFunctional_ofCharacter_injective
    rw [ofCharacter_adjointCharacter, h]
  · intro h
    rw [← ofCharacter_adjointCharacter, h]

end Character

end

end ForestAlgebra

end BSeries
