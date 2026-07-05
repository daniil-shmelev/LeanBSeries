/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.Adjoint
import HopfAlgebras.Util.List

/-!
# Convolution Square Roots of B-Series Characters

This file constructs the convolution square root of a B-series character,
following Shmelev, Ebrahimi-Fard, Tapia & Salvi, *Explicit and Effectively
Symmetric Runge-Kutta Methods* (arXiv:2507.21006), Theorem 6.1 with `q = 1/2`:
whenever `2` is invertible, every character `ψ` has a unique convolution
square root normalized to `1` on the empty forest, given by the recursion

  `2 σ(φ) = ψ(φ) - Σ_{proper cuts} σ(P^c) σ(R^c)`.

The paper uses this to define the symmetric component of a B-series method
via `(ψ⁻)² = ψ* ψ` (Section 6), which is `Character.symmetricPart` below.

## Main definitions

* `RootedForest.sqrtCoeff` - the square-root coefficients
* `ForestAlgebra.Character.sqrtFunctional` - the square root functional
* `ForestAlgebra.Character.convolution_sqrtFunctional` - `σ σ = ψ`
* `ForestAlgebra.Character.sqrtFunctional_unique` - uniqueness
* `ForestAlgebra.Character.symmetricPart` - the symmetric component of a
  B-series method, `(ψ* ψ)^{1/2}`
-/

namespace BSeries

open HopfAlgebras

universe u

namespace RootedForest

open HopfAlgebras.RootedForest

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- The coefficients of the convolution square root of a character, defined
by the recursion `2 σ(φ) = ψ(φ) - Σ_{proper cuts} σ(P^c) σ(R^c)`
(arXiv:2507.21006, Theorem 6.1). -/
noncomputable def sqrtCoeff (ψ : ForestAlgebra.Character R)
    (φ : RootedForest) : R := by
  classical
  exact
    if hφ : φ = 0 then 1
    else
      ⅟(2 : R) * (ψ.evalForest φ -
        ((properCoproductTerms φ).attach.map fun term =>
          sqrtCoeff ψ term.1.1 * sqrtCoeff ψ term.1.2).sum)
termination_by order φ
decreasing_by
  · exact properCoproductTerms_left_order_lt term.2
  · exact properCoproductTerms_right_order_lt term.2

@[simp]
theorem sqrtCoeff_zero (ψ : ForestAlgebra.Character R) :
    sqrtCoeff ψ (0 : RootedForest) = 1 := by
  rw [sqrtCoeff]
  simp

theorem sqrtCoeff_eq_of_ne_zero (ψ : ForestAlgebra.Character R)
    {φ : RootedForest} (hφ : φ ≠ 0) :
    sqrtCoeff ψ φ =
      ⅟(2 : R) * (ψ.evalForest φ -
        ((properCoproductTerms φ).map fun term =>
          sqrtCoeff ψ term.1 * sqrtCoeff ψ term.2).sum) := by
  conv_lhs => rw [sqrtCoeff]
  rw [dif_neg hφ, List.sum_attach_map (properCoproductTerms φ)
    fun term => sqrtCoeff ψ term.1 * sqrtCoeff ψ term.2]

/-- The square-root recursion, solved for the character value. -/
theorem two_mul_sqrtCoeff_add_proper (ψ : ForestAlgebra.Character R)
    {φ : RootedForest} (hφ : φ ≠ 0) :
    2 * sqrtCoeff ψ φ +
        ((properCoproductTerms φ).map fun term =>
          sqrtCoeff ψ term.1 * sqrtCoeff ψ term.2).sum =
      ψ.evalForest φ := by
  rw [sqrtCoeff_eq_of_ne_zero ψ hφ, ← mul_assoc, mul_invOf_self, one_mul]
  ring

end

noncomputable section

variable {R : Type u} [CommRing R]

/-- Coefficients of the left convolution inverse of a normalized linear
functional, by the recursion `g(φ) = -f(φ) - Σ_{proper cuts} g(P^c) f(R^c)`. -/
noncomputable def leftInverseCoeff (f : ForestAlgebra.LinearFunctional R)
    (φ : RootedForest) : R := by
  classical
  exact
    if hφ : φ = 0 then 1
    else
      -(f (ForestAlgebra.ofForest (R := R) φ)) -
        ((properCoproductTerms φ).attach.map fun term =>
          leftInverseCoeff f term.1.1 *
            f (ForestAlgebra.ofForest (R := R) term.1.2)).sum
termination_by order φ
decreasing_by
  exact properCoproductTerms_left_order_lt term.2

@[simp]
theorem leftInverseCoeff_zero (f : ForestAlgebra.LinearFunctional R) :
    leftInverseCoeff f (0 : RootedForest) = 1 := by
  rw [leftInverseCoeff]
  simp

theorem leftInverseCoeff_add_proper (f : ForestAlgebra.LinearFunctional R)
    {φ : RootedForest} (hφ : φ ≠ 0) :
    leftInverseCoeff f φ + f (ForestAlgebra.ofForest (R := R) φ) +
        ((properCoproductTerms φ).map fun term =>
          leftInverseCoeff f term.1 *
            f (ForestAlgebra.ofForest (R := R) term.2)).sum = 0 := by
  conv_lhs => rw [leftInverseCoeff]
  rw [dif_neg hφ, List.sum_attach_map (properCoproductTerms φ) fun term =>
    leftInverseCoeff f term.1 * f (ForestAlgebra.ofForest (R := R) term.2)]
  ring

/-- Coefficients of the right convolution inverse of a normalized linear
functional, by the recursion `g(φ) = -f(φ) - Σ_{proper cuts} f(P^c) g(R^c)`. -/
noncomputable def rightInverseCoeff (f : ForestAlgebra.LinearFunctional R)
    (φ : RootedForest) : R := by
  classical
  exact
    if hφ : φ = 0 then 1
    else
      -(f (ForestAlgebra.ofForest (R := R) φ)) -
        ((properCoproductTerms φ).attach.map fun term =>
          f (ForestAlgebra.ofForest (R := R) term.1.1) *
            rightInverseCoeff f term.1.2).sum
termination_by order φ
decreasing_by
  exact properCoproductTerms_right_order_lt term.2

@[simp]
theorem rightInverseCoeff_zero (f : ForestAlgebra.LinearFunctional R) :
    rightInverseCoeff f (0 : RootedForest) = 1 := by
  rw [rightInverseCoeff]
  simp

theorem rightInverseCoeff_add_proper (f : ForestAlgebra.LinearFunctional R)
    {φ : RootedForest} (hφ : φ ≠ 0) :
    f (ForestAlgebra.ofForest (R := R) φ) + rightInverseCoeff f φ +
        ((properCoproductTerms φ).map fun term =>
          f (ForestAlgebra.ofForest (R := R) term.1) *
            rightInverseCoeff f term.2).sum = 0 := by
  conv_lhs => rw [rightInverseCoeff]
  rw [dif_neg hφ, List.sum_attach_map (properCoproductTerms φ) fun term =>
    f (ForestAlgebra.ofForest (R := R) term.1) * rightInverseCoeff f term.2]
  ring

end

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- The square-root coefficients depend only on the character's values on
forests up to the given order. -/
theorem sqrtCoeff_congr {ψ ψ' : ForestAlgebra.Character R} (n : ℕ)
    (h : ∀ φ : RootedForest, order φ ≤ n →
      ψ.evalForest φ = ψ'.evalForest φ) :
    ∀ φ : RootedForest, order φ ≤ n → sqrtCoeff ψ φ = sqrtCoeff ψ' φ := by
  suffices haux : ∀ (m : ℕ) (φ : RootedForest), order φ ≤ m →
      order φ ≤ n → sqrtCoeff ψ φ = sqrtCoeff ψ' φ from
    fun φ hφ => haux (order φ) φ le_rfl hφ
  intro m
  induction m with
  | zero =>
      intro φ h0 _
      have hφ : φ = 0 := (order_eq_zero_iff φ).1 (by omega)
      rw [hφ, sqrtCoeff_zero, sqrtCoeff_zero]
  | succ m ih =>
      intro φ hm hn
      by_cases hφ : φ = 0
      · rw [hφ, sqrtCoeff_zero, sqrtCoeff_zero]
      · rw [sqrtCoeff_eq_of_ne_zero ψ hφ, sqrtCoeff_eq_of_ne_zero ψ' hφ,
          h φ hn]
        congr 2
        refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
        have hl := properCoproductTerms_left_order_lt hterm
        have hr := properCoproductTerms_right_order_lt hterm
        have hg := properCoproductTerms_order hterm
        rw [ih term.1 (by omega) (by omega),
          ih term.2 (by omega) (by omega)]

/-- The coproduct terms of the empty forest. -/
theorem coproductTerms_zero :
    coproductTerms (0 : RootedForest) =
      [((0 : RootedForest), (0 : RootedForest))] := by
  have hout : (Quotient.out (0 : RootedForest) : List RootedTree) = [] := by
    have h : (Quotient.out (0 : RootedForest)).Perm ([] : List RootedTree) :=
      Quotient.exact (Quotient.out_eq (0 : RootedForest))
    exact h.eq_nil
  rw [coproductTerms, hout]
  rfl

end

end RootedForest

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

namespace Character

open HopfAlgebras.ForestAlgebra.Character

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- The convolution square root of a character, as a linear functional. -/
noncomputable def sqrtFunctional (ψ : Character R) : LinearFunctional R :=
  Finsupp.linearCombination R (RootedForest.sqrtCoeff ψ)

@[simp]
theorem sqrtFunctional_ofForest (ψ : Character R) (φ : RootedForest) :
    sqrtFunctional ψ (ofForest (R := R) φ) = RootedForest.sqrtCoeff ψ φ := by
  rw [sqrtFunctional, ofForest]
  change (Finsupp.linearCombination R (RootedForest.sqrtCoeff ψ))
      (Finsupp.single φ (1 : R)) = RootedForest.sqrtCoeff ψ φ
  rw [Finsupp.linearCombination_single]
  simp

private theorem sum_terms_eq_boundary_add_proper {M : Type*} [AddCommMonoid M]
    {φ : RootedForest} (hφ : φ ≠ 0)
    (F : RootedForest × RootedForest → M) :
    ∀ terms : List (RootedForest × RootedForest),
      (∀ term ∈ terms, RootedForest.order term.1 = 0 → term = (0, φ)) →
      (∀ term ∈ terms, RootedForest.order term.2 = 0 → term = (φ, 0)) →
      (terms.map F).sum =
        ((terms.filterMap PTree.leftBoundaryCoproductTerm?).map F).sum +
        ((terms.filterMap PTree.rightBoundaryCoproductTerm?).map F).sum +
        ((terms.filter fun term =>
            0 < RootedForest.order term.1 ∧
              0 < RootedForest.order term.2).map F).sum
  | [], _hleft, _hright => by
      simp
  | term :: terms, hleft, hright => by
      have hleft_tail :
          ∀ term' ∈ terms, RootedForest.order term'.1 = 0 → term' = (0, φ) :=
        fun term' hmem hzero => hleft term' (by simp [hmem]) hzero
      have hright_tail :
          ∀ term' ∈ terms, RootedForest.order term'.2 = 0 → term' = (φ, 0) :=
        fun term' hmem hzero => hright term' (by simp [hmem]) hzero
      have ih := sum_terms_eq_boundary_add_proper hφ F terms hleft_tail
        hright_tail
      have hφ_order : RootedForest.order φ ≠ 0 := fun hzero =>
        hφ ((RootedForest.order_eq_zero_iff φ).1 hzero)
      by_cases hterm_left : RootedForest.order term.1 = 0
      · have hterm : term = (0, φ) := hleft term (by simp) hterm_left
        subst hterm
        simp [PTree.leftBoundaryCoproductTerm?,
          PTree.rightBoundaryCoproductTerm?, hφ_order, ih]
        abel
      · by_cases hterm_right : RootedForest.order term.2 = 0
        · have hterm : term = (φ, 0) := hright term (by simp) hterm_right
          subst hterm
          simp [PTree.leftBoundaryCoproductTerm?,
            PTree.rightBoundaryCoproductTerm?, hφ_order, ih]
          abel
        · have hpos : 0 < RootedForest.order term.1 ∧
              0 < RootedForest.order term.2 :=
            ⟨Nat.pos_of_ne_zero hterm_left, Nat.pos_of_ne_zero hterm_right⟩
          simp [PTree.leftBoundaryCoproductTerm?,
            PTree.rightBoundaryCoproductTerm?, hterm_left, hterm_right,
            hpos, ih]
          abel

private theorem coproductTerms_boundary_hyps {φ : RootedForest}
    (_hφ : φ ≠ 0) :
    (∀ term ∈ RootedForest.coproductTerms φ,
      RootedForest.order term.1 = 0 → term = (0, φ)) ∧
    (∀ term ∈ RootedForest.coproductTerms φ,
      RootedForest.order term.2 = 0 → term = (φ, 0)) := by
  constructor
  · intro term hterm hzero
    have hleft_zero : term.1 = 0 :=
      (RootedForest.order_eq_zero_iff term.1).1 hzero
    have hright := RootedForest.coproductTerms_left_eq_zero hterm hleft_zero
    cases term with
    | mk left right =>
        simp only at hleft_zero hright
        rw [hleft_zero, hright]
  · intro term hterm hzero
    have hright_zero : term.2 = 0 :=
      (RootedForest.order_eq_zero_iff term.2).1 hzero
    have hleft := RootedForest.coproductTerms_right_eq_zero hterm hright_zero
    cases term with
    | mk left right =>
        simp only at hright_zero hleft
        rw [hright_zero, hleft]

/-- The square root squares to the character:
`σ σ = ψ` in the convolution algebra (arXiv:2507.21006, Theorem 6.1). -/
theorem convolution_sqrtFunctional (ψ : Character R) :
    LinearFunctional.convolution (sqrtFunctional ψ) (sqrtFunctional ψ) =
      LinearFunctional.ofCharacter ψ := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on (x := x)
    (p := fun y =>
      LinearFunctional.convolution (sqrtFunctional ψ) (sqrtFunctional ψ) y =
        LinearFunctional.ofCharacter ψ y) ?_ ?_ ?_
  · intro φ
    change
      LinearFunctional.convolution (sqrtFunctional ψ) (sqrtFunctional ψ)
          (ofForest (R := R) φ) = ψ (ofForest (R := R) φ)
    rw [LinearFunctional.convolution_ofForest]
    by_cases hφ : φ = 0
    · subst hφ
      rw [RootedForest.coproductTerms_zero]
      simp
    · obtain ⟨hleft, hright⟩ := coproductTerms_boundary_hyps hφ
      rw [sum_terms_eq_boundary_add_proper hφ _
          (RootedForest.coproductTerms φ) hleft hright,
        RootedForest.coproductTerms_leftBoundaryCoproductTerm,
        RootedForest.coproductTerms_rightBoundaryCoproductTerm]
      rw [show ((RootedForest.coproductTerms φ).filter fun term =>
          0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2) =
            RootedForest.properCoproductTerms φ from rfl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, sqrtFunctional_ofForest, RootedForest.sqrtCoeff_zero,
        one_mul, mul_one]
      have h := RootedForest.two_mul_sqrtCoeff_add_proper ψ hφ
      change _ = ψ (ofForest (R := R) φ) at h ⊢
      rw [← h]
      ring
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

/-- Uniqueness of the normalized convolution square root, on forest
monomials. -/
theorem sqrtFunctional_unique_coeff (ψ : Character R)
    {f : LinearFunctional R}
    (hone : f (ofForest (R := R) 0) = 1)
    (hsq : LinearFunctional.convolution f f =
      LinearFunctional.ofCharacter ψ) :
    ∀ φ : RootedForest, f (ofForest (R := R) φ) =
      RootedForest.sqrtCoeff ψ φ := by
  have key : ∀ (n : Nat) (φ : RootedForest), RootedForest.order φ ≤ n →
      f (ofForest (R := R) φ) = RootedForest.sqrtCoeff ψ φ := by
    intro n
    induction n with
    | zero =>
        intro φ h
        have hφ : φ = 0 :=
          (RootedForest.order_eq_zero_iff φ).1 (Nat.le_zero.1 h)
        subst hφ
        rw [hone, RootedForest.sqrtCoeff_zero]
    | succ n ih =>
        intro φ hle
        by_cases hφ : φ = 0
        · subst hφ
          rw [hone, RootedForest.sqrtCoeff_zero]
        · have hsq_φ := congrArg (fun g : LinearFunctional R =>
            g (ofForest (R := R) φ)) hsq
          rw [LinearFunctional.convolution_ofForest] at hsq_φ
          obtain ⟨hleft, hright⟩ := coproductTerms_boundary_hyps hφ
          rw [sum_terms_eq_boundary_add_proper hφ _
              (RootedForest.coproductTerms φ) hleft hright,
            RootedForest.coproductTerms_leftBoundaryCoproductTerm,
            RootedForest.coproductTerms_rightBoundaryCoproductTerm] at hsq_φ
          rw [show ((RootedForest.coproductTerms φ).filter fun term =>
              0 < RootedForest.order term.1 ∧
                0 < RootedForest.order term.2) =
                RootedForest.properCoproductTerms φ from rfl] at hsq_φ
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            add_zero, hone, one_mul, mul_one] at hsq_φ
          have hproper :
              ((RootedForest.properCoproductTerms φ).map fun term =>
                f (ofForest (R := R) term.1) * f (ofForest (R := R) term.2)).sum =
              ((RootedForest.properCoproductTerms φ).map fun term =>
                RootedForest.sqrtCoeff ψ term.1 *
                  RootedForest.sqrtCoeff ψ term.2).sum := by
            refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
            rw [ih term.1 (by
                have := RootedForest.properCoproductTerms_left_order_lt hterm
                omega),
              ih term.2 (by
                have := RootedForest.properCoproductTerms_right_order_lt hterm
                omega)]
          rw [hproper] at hsq_φ
          have h2 := RootedForest.two_mul_sqrtCoeff_add_proper ψ hφ
          change _ = ψ (ofForest (R := R) φ) at h2
          have hcancel : 2 * f (ofForest (R := R) φ) =
              2 * RootedForest.sqrtCoeff ψ φ := by
            change _ = ψ (ofForest (R := R) φ) at hsq_φ
            linear_combination hsq_φ - h2
          simpa [invOf_mul_cancel_left] using
            congrArg (⅟(2 : R) * ·) hcancel
  exact fun φ => key (RootedForest.order φ) φ le_rfl

/--
The symmetric component of a B-series method: the convolution square root of
the canonical symmetric composition `ψ* ψ`, so that `(ψ⁻)² = ψ* ψ`
(arXiv:2507.21006, Section 6).
-/
noncomputable def symmetricPart (ψ : Character R) : LinearFunctional R :=
  sqrtFunctional (Character.convolution (adjointCharacter ψ) ψ)

/-- The defining property of the symmetric component:
`(ψ⁻)² = ψ* ψ` (arXiv:2507.21006, Section 6). -/
theorem convolution_symmetricPart (ψ : Character R) :
    LinearFunctional.convolution (symmetricPart ψ) (symmetricPart ψ) =
      LinearFunctional.ofCharacter
        (Character.convolution (adjointCharacter ψ) ψ) :=
  convolution_sqrtFunctional _

end

end Character

namespace LinearFunctional

open HopfAlgebras.ForestAlgebra.LinearFunctional

noncomputable section

variable {R : Type u} [CommRing R]

/-- The left convolution inverse of a normalized linear functional. -/
noncomputable def leftInverse (f : LinearFunctional R) : LinearFunctional R :=
  Finsupp.linearCombination R (RootedForest.leftInverseCoeff f)

@[simp]
theorem leftInverse_ofForest (f : LinearFunctional R) (φ : RootedForest) :
    leftInverse f (ofForest (R := R) φ) =
      RootedForest.leftInverseCoeff f φ := by
  rw [leftInverse, ofForest]
  change (Finsupp.linearCombination R (RootedForest.leftInverseCoeff f))
      (Finsupp.single φ (1 : R)) = _
  rw [Finsupp.linearCombination_single]
  simp

/-- The right convolution inverse of a normalized linear functional. -/
noncomputable def rightInverse (f : LinearFunctional R) : LinearFunctional R :=
  Finsupp.linearCombination R (RootedForest.rightInverseCoeff f)

@[simp]
theorem rightInverse_ofForest (f : LinearFunctional R) (φ : RootedForest) :
    rightInverse f (ofForest (R := R) φ) =
      RootedForest.rightInverseCoeff f φ := by
  rw [rightInverse, ofForest]
  change (Finsupp.linearCombination R (RootedForest.rightInverseCoeff f))
      (Finsupp.single φ (1 : R)) = _
  rw [Finsupp.linearCombination_single]
  simp

theorem convolution_leftInverse (f : LinearFunctional R)
    (hf : f (ofForest (R := R) 0) = 1) :
    convolution (leftInverse f) f = LinearFunctional.counit R := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on (x := x) (p := fun y =>
    convolution (leftInverse f) f y = LinearFunctional.counit R y) ?_ ?_ ?_
  · intro φ
    change convolution (leftInverse f) f (ofForest (R := R) φ) =
      LinearFunctional.counit R (ofForest (R := R) φ)
    rw [convolution_ofForest]
    have hcounit : LinearFunctional.counit R (ofForest (R := R) φ) =
        ForestAlgebra.counitCoeff (R := R) φ := by
      change ForestAlgebra.counit R (ofForest (R := R) φ) = _
      rw [ForestAlgebra.counit_ofForest]
    rw [hcounit]
    by_cases hφ : φ = 0
    · subst hφ
      rw [RootedForest.coproductTerms_zero]
      rw [ForestAlgebra.ofForest_zero] at hf
      simp [hf]
    · rw [ForestAlgebra.counitCoeff_ne_zero hφ]
      obtain ⟨hleft, hright⟩ := Character.coproductTerms_boundary_hyps hφ
      rw [Character.sum_terms_eq_boundary_add_proper hφ _
          (RootedForest.coproductTerms φ) hleft hright,
        RootedForest.coproductTerms_leftBoundaryCoproductTerm,
        RootedForest.coproductTerms_rightBoundaryCoproductTerm]
      rw [show ((RootedForest.coproductTerms φ).filter fun term =>
          0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2) =
            RootedForest.properCoproductTerms φ from rfl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, leftInverse_ofForest, RootedForest.leftInverseCoeff_zero,
        one_mul, hf, mul_one]
      have h := RootedForest.leftInverseCoeff_add_proper f hφ
      linear_combination h
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

theorem convolution_rightInverse (f : LinearFunctional R)
    (hf : f (ofForest (R := R) 0) = 1) :
    convolution f (rightInverse f) = LinearFunctional.counit R := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on (x := x) (p := fun y =>
    convolution f (rightInverse f) y = LinearFunctional.counit R y) ?_ ?_ ?_
  · intro φ
    change convolution f (rightInverse f) (ofForest (R := R) φ) =
      LinearFunctional.counit R (ofForest (R := R) φ)
    rw [convolution_ofForest]
    have hcounit : LinearFunctional.counit R (ofForest (R := R) φ) =
        ForestAlgebra.counitCoeff (R := R) φ := by
      change ForestAlgebra.counit R (ofForest (R := R) φ) = _
      rw [ForestAlgebra.counit_ofForest]
    rw [hcounit]
    by_cases hφ : φ = 0
    · subst hφ
      rw [RootedForest.coproductTerms_zero]
      rw [ForestAlgebra.ofForest_zero] at hf
      simp [hf]
    · rw [ForestAlgebra.counitCoeff_ne_zero hφ]
      obtain ⟨hleft, hright⟩ := Character.coproductTerms_boundary_hyps hφ
      rw [Character.sum_terms_eq_boundary_add_proper hφ _
          (RootedForest.coproductTerms φ) hleft hright,
        RootedForest.coproductTerms_leftBoundaryCoproductTerm,
        RootedForest.coproductTerms_rightBoundaryCoproductTerm]
      rw [show ((RootedForest.coproductTerms φ).filter fun term =>
          0 < RootedForest.order term.1 ∧ 0 < RootedForest.order term.2) =
            RootedForest.properCoproductTerms φ from rfl]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, rightInverse_ofForest, RootedForest.rightInverseCoeff_zero,
        one_mul, hf, mul_one]
      have h := RootedForest.rightInverseCoeff_add_proper f hφ
      linear_combination h
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

/-- Left and right convolution inverses coincide. -/
theorem leftInverse_eq_rightInverse (f : LinearFunctional R)
    (hf : f (ofForest (R := R) 0) = 1) :
    leftInverse f = rightInverse f :=
  convolution_inverse_unique (convolution_leftInverse f hf)
    (convolution_rightInverse f hf)

/-- The left inverse is a two-sided inverse. -/
theorem convolution_leftInverse_right (f : LinearFunctional R)
    (hf : f (ofForest (R := R) 0) = 1) :
    convolution f (leftInverse f) = LinearFunctional.counit R := by
  rw [leftInverse_eq_rightInverse f hf]
  exact convolution_rightInverse f hf

/-- The counit is fixed by the grading involution. -/
theorem compGradingInvolution_counit :
    compGradingInvolution (LinearFunctional.counit R) = LinearFunctional.counit R := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on (x := x) (p := fun y =>
    compGradingInvolution (LinearFunctional.counit R) y = LinearFunctional.counit R y) ?_ ?_ ?_
  · intro φ
    change compGradingInvolution (LinearFunctional.counit R) (ofForest (R := R) φ) =
      LinearFunctional.counit R (ofForest (R := R) φ)
    rw [compGradingInvolution_ofForest]
    have hc : LinearFunctional.counit R (ofForest (R := R) φ) =
        ForestAlgebra.counitCoeff (R := R) φ := by
      change ForestAlgebra.counit R (ofForest (R := R) φ) = _
      rw [ForestAlgebra.counit_ofForest]
    rw [hc]
    by_cases hφ : φ = 0
    · subst hφ
      simp
    · rw [ForestAlgebra.counitCoeff_ne_zero hφ, mul_zero]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

end

end LinearFunctional

namespace Character

open HopfAlgebras.ForestAlgebra.Character

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- Uniqueness of the normalized convolution square root. -/
theorem sqrtFunctional_unique (ψ : Character R) {f : LinearFunctional R}
    (hone : f (ofForest (R := R) 0) = 1)
    (hsq : LinearFunctional.convolution f f =
      LinearFunctional.ofCharacter ψ) :
    f = sqrtFunctional ψ := by
  apply LinearMap.ext
  intro x
  refine AddMonoidAlgebra.induction_on (x := x)
    (p := fun y => f y = sqrtFunctional ψ y) ?_ ?_ ?_
  · intro φ
    change f (ofForest (R := R) φ) = sqrtFunctional ψ (ofForest (R := R) φ)
    rw [sqrtFunctional_ofForest]
    exact sqrtFunctional_unique_coeff ψ hone hsq φ
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]

/--
The symmetric component of a B-series method is symmetric: the involution of
`ψ⁻ = (ψ* ψ)^{1/2}` is its convolution inverse (arXiv:2507.21006, Section 6;
the case `q = 1/2` of Proposition 6.2).
-/
theorem convolution_compGradingInvolution_symmetricPart (ψ : Character R) :
    LinearFunctional.convolution
        (LinearFunctional.compGradingInvolution (symmetricPart ψ))
        (symmetricPart ψ) =
      LinearFunctional.counit R := by
  have hσ_one : symmetricPart ψ (ofForest (R := R) 0) = 1 := by
    rw [symmetricPart, sqrtFunctional_ofForest, RootedForest.sqrtCoeff_zero]
  have hginv := LinearFunctional.convolution_leftInverse (symmetricPart ψ)
    hσ_one
  have hg_norm : LinearFunctional.leftInverse (symmetricPart ψ)
      (ofForest (R := R) 0) = 1 := by
    rw [LinearFunctional.leftInverse_ofForest,
      RootedForest.leftInverseCoeff_zero]
  -- the square of the inverse is the inverse of the square
  have hgg : LinearFunctional.convolution
      (LinearFunctional.convolution
        (LinearFunctional.leftInverse (symmetricPart ψ))
        (LinearFunctional.leftInverse (symmetricPart ψ)))
      (LinearFunctional.ofCharacter
        (convolution (adjointCharacter ψ) ψ)) =
      LinearFunctional.counit R := by
    rw [← convolution_symmetricPart ψ, LinearFunctional.convolution_assoc,
      ← LinearFunctional.convolution_assoc
        (LinearFunctional.leftInverse (symmetricPart ψ)) (symmetricPart ψ)
        (symmetricPart ψ),
      hginv, LinearFunctional.convolution_counit_left, hginv]
  have hobs : LinearFunctional.convolution
      (LinearFunctional.ofCharacter (convolution (adjointCharacter ψ) ψ))
      (LinearFunctional.ofCharacter
        (inverseCharacter (convolution (adjointCharacter ψ) ψ))) =
      LinearFunctional.counit R := by
    rw [← linearFunctional_ofCharacter_convolution,
      convolution_inverseCharacter_right, linearFunctional_ofCharacter_unit]
  have hgg' : LinearFunctional.convolution
      (LinearFunctional.leftInverse (symmetricPart ψ))
      (LinearFunctional.leftInverse (symmetricPart ψ)) =
      LinearFunctional.ofCharacter
        (inverseCharacter (convolution (adjointCharacter ψ) ψ)) :=
    LinearFunctional.convolution_inverse_unique hgg hobs
  -- the involuted square root also squares to the inverse character
  have hodd_eq : involution (convolution (adjointCharacter ψ) ψ) =
      inverseCharacter (convolution (adjointCharacter ψ) ψ) :=
    linearFunctional_ofCharacter_injective (by
      rw [ofCharacter_inverseCharacter]
      exact isOdd_convolution_adjointCharacter ψ)
  have hbar : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution (symmetricPart ψ))
      (LinearFunctional.compGradingInvolution (symmetricPart ψ)) =
      LinearFunctional.ofCharacter
        (inverseCharacter (convolution (adjointCharacter ψ) ψ)) := by
    rw [LinearFunctional.convolution_compGradingInvolution,
      convolution_symmetricPart, ← ofCharacter_involution, hodd_eq]
  have hbar_norm : LinearFunctional.compGradingInvolution (symmetricPart ψ)
      (ofForest (R := R) 0) = 1 := by
    rw [LinearFunctional.compGradingInvolution_ofForest, hσ_one,
      RootedForest.order_zero, pow_zero, one_mul]
  have h1 := sqrtFunctional_unique
    (inverseCharacter (convolution (adjointCharacter ψ) ψ)) hbar_norm hbar
  have h2 := sqrtFunctional_unique
    (inverseCharacter (convolution (adjointCharacter ψ) ψ)) hg_norm hgg'
  rw [h1, ← h2]
  exact hginv

/-- The symmetric component is invertible with inverse its involution. -/
theorem convolution_symmetricPart_compGradingInvolution (ψ : Character R) :
    LinearFunctional.convolution (symmetricPart ψ)
        (LinearFunctional.compGradingInvolution (symmetricPart ψ)) =
      LinearFunctional.counit R := by
  have hσ_one : symmetricPart ψ (ofForest (R := R) 0) = 1 := by
    rw [symmetricPart, sqrtFunctional_ofForest, RootedForest.sqrtCoeff_zero]
  have h3 : LinearFunctional.compGradingInvolution (symmetricPart ψ) =
      LinearFunctional.leftInverse (symmetricPart ψ) :=
    LinearFunctional.convolution_inverse_unique
      (convolution_compGradingInvolution_symmetricPart ψ)
      (LinearFunctional.convolution_leftInverse_right (symmetricPart ψ)
        hσ_one)
  rw [h3]
  exact LinearFunctional.convolution_leftInverse_right (symmetricPart ψ)
    hσ_one

/--
The antisymmetric component of a B-series method: `ψ⁺ := ψ (ψ⁻)⁻¹`, so that
`ψ = ψ⁺ ψ⁻` (arXiv:2507.21006, Corollary 5.3 via the Section 6
construction).
-/
noncomputable def antisymmetricPart (ψ : Character R) : LinearFunctional R :=
  LinearFunctional.convolution (LinearFunctional.ofCharacter ψ)
    (LinearFunctional.compGradingInvolution (symmetricPart ψ))

/-- The symmetric decomposition of a B-series method: `ψ = ψ⁺ ψ⁻` with `ψ⁻`
symmetric and `ψ⁺` antisymmetric (arXiv:2507.21006, Corollary 5.3). -/
theorem convolution_antisymmetricPart_symmetricPart (ψ : Character R) :
    LinearFunctional.convolution (antisymmetricPart ψ) (symmetricPart ψ) =
      LinearFunctional.ofCharacter ψ := by
  rw [antisymmetricPart, LinearFunctional.convolution_assoc,
    convolution_compGradingInvolution_symmetricPart,
    LinearFunctional.convolution_counit_right]

/-- The antisymmetric component is even: it is fixed by the canonical
involution (arXiv:2507.21006, Corollary 5.3). -/
theorem compGradingInvolution_antisymmetricPart (ψ : Character R) :
    LinearFunctional.compGradingInvolution (antisymmetricPart ψ) =
      antisymmetricPart ψ := by
  have hcancel : ∀ f g : LinearFunctional R,
      LinearFunctional.convolution f (symmetricPart ψ) =
        LinearFunctional.convolution g (symmetricPart ψ) → f = g := by
    intro f g h
    have h' := congrArg (fun k => LinearFunctional.convolution k
      (LinearFunctional.compGradingInvolution (symmetricPart ψ))) h
    simpa [LinearFunctional.convolution_assoc,
      convolution_symmetricPart_compGradingInvolution ψ,
      LinearFunctional.convolution_counit_right] using h'
  apply hcancel
  have hlhs : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution (antisymmetricPart ψ))
      (symmetricPart ψ) = LinearFunctional.ofCharacter ψ := by
    rw [antisymmetricPart,
      ← LinearFunctional.convolution_compGradingInvolution,
      LinearFunctional.compGradingInvolution_compGradingInvolution,
      LinearFunctional.convolution_assoc, convolution_symmetricPart,
      ← ofCharacter_involution, ← linearFunctional_ofCharacter_convolution,
      ← convolution_assoc, convolution_involution_adjointCharacter,
      convolution_unit_left]
  rw [hlhs]
  exact (convolution_antisymmetricPart_symmetricPart ψ).symm

/--
Uniqueness of the symmetric factor: if `ψ = e ⋆ o` with `e` even, `o` odd and
both normalized, then `o` is the symmetric component
(arXiv:2507.21006, Theorem 5.2, uniqueness).
-/
theorem symmetricPart_unique (ψ : Character R) {e o : LinearFunctional R}
    (he_norm : e (ofForest (R := R) 0) = 1)
    (ho_norm : o (ofForest (R := R) 0) = 1)
    (he : LinearFunctional.compGradingInvolution e = e)
    (ho : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution o) o =
      LinearFunctional.counit R)
    (hdec : LinearFunctional.convolution e o =
      LinearFunctional.ofCharacter ψ) :
    o = symmetricPart ψ := by
  -- the involution of `o` is its two-sided inverse
  have ho2 : LinearFunctional.convolution o
      (LinearFunctional.compGradingInvolution o) =
      LinearFunctional.counit R := by
    have h1 : LinearFunctional.compGradingInvolution o =
        LinearFunctional.leftInverse o :=
      LinearFunctional.convolution_inverse_unique ho
        (LinearFunctional.convolution_leftInverse_right o ho_norm)
    rw [h1]
    exact LinearFunctional.convolution_leftInverse_right o ho_norm
  have he_inv_left := LinearFunctional.convolution_leftInverse e he_norm
  have he_inv_right :=
    LinearFunctional.convolution_leftInverse_right e he_norm
  -- the adjoint of `ψ` factors as `o ⋆ e⁻¹`
  have hinvol : LinearFunctional.compGradingInvolution
      (LinearFunctional.ofCharacter ψ) =
      LinearFunctional.convolution e
        (LinearFunctional.compGradingInvolution o) := by
    rw [← hdec, ← LinearFunctional.convolution_compGradingInvolution, he]
  have hadj_left : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution
        (LinearFunctional.ofCharacter ψ))
      (LinearFunctional.ofCharacter (adjointCharacter ψ)) =
      LinearFunctional.counit R := by
    rw [← ofCharacter_involution, ← linearFunctional_ofCharacter_convolution,
      convolution_involution_adjointCharacter,
      linearFunctional_ofCharacter_unit]
  have hcand_right : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution
        (LinearFunctional.ofCharacter ψ))
      (LinearFunctional.convolution o (LinearFunctional.leftInverse e)) =
      LinearFunctional.counit R := by
    rw [hinvol, LinearFunctional.convolution_assoc,
      ← LinearFunctional.convolution_assoc
        (LinearFunctional.compGradingInvolution o) o
        (LinearFunctional.leftInverse e),
      ho, LinearFunctional.convolution_counit_left, he_inv_right]
  have hadj_eq : LinearFunctional.ofCharacter (adjointCharacter ψ) =
      LinearFunctional.convolution o (LinearFunctional.leftInverse e) := by
    refine LinearFunctional.convolution_inverse_unique ?_ hcand_right
    rw [← ofCharacter_involution, ← linearFunctional_ofCharacter_convolution]
    rw [show convolution (adjointCharacter ψ) (involution ψ) = unit R from
      convolution_adjointCharacter_involution ψ,
      linearFunctional_ofCharacter_unit]
  have hsq : LinearFunctional.convolution o o =
      LinearFunctional.ofCharacter
        (convolution (adjointCharacter ψ) ψ) := by
    rw [linearFunctional_ofCharacter_convolution, hadj_eq, ← hdec,
      LinearFunctional.convolution_assoc,
      ← LinearFunctional.convolution_assoc (LinearFunctional.leftInverse e)
        e o,
      he_inv_left, LinearFunctional.convolution_counit_left]
  exact sqrtFunctional_unique _ ho_norm hsq

/--
Uniqueness of the antisymmetric factor: if `ψ = e ⋆ o` with `e` even, `o` odd
and both normalized, then `e` is the antisymmetric component
(arXiv:2507.21006, Theorem 5.2, uniqueness).
-/
theorem antisymmetricPart_unique (ψ : Character R) {e o : LinearFunctional R}
    (he_norm : e (ofForest (R := R) 0) = 1)
    (ho_norm : o (ofForest (R := R) 0) = 1)
    (he : LinearFunctional.compGradingInvolution e = e)
    (ho : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution o) o =
      LinearFunctional.counit R)
    (hdec : LinearFunctional.convolution e o =
      LinearFunctional.ofCharacter ψ) :
    e = antisymmetricPart ψ := by
  have hoeq := symmetricPart_unique ψ he_norm ho_norm he ho hdec
  have ho2 : LinearFunctional.convolution o
      (LinearFunctional.compGradingInvolution o) =
      LinearFunctional.counit R := by
    have h1 : LinearFunctional.compGradingInvolution o =
        LinearFunctional.leftInverse o :=
      LinearFunctional.convolution_inverse_unique ho
        (LinearFunctional.convolution_leftInverse_right o ho_norm)
    rw [h1]
    exact LinearFunctional.convolution_leftInverse_right o ho_norm
  calc e = LinearFunctional.convolution e (LinearFunctional.counit R) :=
        (LinearFunctional.convolution_counit_right e).symm
    _ = LinearFunctional.convolution e (LinearFunctional.convolution o
          (LinearFunctional.compGradingInvolution o)) := by rw [ho2]
    _ = LinearFunctional.convolution (LinearFunctional.convolution e o)
          (LinearFunctional.compGradingInvolution o) :=
        (LinearFunctional.convolution_assoc _ _ _).symm
    _ = LinearFunctional.convolution (LinearFunctional.ofCharacter ψ)
          (LinearFunctional.compGradingInvolution (symmetricPart ψ)) := by
        rw [hdec, hoeq]
    _ = antisymmetricPart ψ := rfl

/-- Two characters are S-equivalent if they have the same symmetric
component (arXiv:2507.21006, Section 7). -/
def SEquiv (ζ ξ : Character R) : Prop :=
  symmetricPart ζ = symmetricPart ξ

theorem sEquiv_refl (ζ : Character R) : SEquiv ζ ζ :=
  rfl

theorem SEquiv.symm {ζ ξ : Character R} (h : SEquiv ζ ξ) : SEquiv ξ ζ :=
  Eq.symm h

theorem SEquiv.trans {ζ ξ η : Character R} (h₁ : SEquiv ζ ξ)
    (h₂ : SEquiv ξ η) : SEquiv ζ η :=
  Eq.trans h₁ h₂

/-- S-equivalence is precisely the kernel of the map `ψ ↦ ψ* ψ` on
characters (arXiv:2507.21006, Section 7). -/
theorem sEquiv_iff_adjoint_convolution_eq (ζ ξ : Character R) :
    SEquiv ζ ξ ↔
      convolution (adjointCharacter ζ) ζ =
        convolution (adjointCharacter ξ) ξ := by
  constructor
  · intro h
    apply linearFunctional_ofCharacter_injective
    rw [← convolution_symmetricPart ζ, ← convolution_symmetricPart ξ, h]
  · intro h
    rw [SEquiv, symmetricPart, symmetricPart, h]

/-- An odd (symmetric) character is its own symmetric component. -/
theorem symmetricPart_of_isOdd {ζ : Character R} (h : IsOdd ζ) :
    symmetricPart ζ = LinearFunctional.ofCharacter ζ := by
  have hone : LinearFunctional.ofCharacter ζ (ofForest (R := R) 0) = 1 := by
    change ζ (ofForest (R := R) 0) = 1
    rw [ofForest_zero]
    exact map_one ζ
  have hsq : LinearFunctional.convolution (LinearFunctional.ofCharacter ζ)
      (LinearFunctional.ofCharacter ζ) =
      LinearFunctional.ofCharacter (convolution (adjointCharacter ζ) ζ) := by
    rw [← linearFunctional_ofCharacter_convolution,
      (isOdd_iff_adjointCharacter_eq ζ).1 h]
  exact (sqrtFunctional_unique _ hone hsq).symm

/-- Every S-equivalence class contains at most one odd character: the
symmetric method is the unique symmetric element of its class
(arXiv:2507.21006, Section 7). -/
theorem isOdd_eq_of_sEquiv {ζ ξ : Character R} (hζ : IsOdd ζ)
    (hξ : IsOdd ξ) (h : SEquiv ζ ξ) : ζ = ξ := by
  apply linearFunctional_ofCharacter_injective
  rw [← symmetricPart_of_isOdd hζ, ← symmetricPart_of_isOdd hξ]
  exact h

/-- A character is S-equivalent to its own symmetric decomposition data:
`ψ ~ ζ` whenever `ζ` is odd with `ψ = e ⋆ ζ` for an even `e`. -/
theorem sEquiv_of_decomposition (ψ : Character R) {e : LinearFunctional R}
    {ζ : Character R} (hζ : IsOdd ζ)
    (he_norm : e (ofForest (R := R) 0) = 1)
    (he : LinearFunctional.compGradingInvolution e = e)
    (hdec : LinearFunctional.convolution e (LinearFunctional.ofCharacter ζ) =
      LinearFunctional.ofCharacter ψ) :
    SEquiv ψ ζ := by
  have ho_norm : LinearFunctional.ofCharacter ζ (ofForest (R := R) 0) = 1 := by
    change ζ (ofForest (R := R) 0) = 1
    rw [ofForest_zero]
    exact map_one ζ
  have ho : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution (LinearFunctional.ofCharacter ζ))
      (LinearFunctional.ofCharacter ζ) = LinearFunctional.counit R := by
    rw [← ofCharacter_involution, ← linearFunctional_ofCharacter_convolution]
    have hinv : involution ζ = inverseCharacter ζ :=
      linearFunctional_ofCharacter_injective (by
        rw [ofCharacter_inverseCharacter]
        exact hζ)
    rw [hinv, convolution_inverseCharacter_left,
      linearFunctional_ofCharacter_unit]
  have h1 := symmetricPart_unique ψ he_norm ho_norm he ho hdec
  rw [SEquiv, ← h1, symmetricPart_of_isOdd hζ]

end

end Character

end ForestAlgebra

namespace RootedForest

open HopfAlgebras.RootedForest

open ForestAlgebra

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- The convolution identity `σ ⋆ σ = ψ` in coefficient form. -/
private theorem sum_coproductTerms_sqrtCoeff (ψ : Character R)
    (φ : RootedForest) :
    ((coproductTerms φ).map fun term =>
      sqrtCoeff ψ term.1 * sqrtCoeff ψ term.2).sum = ψ.evalForest φ := by
  have h := congrArg (fun f : LinearFunctional R => f (ofForest (R := R) φ))
    (Character.convolution_sqrtFunctional ψ)
  simp only [LinearFunctional.convolution_ofForest,
    Character.sqrtFunctional_ofForest] at h
  exact h

private theorem sum_flatMap' {α β : Type _} [AddCommMonoid β]
    (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

omit [Invertible (2 : R)] in
private theorem sum_map_mul_sum_map {α β : Type _} (l₁ : List α)
    (l₂ : List β) (f : α → R) (g : β → R) :
    (l₁.map f).sum * (l₂.map g).sum =
      ((l₁.map fun x => ((l₂.map fun y => f x * g y)).sum)).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, add_mul, ih, List.map_cons,
        List.sum_cons, List.sum_map_mul_left]

omit [Invertible (2 : R)] in
/-- Splitting a sum over all cuts into the two boundary terms and the
proper part. -/
theorem sum_map_coproductTerms_split {φ : RootedForest} (hφ : φ ≠ 0)
    (F : RootedForest × RootedForest → R) :
    ((coproductTerms φ).map F).sum =
      F (0, φ) + F (φ, 0) +
      (((coproductTerms φ).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map F).sum := by
  obtain ⟨hl, hr⟩ := Character.coproductTerms_boundary_hyps (φ := φ) hφ
  have h := Character.sum_terms_eq_boundary_add_proper (φ := φ) hφ F
    (coproductTerms φ) hl hr
  rw [coproductTerms_leftBoundaryCoproductTerm,
    coproductTerms_rightBoundaryCoproductTerm] at h
  simpa using h

/--
**The convolution square root of a character is multiplicative**:
`σ(φ₁ φ₂) = σ(φ₁) σ(φ₂)`, so the square root of a character on the BCK Hopf
algebra is again a character (arXiv:2507.21006, Theorem 6.1).

Proof: compare the double cut sum `Σ_{x,y} σ(x₁+y₁)σ(x₂+y₂)` (which equals
`ψ(φ₁)ψ(φ₂)` via `Δ(φ₁φ₂) = Δφ₁·Δφ₂` and `σ⋆σ = ψ`) with its factored form
`Σ_{x,y} σ(x₁)σ(x₂)·σ(y₁)σ(y₂)` (which also equals `ψ(φ₁)ψ(φ₂)`); by strong
induction on the total order, the summands agree except at the two
double-boundary pairs, which contribute `2σ(φ₁+φ₂)` versus `2σ(φ₁)σ(φ₂)`.
-/
theorem sqrtCoeff_add (ψ : Character R) (φ₁ φ₂ : RootedForest) :
    sqrtCoeff ψ (φ₁ + φ₂) = sqrtCoeff ψ φ₁ * sqrtCoeff ψ φ₂ := by
  generalize hn : RootedForest.order φ₁ + RootedForest.order φ₂ = n
  induction n using Nat.strong_induction_on generalizing φ₁ φ₂ with
  | _ n ih =>
  by_cases h1 : φ₁ = 0
  · subst h1
    rw [zero_add, sqrtCoeff_zero, one_mul]
  by_cases h2 : φ₂ = 0
  · subst h2
    rw [add_zero, sqrtCoeff_zero, mul_one]
  subst hn
  have hIH : ∀ (a b : RootedForest),
      RootedForest.order a + RootedForest.order b <
        RootedForest.order φ₁ + RootedForest.order φ₂ →
      sqrtCoeff ψ (a + b) = sqrtCoeff ψ a * sqrtCoeff ψ b := fun a b hab =>
    ih _ hab a b rfl
  have hn₁ : 0 < RootedForest.order φ₁ :=
    (RootedForest.order_pos_iff_ne_zero φ₁).2 h1
  have hn₂ : 0 < RootedForest.order φ₂ :=
    (RootedForest.order_pos_iff_ne_zero φ₂).2 h2
  -- (I) the mixed double sum equals ψ(φ₁)ψ(φ₂)
  have hI : ((coproductTerms φ₁).map fun x =>
      ((coproductTerms φ₂).map fun y =>
        sqrtCoeff ψ (x.1 + y.1) * sqrtCoeff ψ (x.2 + y.2)).sum).sum =
      ψ.evalForest φ₁ * ψ.evalForest φ₂ := by
    have hperm := ((coproductTerms_add_perm φ₁ φ₂).map
      (fun term => sqrtCoeff ψ term.1 * sqrtCoeff ψ term.2)).sum_eq
    rw [sum_coproductTerms_sqrtCoeff, Character.evalForest_add] at hperm
    rw [hperm, PTree.multiplyCoproductTerms, List.map_flatMap, sum_flatMap']
    exact congrArg List.sum (List.map_congr_left fun x _ => by
      rw [List.map_map]
      rfl)
  -- (II) the factored double sum also equals ψ(φ₁)ψ(φ₂)
  have hII : ((coproductTerms φ₁).map fun x =>
      ((coproductTerms φ₂).map fun y =>
        (sqrtCoeff ψ x.1 * sqrtCoeff ψ x.2) *
          (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum).sum =
      ψ.evalForest φ₁ * ψ.evalForest φ₂ := by
    rw [← sum_coproductTerms_sqrtCoeff ψ φ₁,
      ← sum_coproductTerms_sqrtCoeff ψ φ₂, sum_map_mul_sum_map]
  -- inner sums coincide whenever `x` is a proper cut of `φ₁`
  have hproper_inner : ∀ x ∈ coproductTerms φ₁,
      0 < RootedForest.order x.1 → 0 < RootedForest.order x.2 →
      ((coproductTerms φ₂).map fun y =>
        sqrtCoeff ψ (x.1 + y.1) * sqrtCoeff ψ (x.2 + y.2)).sum =
      ((coproductTerms φ₂).map fun y =>
        (sqrtCoeff ψ x.1 * sqrtCoeff ψ x.2) *
          (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum := by
    intro x hx hx1 hx2
    have hxo := coproductTerms_order hx
    refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
    have hyo := coproductTerms_order hy
    rw [hIH x.1 y.1 (by omega), hIH x.2 y.2 (by omega)]
    ring
  -- inner comparison at the left boundary `x = (0, φ₁)`
  have e_left : ((coproductTerms φ₂).map fun y =>
        sqrtCoeff ψ ((0 : RootedForest) + y.1) *
          sqrtCoeff ψ (φ₁ + y.2)).sum +
        sqrtCoeff ψ φ₁ * sqrtCoeff ψ φ₂ =
      ((coproductTerms φ₂).map fun y =>
        (sqrtCoeff ψ (0 : RootedForest) * sqrtCoeff ψ φ₁) *
          (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum +
        sqrtCoeff ψ (φ₁ + φ₂) := by
    rw [sum_map_coproductTerms_split h2, sum_map_coproductTerms_split h2]
    have hfil : (((coproductTerms φ₂).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2).map fun y =>
          sqrtCoeff ψ ((0 : RootedForest) + y.1) *
            sqrtCoeff ψ (φ₁ + y.2)).sum =
        (((coproductTerms φ₂).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2).map fun y =>
          (sqrtCoeff ψ (0 : RootedForest) * sqrtCoeff ψ φ₁) *
            (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum := by
      refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
      obtain ⟨hym, hyp⟩ := List.mem_filter.1 hy
      have hyp' : 0 < RootedForest.order y.1 ∧
          0 < RootedForest.order y.2 := by
        simpa using hyp
      have hyo := coproductTerms_order hym
      rw [zero_add, hIH φ₁ y.2 (by omega), sqrtCoeff_zero]
      ring
    rw [hfil]
    simp only [zero_add, add_zero, sqrtCoeff_zero]
    ring
  -- inner comparison at the right boundary `x = (φ₁, 0)`
  have e_right : ((coproductTerms φ₂).map fun y =>
        sqrtCoeff ψ (φ₁ + y.1) *
          sqrtCoeff ψ ((0 : RootedForest) + y.2)).sum +
        sqrtCoeff ψ φ₁ * sqrtCoeff ψ φ₂ =
      ((coproductTerms φ₂).map fun y =>
        (sqrtCoeff ψ φ₁ * sqrtCoeff ψ (0 : RootedForest)) *
          (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum +
        sqrtCoeff ψ (φ₁ + φ₂) := by
    rw [sum_map_coproductTerms_split h2, sum_map_coproductTerms_split h2]
    have hfil : (((coproductTerms φ₂).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2).map fun y =>
          sqrtCoeff ψ (φ₁ + y.1) *
            sqrtCoeff ψ ((0 : RootedForest) + y.2)).sum =
        (((coproductTerms φ₂).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2).map fun y =>
          (sqrtCoeff ψ φ₁ * sqrtCoeff ψ (0 : RootedForest)) *
            (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum := by
      refine congrArg List.sum (List.map_congr_left fun y hy => ?_)
      obtain ⟨hym, hyp⟩ := List.mem_filter.1 hy
      have hyp' : 0 < RootedForest.order y.1 ∧
          0 < RootedForest.order y.2 := by
        simpa using hyp
      have hyo := coproductTerms_order hym
      rw [zero_add, hIH φ₁ y.1 (by omega), sqrtCoeff_zero]
      ring
    rw [hfil]
    simp only [zero_add, add_zero, sqrtCoeff_zero]
    ring
  -- assemble: split the outer sums at the boundaries of `φ₁`
  have houter : ((coproductTerms φ₁).map fun x =>
        ((coproductTerms φ₂).map fun y =>
          sqrtCoeff ψ (x.1 + y.1) * sqrtCoeff ψ (x.2 + y.2)).sum).sum +
        2 * (sqrtCoeff ψ φ₁ * sqrtCoeff ψ φ₂) =
      ((coproductTerms φ₁).map fun x =>
        ((coproductTerms φ₂).map fun y =>
          (sqrtCoeff ψ x.1 * sqrtCoeff ψ x.2) *
            (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum).sum +
        2 * sqrtCoeff ψ (φ₁ + φ₂) := by
    rw [sum_map_coproductTerms_split h1, sum_map_coproductTerms_split h1]
    have hfil : (((coproductTerms φ₁).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2).map fun x =>
          ((coproductTerms φ₂).map fun y =>
            sqrtCoeff ψ (x.1 + y.1) * sqrtCoeff ψ (x.2 + y.2)).sum).sum =
        (((coproductTerms φ₁).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2).map fun x =>
          ((coproductTerms φ₂).map fun y =>
            (sqrtCoeff ψ x.1 * sqrtCoeff ψ x.2) *
              (sqrtCoeff ψ y.1 * sqrtCoeff ψ y.2)).sum).sum := by
      refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
      obtain ⟨hxm, hxp⟩ := List.mem_filter.1 hx
      have hxp' : 0 < RootedForest.order x.1 ∧
          0 < RootedForest.order x.2 := by
        simpa using hxp
      exact hproper_inner x hxm hxp'.1 hxp'.2
    rw [hfil]
    linear_combination e_left + e_right
  -- conclude: `2σ(φ₁)σ(φ₂) = 2σ(φ₁+φ₂)`, cancel the invertible 2
  have h2eq : (2 : R) * (sqrtCoeff ψ φ₁ * sqrtCoeff ψ φ₂) =
      2 * sqrtCoeff ψ (φ₁ + φ₂) := by
    linear_combination houter - hI + hII
  simpa [invOf_mul_cancel_left'] using
    (congrArg (⅟(2 : R) * ·) h2eq).symm

end

end RootedForest

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

namespace Character

open HopfAlgebras.ForestAlgebra.Character

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- The square-root coefficients as a monoid homomorphism on forest
monomials, by `sqrtCoeff_add`. -/
def sqrtMonoidHom (ψ : Character R) : Multiplicative RootedForest →* R where
  toFun φ := RootedForest.sqrtCoeff ψ (Multiplicative.toAdd φ)
  map_one' := RootedForest.sqrtCoeff_zero ψ
  map_mul' _ _ := RootedForest.sqrtCoeff_add ψ _ _

/-- **The convolution square root of a character, as a character**: the
square root of a character on the BCK Hopf algebra is again a character
(arXiv:2507.21006, Theorem 6.1). -/
def sqrtCharacter (ψ : Character R) : Character R :=
  (AddMonoidAlgebra.lift R R RootedForest) (sqrtMonoidHom ψ)

@[simp]
theorem sqrtCharacter_evalForest (ψ : Character R) (φ : RootedForest) :
    (sqrtCharacter ψ).evalForest φ = RootedForest.sqrtCoeff ψ φ := by
  show sqrtCharacter ψ (ofForest (R := R) φ) = _
  rw [ofForest, sqrtCharacter]
  rw [AddMonoidAlgebra.lift_single]
  simp [sqrtMonoidHom]

/-- The character square root has the square-root functional as its
underlying linear functional. -/
theorem ofCharacter_sqrtCharacter (ψ : Character R) :
    LinearFunctional.ofCharacter (sqrtCharacter ψ) = sqrtFunctional ψ := by
  apply LinearFunctional.ext_evalForest
  intro φ
  rw [LinearFunctional.evalForest_ofCharacter, sqrtCharacter_evalForest]
  show _ = sqrtFunctional ψ (ofForest (R := R) φ)
  rw [sqrtFunctional_ofForest]

/-- `√ψ ⋆ √ψ = ψ` at the level of characters. -/
theorem convolution_sqrtCharacter_self (ψ : Character R) :
    convolution (sqrtCharacter ψ) (sqrtCharacter ψ) = ψ := by
  apply linearFunctional_ofCharacter_injective
  rw [linearFunctional_ofCharacter_convolution, ofCharacter_sqrtCharacter,
    convolution_sqrtFunctional]

omit [Invertible (2 : R)] in
private theorem character_norm_one (χ : Character R) :
    LinearFunctional.ofCharacter χ (ofForest (R := R) 0) = 1 := by
  show χ (ofForest (R := R) 0) = 1
  rw [ofForest_zero]
  exact map_one χ

/-- **Odd roots are odd**: the square root of an odd (symmetric) character
is again odd (arXiv:2507.21006, Proposition 6.2). -/
theorem isOdd_sqrtCharacter {ψ : Character R} (h : IsOdd ψ) :
    IsOdd (sqrtCharacter ψ) := by
  have hψinv : involution ψ = inverseCharacter ψ := by
    apply linearFunctional_ofCharacter_injective
    rw [ofCharacter_inverseCharacter]
    exact h
  -- both the involution and the inverse of `√ψ` square to `ψ⁻¹`
  have hsq₁ : LinearFunctional.convolution
      (LinearFunctional.ofCharacter (involution (sqrtCharacter ψ)))
      (LinearFunctional.ofCharacter (involution (sqrtCharacter ψ))) =
      LinearFunctional.ofCharacter (inverseCharacter ψ) := by
    rw [← linearFunctional_ofCharacter_convolution, ← involution_convolution,
      convolution_sqrtCharacter_self, hψinv]
  have hsq₂ : LinearFunctional.convolution
      (LinearFunctional.ofCharacter (inverseCharacter (sqrtCharacter ψ)))
      (LinearFunctional.ofCharacter (inverseCharacter (sqrtCharacter ψ))) =
      LinearFunctional.ofCharacter (inverseCharacter ψ) := by
    rw [← linearFunctional_ofCharacter_convolution,
      ← inverseCharacter_convolution, convolution_sqrtCharacter_self]
  -- square-root uniqueness identifies them
  have h₁ := sqrtFunctional_unique (inverseCharacter ψ)
    (character_norm_one (involution (sqrtCharacter ψ))) hsq₁
  have h₂ := sqrtFunctional_unique (inverseCharacter ψ)
    (character_norm_one (inverseCharacter (sqrtCharacter ψ))) hsq₂
  have heq : involution (sqrtCharacter ψ) =
      inverseCharacter (sqrtCharacter ψ) :=
    linearFunctional_ofCharacter_injective (h₁.trans h₂.symm)
  show LinearFunctional.ofCharacter (involution (sqrtCharacter ψ)) =
    LinearFunctional.compAntipode
      (LinearFunctional.ofCharacter (sqrtCharacter ψ))
  rw [heq, ofCharacter_inverseCharacter]

/-- **A B-series method is symmetric iff it factors as `Ω* ⋆ Ω`**
(arXiv:2507.21006, Theorem `thm:main`): a character is odd precisely when
it is the convolution of some character's adjoint with that character. -/
theorem isOdd_iff_exists_convolution_adjoint (ψ : Character R) :
    IsOdd ψ ↔ ∃ Ω : Character R,
      ψ = convolution (adjointCharacter Ω) Ω := by
  constructor
  · intro h
    refine ⟨sqrtCharacter ψ, ?_⟩
    rw [(isOdd_iff_adjointCharacter_eq (sqrtCharacter ψ)).1
      (isOdd_sqrtCharacter h), convolution_sqrtCharacter_self]
  · rintro ⟨Ω, rfl⟩
    exact isOdd_convolution_adjointCharacter Ω

end

noncomputable section

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

/-- **The symmetric component of a B-series method, as a character**:
`ψ⁻ := (ψ*⋆ψ)^{1/2}` is itself the character of a (symmetric) B-series
method (arXiv:2507.21006, Corollary 5.3 with Theorem 6.1). -/
noncomputable def symmetricPartChar (ψ : Character R) : Character R :=
  sqrtCharacter (convolution (adjointCharacter ψ) ψ)

/-- The character-level symmetric part has the symmetric-part functional
as its underlying linear functional. -/
theorem ofCharacter_symmetricPartChar (ψ : Character R) :
    LinearFunctional.ofCharacter (symmetricPartChar ψ) = symmetricPart ψ := by
  rw [symmetricPartChar, ofCharacter_sqrtCharacter, symmetricPart]

/-- **The symmetric component is a symmetric method**: `ψ⁻` is odd
(arXiv:2507.21006, Proposition 6.2 with Corollary 5.3). -/
theorem isOdd_symmetricPartChar (ψ : Character R) :
    IsOdd (symmetricPartChar ψ) :=
  isOdd_sqrtCharacter (isOdd_convolution_adjointCharacter ψ)

/-- The inverse of the symmetric component is its involution (it is odd). -/
theorem inverseCharacter_symmetricPartChar (ψ : Character R) :
    inverseCharacter (symmetricPartChar ψ) =
      involution (symmetricPartChar ψ) :=
  linearFunctional_ofCharacter_injective (by
    rw [ofCharacter_inverseCharacter]
    exact (isOdd_symmetricPartChar ψ).symm)

/-- **The antisymmetric component of a B-series method, as a character**:
`ψ⁺ := ψ ⋆ (ψ⁻)⁻¹` (arXiv:2507.21006, Corollary 5.3). -/
noncomputable def antisymmetricPartChar (ψ : Character R) : Character R :=
  convolution ψ (inverseCharacter (symmetricPartChar ψ))

/-- The character-level antisymmetric part has the antisymmetric-part
functional as its underlying linear functional. -/
theorem ofCharacter_antisymmetricPartChar (ψ : Character R) :
    LinearFunctional.ofCharacter (antisymmetricPartChar ψ) =
      antisymmetricPart ψ := by
  rw [antisymmetricPartChar, linearFunctional_ofCharacter_convolution,
    inverseCharacter_symmetricPartChar, ofCharacter_involution,
    ofCharacter_symmetricPartChar, antisymmetricPart]

end

end Character

end ForestAlgebra

end BSeries
