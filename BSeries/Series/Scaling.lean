/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.ExactFlow

/-!
# Grading scalings and integer rescalings of the exact flow

The scaling `c_q : τ ↦ q^{|τ|} τ` of the forest algebra and the induced
rescaling of characters (arXiv:2507.21006, Proposition 7.1(2)). The exact
flow is invariant under substepping: the `n`-fold convolution power of the
exact character is the time-`n` flow, and rescaling it back by `1/n`
recovers the exact character — the identity `a_n = a` of the paper.
-/

namespace BSeries

open HopfAlgebras

universe u

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

noncomputable section

variable {R : Type u}

private def scalingMonoidHom (R : Type u) [CommSemiring R] (c : R) :
    Multiplicative RootedForest →* ForestAlgebra R where
  toFun φ :=
    (c ^ RootedForest.order (Multiplicative.toAdd φ)) •
      ofForest (R := R) (Multiplicative.toAdd φ)
  map_one' := by
    change (c ^ RootedForest.order 0) • ofForest (R := R) 0 = 1
    simp [RootedForest.order_zero]
  map_mul' φ ψ := by
    change
      (c ^
          RootedForest.order (Multiplicative.toAdd φ + Multiplicative.toAdd ψ)) •
        ofForest (R := R) (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) = _
    rw [RootedForest.order_add, pow_add, ofForest_add, smul_mul_smul_comm]

/-- The grading scaling `τ ↦ c^{|τ|} τ` of the forest algebra (the map
`c_q` of arXiv:2507.21006, Proposition 7.1). -/
def scalingHom [CommSemiring R] (c : R) :
    ForestAlgebra R →ₐ[R] ForestAlgebra R :=
  (AddMonoidAlgebra.lift R (ForestAlgebra R) RootedForest)
    (scalingMonoidHom R c)

@[simp]
theorem scalingHom_ofForest [CommSemiring R] (c : R) (φ : RootedForest) :
    scalingHom c (ofForest (R := R) φ) =
      (c ^ RootedForest.order φ) • ofForest (R := R) φ := by
  rw [ofForest, scalingHom, AddMonoidAlgebra.lift_single, one_smul]
  rfl

namespace Character

open HopfAlgebras.ForestAlgebra.Character

/-- Rescaling a character along the grading: `(χ_c)(τ) = c^{|τ|} χ(τ)`. -/
def scaling [CommSemiring R] (c : R) (χ : Character R) : Character R :=
  χ.comp (scalingHom c)

@[simp]
theorem scaling_evalForest [CommSemiring R] (c : R) (χ : Character R)
    (φ : RootedForest) :
    (scaling c χ).evalForest φ =
      c ^ RootedForest.order φ * χ.evalForest φ := by
  show χ (scalingHom c (ofForest (R := R) φ)) = _
  rw [scalingHom_ofForest, map_smul, smul_eq_mul]
  rfl

end Character

end

end ForestAlgebra

namespace Series

noncomputable section

variable {R : Type u}

/-- **The convolution powers of the exact flow are its time-`n` flows**:
`a^{⋆n} = a(nh)` (arXiv:2507.21006, Proposition 7.1(2), via the flow
property). -/
theorem convolutionPower_exact [Field R] [CharZero R] :
    ∀ n : ℕ, ForestAlgebra.LinearFunctional.convolutionPower
      (ForestAlgebra.LinearFunctional.ofCharacter (toCharacter (exact R)))
      n =
      ForestAlgebra.LinearFunctional.ofCharacter
        (toCharacter (scaledExact (n : R)))
  | 0 => by
      rw [ForestAlgebra.LinearFunctional.convolutionPower_zero]
      rw [show ((0 : ℕ) : R) = 0 from Nat.cast_zero, scaledExact_zero,
        toCharacter_unit]
      rw [← ForestAlgebra.Character.unit_eq_counit]
      exact (ForestAlgebra.Character.linearFunctional_ofCharacter_unit
        (R := R)).symm
  | n + 1 => by
      have ih : ForestAlgebra.LinearFunctional.convolutionPower
          (ForestAlgebra.LinearFunctional.ofCharacter
            (toCharacter (exact R))) n =
          ForestAlgebra.LinearFunctional.ofCharacter
            (toCharacter (scaledExact (n : R))) := convolutionPower_exact n
      rw [ForestAlgebra.LinearFunctional.convolutionPower_succ, ih,
        ← ForestAlgebra.Character.linearFunctional_ofCharacter_convolution,
        ← toCharacter_convolution]
      have h := convolution_scaledExact (1 : R) (n : R)
      rw [scaledExact_one] at h
      rw [h]
      congr 2
      push_cast
      ring_nf

/-- **The exact flow is invariant under substepping** (`a_n = a`,
arXiv:2507.21006, Proposition 7.1(2)): rescaling the time-`n` flow by
`1/n` recovers the exact character. -/
theorem scaling_inv_toCharacter_scaledExact [Field R] [CharZero R]
    {n : ℕ} (hn : n ≠ 0) :
    ForestAlgebra.Character.scaling ((n : R))⁻¹
        (toCharacter (scaledExact (n : R))) =
      toCharacter (exact R) := by
  apply ForestAlgebra.Character.ext
  intro φ
  rw [ForestAlgebra.Character.scaling_evalForest]
  rw [show (toCharacter (scaledExact (n : R))).evalForest φ =
    toCharacter (scaledExact (n : R))
      (ForestAlgebra.ofForest (R := R) φ) from rfl,
    toCharacter_scaledExact_ofForest]
  rw [show (toCharacter (exact R)).evalForest φ =
    toCharacter (exact R) (ForestAlgebra.ofForest (R := R) φ) from rfl,
    toCharacter_exact_ofForest]
  have hn' : ((n : R)) ≠ 0 := by exact_mod_cast hn
  rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hn'), one_mul]

end

end Series

end BSeries
