/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Composition
import BSeries.Series.ExactFlow

/-!
# The adjoint of a Runge–Kutta scheme at tableau level

The adjoint method of a Runge–Kutta scheme `(A, b)` is again a Runge–Kutta
scheme, with tableau `(𝟙bᵀ - A, b)`, i.e. `a*ᵢⱼ = bⱼ - aᵢⱼ`
(Hairer–Nørsett–Wanner, Theorem II.8.3; arXiv:2507.21006, Section 3).

The proof factors through two facts:
* negating the tableau corresponds to the canonical grading involution
  `ψ̄(τ) = (-1)^{|τ|} ψ(τ)` of the character (step reversal `h ↦ -h`), and
* the tableau `(A - 𝟙bᵀ, -b)` gives the convolution inverse of the
  character, proven by composing with the original scheme and checking the
  second-block stages collapse onto the first-block stages.

Combining, `adjointScheme = negScheme ∘ inverseScheme` realizes
`ψ* = (ψ⁻¹)̄` at the level of tableaux.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe u v

variable {ι : Type u} {R : Type v}

/-- The scheme with negated tableau: one step of size `-h`. -/
def negScheme [Neg R] (rk : RungeKutta ι R) : RungeKutta ι R where
  A i j := -rk.A i j
  b j := -rk.b j

/-- The scheme inverting one step of `rk`: tableau `(A - 𝟙bᵀ, -b)`. -/
def inverseScheme [Sub R] [Neg R] (rk : RungeKutta ι R) : RungeKutta ι R where
  A i j := rk.A i j - rk.b j
  b j := -rk.b j

/-- The adjoint scheme: tableau `(𝟙bᵀ - A, b)`, i.e. `a*ᵢⱼ = bⱼ - aᵢⱼ`
(Hairer–Nørsett–Wanner, Theorem II.8.3). -/
def adjointScheme [Sub R] (rk : RungeKutta ι R) : RungeKutta ι R where
  A i j := rk.b j - rk.A i j
  b j := rk.b j

section Apply

variable [Neg R] [Sub R] (rk : RungeKutta ι R)

omit [Sub R] in
@[simp]
theorem negScheme_A (i j : ι) : (negScheme rk).A i j = -rk.A i j := rfl

omit [Sub R] in
@[simp]
theorem negScheme_b (j : ι) : (negScheme rk).b j = -rk.b j := rfl

@[simp]
theorem inverseScheme_A (i j : ι) :
    (inverseScheme rk).A i j = rk.A i j - rk.b j := rfl

@[simp]
theorem inverseScheme_b (j : ι) : (inverseScheme rk).b j = -rk.b j := rfl

omit [Neg R] in
@[simp]
theorem adjointScheme_A (i j : ι) :
    (adjointScheme rk).A i j = rk.b j - rk.A i j := rfl

omit [Neg R] in
@[simp]
theorem adjointScheme_b (j : ι) : (adjointScheme rk).b j = rk.b j := rfl

end Apply

/-- The adjoint tableau is the negation of the inverting tableau. -/
theorem negScheme_inverseScheme [SubtractionMonoid R] (rk : RungeKutta ι R) :
    negScheme (inverseScheme rk) = adjointScheme rk := by
  unfold negScheme inverseScheme adjointScheme
  congr 1
  · funext i j
    exact neg_sub _ _
  · funext j
    exact neg_neg _

variable [Fintype ι] [CommRing R]

private theorem neg_one_pow_succ (n : ℕ) :
    ((-1 : R)) ^ (n + 1) = (-1) ^ n * (-1) :=
  pow_succ _ _

mutual

/-- Stage weights change sign according to the subtree order under tableau
negation. -/
theorem stageWeight_negScheme (rk : RungeKutta ι R) :
    ∀ (t : PTree) (i : ι),
      stageWeight (negScheme rk) t i =
        (-1) ^ (PTree.order t + 1) * stageWeight rk t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_negScheme rk ts i, PTree.order_node]
      rw [show 1 + PTree.orderList ts + 1 = PTree.orderList ts + 2 by omega,
        pow_add]
      norm_num

theorem stageWeightList_negScheme (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (i : ι),
      stageWeightList (negScheme rk) ts i =
        (-1) ^ (PTree.orderList ts) * stageWeightList rk ts i
  | [], i => by simp
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_negScheme rk ts i, PTree.orderList_cons, pow_add]
      have hj : ∀ j, (negScheme rk).A i j * stageWeight (negScheme rk) t j =
          (-1) ^ (PTree.order t) * (rk.A i j * stageWeight rk t j) := fun j => by
        rw [negScheme_A, stageWeight_negScheme rk t j, neg_one_pow_succ]
        ring
      rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
      ring

end

/-- Elementary weights change sign according to the tree order under tableau
negation: negating the tableau is a step of size `-h`. -/
theorem weight_negScheme (rk : RungeKutta ι R) (t : PTree) :
    weight (negScheme rk) t = (-1) ^ (PTree.order t) * weight rk t := by
  rw [weight, weight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [negScheme_b, stageWeight_negScheme rk t i, neg_one_pow_succ]
  ring

/-- Negating the tableau realizes the grading involution of the character. -/
theorem toCharacter_series_negScheme (rk : RungeKutta ι R) :
    Series.toCharacter (series (negScheme rk)) =
      ForestAlgebra.Character.involution (Series.toCharacter (series rk)) := by
  apply ForestAlgebra.Character.ext_tree
  intro τ
  refine Quotient.inductionOn τ ?_
  intro t
  have hτ : (⟦t⟧ : RootedTree) = RootedTree.ofPTree t := rfl
  rw [hτ, ForestAlgebra.Character.involution_evalForest,
    toCharacter_series_evalForest, toCharacter_series_evalForest,
    forestWeight_singleton, forestWeight_singleton, treeWeight_ofPTree,
    treeWeight_ofPTree, RootedForest.order_singleton,
    RootedTree.order_ofPTree, weight_negScheme]

mutual

/-- In the composition of a scheme with its inverting scheme, the
second-block stages collapse onto the first-block stages. -/
theorem stageWeight_compose_inverseScheme (rk : RungeKutta ι R) :
    ∀ (t : PTree) (i : ι),
      stageWeight (compose rk (inverseScheme rk)) t (.inr i) =
        stageWeight rk t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_compose_inverseScheme rk ts i]

theorem stageWeightList_compose_inverseScheme (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (i : ι),
      stageWeightList (compose rk (inverseScheme rk)) ts (.inr i) =
        stageWeightList rk ts i
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_compose_inverseScheme rk ts i]
      congr 1
      rw [Fintype.sum_sum_type]
      have h1 : ∀ j : ι, (compose rk (inverseScheme rk)).A (.inr i) (.inl j) *
          stageWeight (compose rk (inverseScheme rk)) t (.inl j) =
          rk.b j * stageWeight rk t j := fun j => by
        rw [compose_A_inr_inl, stageWeight_compose_inl]
      have h2 : ∀ j : ι, (compose rk (inverseScheme rk)).A (.inr i) (.inr j) *
          stageWeight (compose rk (inverseScheme rk)) t (.inr j) =
          (rk.A i j - rk.b j) * stageWeight rk t j := fun j => by
        rw [compose_A_inr_inr, inverseScheme_A,
          stageWeight_compose_inverseScheme rk t j]
      rw [Finset.sum_congr rfl fun j _ => h1 j,
        Finset.sum_congr rfl fun j _ => h2 j, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

end

/-- All elementary weights of the composed scheme `rk ∘ rk⁻¹` vanish: the
composition is the identity method. -/
theorem weight_compose_inverseScheme (rk : RungeKutta ι R) (t : PTree) :
    weight (compose rk (inverseScheme rk)) t = 0 := by
  rw [weight, Fintype.sum_sum_type]
  have h1 : ∀ j : ι, (compose rk (inverseScheme rk)).b (.inl j) *
      stageWeight (compose rk (inverseScheme rk)) t (.inl j) =
      rk.b j * stageWeight rk t j := fun j => by
    rw [compose_b_inl, stageWeight_compose_inl]
  have h2 : ∀ j : ι, (compose rk (inverseScheme rk)).b (.inr j) *
      stageWeight (compose rk (inverseScheme rk)) t (.inr j) =
      -rk.b j * stageWeight rk t j := fun j => by
    rw [compose_b_inr, inverseScheme_b,
      stageWeight_compose_inverseScheme rk t j]
  rw [Finset.sum_congr rfl fun j _ => h1 j,
    Finset.sum_congr rfl fun j _ => h2 j, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => by ring

/-- The inverting scheme is a right convolution inverse of the scheme. -/
theorem convolution_toCharacter_series_inverseScheme (rk : RungeKutta ι R) :
    ForestAlgebra.Character.convolution (Series.toCharacter (series rk))
        (Series.toCharacter (series (inverseScheme rk))) =
      ForestAlgebra.Character.unit R := by
  rw [← toCharacter_series_compose]
  apply ForestAlgebra.Character.ext_tree
  intro τ
  refine Quotient.inductionOn τ ?_
  intro t
  have hτ : (⟦t⟧ : RootedTree) = RootedTree.ofPTree t := rfl
  rw [hτ, ForestAlgebra.Character.unit_evalForest,
    toCharacter_series_evalForest, forestWeight_singleton, treeWeight_ofPTree,
    weight_compose_inverseScheme]
  classical
  simp [ForestAlgebra.counitCoeff, RootedForest.singleton_ne_zero]

/-- **The inverse method is a Runge–Kutta method**: the tableau
`(A - 𝟙bᵀ, -b)` realizes the convolution inverse of the character. -/
theorem toCharacter_series_inverseScheme (rk : RungeKutta ι R) :
    Series.toCharacter (series (inverseScheme rk)) =
      ForestAlgebra.Character.inverseCharacter
        (Series.toCharacter (series rk)) :=
  (ForestAlgebra.Character.convolution_inverse_unique
    (ForestAlgebra.Character.convolution_inverseCharacter_left _)
    (convolution_toCharacter_series_inverseScheme rk)).symm

/-- **The adjoint method is a Runge–Kutta method** (Hairer–Nørsett–Wanner,
Theorem II.8.3; arXiv:2507.21006, Section 3): the tableau `a*ᵢⱼ = bⱼ - aᵢⱼ`,
`b* = b` realizes the adjoint character `ψ*`. -/
theorem toCharacter_series_adjointScheme (rk : RungeKutta ι R) :
    Series.toCharacter (series (adjointScheme rk)) =
      ForestAlgebra.Character.adjointCharacter
        (Series.toCharacter (series rk)) := by
  rw [← negScheme_inverseScheme, toCharacter_series_negScheme,
    toCharacter_series_inverseScheme,
    ForestAlgebra.Character.adjointCharacter_eq_involution_inverseCharacter]

/-- **Composing a scheme with its adjoint yields a symmetric method**: the
character of `rk* ∘ rk` is odd (arXiv:2507.21006, Theorem `thm:main`, the
constructive direction, at tableau level). -/
theorem isOdd_toCharacter_series_compose_adjointScheme (rk : RungeKutta ι R) :
    ForestAlgebra.Character.IsOdd
      (Series.toCharacter (series (compose (adjointScheme rk) rk))) := by
  rw [toCharacter_series_compose, toCharacter_series_adjointScheme]
  exact ForestAlgebra.Character.isOdd_convolution_adjointCharacter _

/-- **A scheme and its adjoint have the same order**
(Hairer–Nørsett–Wanner, Theorem II.8.3; arXiv:2507.21006,
Proposition 7.1(1) at tableau level). -/
theorem hasOrder_adjointScheme_iff {ι : Type u} {R : Type v} [Fintype ι]
    [Field R] [CharZero R] (rk : RungeKutta ι R) (n : ℕ) :
    HasOrder (adjointScheme rk) n ↔ HasOrder rk n := by
  rw [hasOrder_iff_toCharacter_evalForest, hasOrder_iff_toCharacter_evalForest]
  have hex : ∀ φ : RootedForest,
      (Series.toCharacter (Series.exact R)).evalForest φ =
        (RootedForest.treeFactorial φ : R)⁻¹ := fun φ =>
    Series.toCharacter_exact_ofForest φ
  constructor
  · intro h φ hφ
    rw [← hex φ]
    refine (Series.adjointCharacter_agree_exact_iff
      (Series.toCharacter (series rk)) n).2 ?_ φ hφ
    intro φ' hφ'
    rw [← toCharacter_series_adjointScheme, hex φ']
    exact h φ' hφ'
  · intro h φ hφ
    rw [toCharacter_series_adjointScheme, ← hex φ]
    refine (Series.adjointCharacter_agree_exact_iff
      (Series.toCharacter (series rk)) n).1 ?_ φ hφ
    intro φ' hφ'
    rw [hex φ']
    exact h φ' hφ'

end RungeKutta

end BSeries
