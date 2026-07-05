/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.AdjointScheme

/-!
# Stage relabelling and the antisymmetric two-stage family

Relabelling the stages of a Runge–Kutta tableau leaves all elementary
weights unchanged (P-equivalence; Butcher, *Numerical Methods for ODEs*,
Theorem 381H). As an application we construct the antisymmetric two-stage
family `Ω_λ` of arXiv:2507.21006, Section 7 — the tableau

  `A = [λ λ; -λ -λ]`, `b = (λ, -λ)` —

whose negation is a stage swap of itself, so its character is **even**.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w}

/-- Relabel the stages of a tableau along an equivalence. -/
def reindex (e : κ ≃ ι) (rk : RungeKutta ι R) : RungeKutta κ R where
  A i j := rk.A (e i) (e j)
  b j := rk.b (e j)

section Reindex

variable [Fintype ι] [Fintype κ] [CommSemiring R]

mutual

theorem stageWeight_reindex (e : κ ≃ ι) (rk : RungeKutta ι R) :
    ∀ (t : PTree) (i : κ),
      stageWeight (reindex e rk) t i = stageWeight rk t (e i)
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_reindex e rk ts i]

theorem stageWeightList_reindex (e : κ ≃ ι) (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (i : κ),
      stageWeightList (reindex e rk) ts i = stageWeightList rk ts (e i)
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_reindex e rk ts i]
      congr 1
      rw [← Equiv.sum_comp e fun j => rk.A (e i) j * stageWeight rk t j]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stageWeight_reindex e rk t j]
      rfl

end

/-- **Stage relabelling preserves the elementary weights**
(P-equivalence; Butcher, Theorem 381H). -/
theorem weight_reindex (e : κ ≃ ι) (rk : RungeKutta ι R) (t : PTree) :
    weight (reindex e rk) t = weight rk t := by
  rw [weight, weight, ← Equiv.sum_comp e fun i => rk.b i * stageWeight rk t i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stageWeight_reindex e rk t i]
  rfl

theorem treeWeight_reindex (e : κ ≃ ι) (rk : RungeKutta ι R)
    (τ : RootedTree) :
    treeWeight (reindex e rk) τ = treeWeight rk τ :=
  Quotient.inductionOn τ fun t => weight_reindex e rk t

end Reindex

section AntisymFamily

variable [CommRing R]

/-- The stage swap of a two-stage scheme. -/
def boolSwap : Bool ≃ Bool :=
  ⟨not, not, Bool.not_not, Bool.not_not⟩

/-- The antisymmetric two-stage tableau `Ω_λ` of arXiv:2507.21006,
Section 7: `A = [λ λ; -λ -λ]`, `b = (λ, -λ)`. -/
def antisymScheme (l : R) : RungeKutta Bool R where
  A i _ := if i then -l else l
  b j := if j then -l else l

/-- Negating `Ω_λ` is exactly the swap of its two stages. -/
theorem negScheme_antisymScheme (l : R) :
    negScheme (antisymScheme l) = reindex boolSwap (antisymScheme l) := by
  unfold negScheme antisymScheme reindex boolSwap
  congr 1
  · funext i j
    cases i <;> simp
  · funext j
    cases j <;> simp

/-- **The antisymmetric family is even**: the character of `Ω_λ` is fixed
by the canonical involution (arXiv:2507.21006, Section 7). -/
theorem isEven_toCharacter_antisymScheme (l : R) :
    ForestAlgebra.Character.IsEven
      (Series.toCharacter (series (antisymScheme l))) := by
  show ForestAlgebra.Character.involution
    (Series.toCharacter (series (antisymScheme l))) = _
  rw [show ForestAlgebra.Character.involution
      (Series.toCharacter (series (antisymScheme l))) =
      Series.toCharacter (series (negScheme (antisymScheme l))) from
    (toCharacter_series_negScheme (antisymScheme l)).symm]
  rw [negScheme_antisymScheme]
  apply ForestAlgebra.Character.ext_tree
  intro τ
  rw [toCharacter_series_evalForest, toCharacter_series_evalForest,
    forestWeight_singleton, forestWeight_singleton, treeWeight_reindex]

/-- The quadrature weights of `Ω_λ` sum to zero: `Ω_λ` is inconsistent
(a "do-nothing to first order" scheme). -/
theorem weightBullet_antisymScheme (l : R) :
    weight (antisymScheme l) PTree.bullet = 0 := by
  rw [weight_bullet, weightBullet]
  rw [Fintype.sum_bool]
  show -l + l = 0
  ring

/-- The elementary weight of the two-chain detects `λ`:
`ω_λ(chain₂) = 4λ²`. -/
theorem weight_chain2_antisymScheme (l : R) :
    weight (antisymScheme l) (PTree.node [PTree.node []]) = 4 * l ^ 2 := by
  rw [weight]
  rw [Fintype.sum_bool]
  have hsw : ∀ i : Bool, stageWeight (antisymScheme l)
      (PTree.node [PTree.node []]) i =
      (if i then -(2 * l) else 2 * l) := by
    intro i
    rw [stageWeight_node, stageWeightList_cons, stageWeightList_nil,
      mul_one]
    rw [Fintype.sum_bool]
    have hb : ∀ j : Bool, stageWeight (antisymScheme l)
        (PTree.node []) j = 1 := fun j => by
      rw [stageWeight_node, stageWeightList_nil]
    rw [hb true, hb false]
    cases i <;> simp [antisymScheme] <;> ring
  rw [hsw true, hsw false]
  show -l * -(2 * l) + l * (2 * l) = 4 * l ^ 2
  ring

end AntisymFamily

end RungeKutta

end BSeries
