/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.RungeKutta
import BSeries.Series.Convolution

/-!
# Composition of Runge–Kutta schemes

Butcher's composition theorem: running one Runge–Kutta scheme for a step and
then another corresponds, at the level of B-series, to the convolution
(Butcher group) product of their characters. The composed scheme is the block
tableau

  `A = [A₁ 0; 𝟙b₁ᵀ A₂]`, `b = (b₁, b₂)`,

and its elementary weights satisfy
`ψ_{comp} = ψ₁ ⋆ ψ₂` (Butcher, *Numerical Methods for ODEs*, Section 383;
Hairer–Lubich–Wanner III.1.4). The proof follows the stage-weight recursion:
first-block stages see only `rk₁`, while a second-block stage weight expands
as a sum over root-preserving cuts, pruned subtrees receiving the full `rk₁`
weight and the trunk evaluated by the `rk₂` stage recursion.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w}

/-- The block tableau composing two Runge–Kutta schemes: one step of `rk₁`
followed by one step of `rk₂`. -/
def compose [Zero R] (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    RungeKutta (ι ⊕ κ) R where
  A
    | .inl i, .inl j => rk₁.A i j
    | .inl _, .inr _ => 0
    | .inr _, .inl j => rk₁.b j
    | .inr i, .inr j => rk₂.A i j
  b
    | .inl j => rk₁.b j
    | .inr j => rk₂.b j

section

variable [Zero R] (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R)

@[simp]
theorem compose_A_inl_inl (i j : ι) :
    (compose rk₁ rk₂).A (.inl i) (.inl j) = rk₁.A i j := rfl

@[simp]
theorem compose_A_inl_inr (i : ι) (j : κ) :
    (compose rk₁ rk₂).A (.inl i) (.inr j) = 0 := rfl

@[simp]
theorem compose_A_inr_inl (i : κ) (j : ι) :
    (compose rk₁ rk₂).A (.inr i) (.inl j) = rk₁.b j := rfl

@[simp]
theorem compose_A_inr_inr (i j : κ) :
    (compose rk₁ rk₂).A (.inr i) (.inr j) = rk₂.A i j := rfl

@[simp]
theorem compose_b_inl (j : ι) :
    (compose rk₁ rk₂).b (.inl j) = rk₁.b j := rfl

@[simp]
theorem compose_b_inr (j : κ) :
    (compose rk₁ rk₂).b (.inr j) = rk₂.b j := rfl

end

variable [Fintype ι] [Fintype κ] [CommSemiring R]

private theorem sum_flatMap {α β : Type _} [AddCommMonoid β]
    (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

private theorem finsetSum_listSum {α β : Type _} [Fintype β]
    (l : List α) (f : β → α → R) :
    ∑ j : β, (l.map (f j)).sum = (l.map fun a => ∑ j : β, f j a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

mutual

/-- First-block stages of the composed scheme reproduce `rk₁`. -/
theorem stageWeight_compose_inl (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (t : PTree) (i : ι),
      stageWeight (compose rk₁ rk₂) t (.inl i) = stageWeight rk₁ t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_compose_inl rk₁ rk₂ ts i]

theorem stageWeightList_compose_inl
    (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (ts : List PTree) (i : ι),
      stageWeightList (compose rk₁ rk₂) ts (.inl i) =
        stageWeightList rk₁ ts i
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_compose_inl rk₁ rk₂ ts i]
      congr 1
      rw [Fintype.sum_sum_type]
      have h2 : ∑ j : κ, (compose rk₁ rk₂).A (.inl i) (.inr j) *
          stageWeight (compose rk₁ rk₂) t (.inr j) = 0 := by
        simp
      rw [h2, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [compose_A_inl_inl, stageWeight_compose_inl rk₁ rk₂ t j]

end

mutual

/-- **The key composition identity**: the stage weight of the composed
scheme at a second-block stage expands as a sum over root-preserving cuts,
with pruned subtrees receiving the full `rk₁` weight and the trunk evaluated
by `rk₂`. -/
theorem stageWeight_compose_inr (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (t : PTree) (i : κ),
      stageWeight (compose rk₁ rk₂) t (.inr i) =
        ((PTree.rootCuts t).map fun c =>
          weightList rk₁ c.pruned * stageWeight rk₂ c.trunk i).sum
  | .node ts, i => by
      rw [stageWeight_node, stageWeightList_compose_inr rk₁ rk₂ ts i,
        PTree.rootCuts, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
      simp only [Function.comp_apply, stageWeight_node]

theorem stageWeightList_compose_inr
    (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (ts : List PTree) (i : κ),
      stageWeightList (compose rk₁ rk₂) ts (.inr i) =
        ((PTree.rootCutsList ts).map fun c =>
          weightList rk₁ c.pruned * stageWeightList rk₂ c.trunks i).sum
  | [], i => by
      simp [weightList]
  | t :: ts, i => by
      rw [stageWeightList_cons, Fintype.sum_sum_type,
        stageWeightList_compose_inr rk₁ rk₂ ts i]
      have hfirst : ∑ j : ι, (compose rk₁ rk₂).A (.inr i) (.inl j) *
          stageWeight (compose rk₁ rk₂) t (.inl j) = weight rk₁ t := by
        rw [weight]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [compose_A_inr_inl, stageWeight_compose_inl rk₁ rk₂ t j]
      have hstep : ∀ j : κ, (compose rk₁ rk₂).A (.inr i) (.inr j) *
          stageWeight (compose rk₁ rk₂) t (.inr j) =
          ((PTree.rootCuts t).map fun c =>
            weightList rk₁ c.pruned *
              (rk₂.A i j * stageWeight rk₂ c.trunk j)).sum := fun j => by
        rw [compose_A_inr_inr, stageWeight_compose_inr rk₁ rk₂ t j,
          ← List.sum_map_mul_left]
        refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
        ring
      have hsecond : ∑ j : κ, (compose rk₁ rk₂).A (.inr i) (.inr j) *
          stageWeight (compose rk₁ rk₂) t (.inr j) =
          ((PTree.rootCuts t).map fun c =>
            weightList rk₁ c.pruned *
              ∑ j, rk₂.A i j * stageWeight rk₂ c.trunk j).sum := by
        rw [Finset.sum_congr rfl fun j _ => hstep j, finsetSum_listSum]
        refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
        rw [Finset.mul_sum]
      rw [hfirst, hsecond]
      -- reshape the sum over cuts of `t :: ts` into (choice for `t`) ×
      -- (cuts of `ts`)
      trans (weight rk₁ t * ((PTree.rootCutsList ts).map fun r =>
          weightList rk₁ r.pruned * stageWeightList rk₂ r.trunks i).sum +
        ((PTree.rootCuts t).map fun c =>
          weightList rk₁ c.pruned *
            ∑ j, rk₂.A i j * stageWeight rk₂ c.trunk j).sum *
          ((PTree.rootCutsList ts).map fun r =>
            weightList rk₁ r.pruned * stageWeightList rk₂ r.trunks i).sum)
      · ring
      symm
      rw [PTree.rootCutsList, PTree.childCuts, List.flatMap_cons,
        List.map_append, List.sum_append]
      congr 1
      · -- the edge-cutting choice contributes the full `rk₁` weight of `t`
        rw [List.map_map, ← List.sum_map_mul_left]
        refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
        simp only [Function.comp_apply, PTree.RootCutList.consChild,
          List.singleton_append, weightList_cons]
        ring
      · -- keeping `t` with a root cut links its trunk to an `rk₂` stage
        rw [List.map_flatMap, List.flatMap_map, sum_flatMap,
          ← List.sum_map_mul_right]
        refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
        rw [List.map_map, ← List.sum_map_mul_left]
        refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
        simp only [Function.comp_apply, PTree.RootCutList.consChild,
          weightList_append, stageWeightList_cons]
        ring

end

/-- The elementary weight of the composed scheme as a sum over child cuts:
pruned subtrees carry the full `rk₁` weight, the trunk carries the `rk₂`
weight (empty trunk contributing `1`). -/
theorem weight_compose (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R)
    (t : PTree) :
    weight (compose rk₁ rk₂) t =
      ((PTree.childCuts t).map fun c =>
        weightList rk₁ c.pruned * (c.trunk?.elim 1 (weight rk₂))).sum := by
  rw [weight, Fintype.sum_sum_type, PTree.childCuts, List.map_cons,
    List.sum_cons, List.map_map]
  have hfirst : ∑ j : ι, (compose rk₁ rk₂).b (.inl j) *
      stageWeight (compose rk₁ rk₂) t (.inl j) = weight rk₁ t := by
    rw [weight]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [compose_b_inl, stageWeight_compose_inl rk₁ rk₂ t j]
  have hsecond : ∑ j : κ, (compose rk₁ rk₂).b (.inr j) *
      stageWeight (compose rk₁ rk₂) t (.inr j) =
      ((PTree.rootCuts t).map fun c =>
        weightList rk₁ c.pruned * weight rk₂ c.trunk).sum := by
    have hstep : ∀ j : κ, (compose rk₁ rk₂).b (.inr j) *
        stageWeight (compose rk₁ rk₂) t (.inr j) =
        ((PTree.rootCuts t).map fun c =>
          weightList rk₁ c.pruned *
            (rk₂.b j * stageWeight rk₂ c.trunk j)).sum := fun j => by
      rw [compose_b_inr, stageWeight_compose_inr rk₁ rk₂ t j,
        ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
      ring
    rw [Finset.sum_congr rfl fun j _ => hstep j, finsetSum_listSum]
    refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
    rw [weight, Finset.mul_sum]
  rw [hfirst, hsecond]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp
  · exact congrArg List.sum (List.map_congr_left fun c _ => by simp)

/-- **Butcher's composition theorem** at the level of tree coefficients:
the elementary weight of the composed scheme is the convolution of the
two elementary weight characters. -/
theorem weight_compose_eq_convolutionCoeff
    (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) (t : PTree) :
    weight (compose rk₁ rk₂) t =
      PTree.convolutionCoeff (Series.toCharacter (series rk₁))
        (Series.toCharacter (series rk₂)) t := by
  rw [PTree.convolutionCoeff.eq_def,
    ← PTree.evalCoproductTerms_perm _ _ (PTree.childCuts_coproductTerms_perm t),
    weight_compose]
  simp only [PTree.evalCoproductTerms, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
  simp only [Function.comp_apply, PTree.evalCoproductTerm,
    PTree.ChildCut.coproductTerm, PTree.ChildCut.prunedForest,
    PTree.ChildCut.trunkForest]
  cases htr : c.trunk? with
  | none =>
      simp [Option.elim, ForestAlgebra.Character.evalForest,
        forestWeight_ofPTree_list]
  | some tr =>
      simp [Option.elim, ForestAlgebra.Character.evalForest,
        forestWeight_ofPTree_list, treeWeight_ofPTree]

/-- **Butcher's composition theorem**: the B-series character of a composed
Runge–Kutta scheme is the convolution (Butcher group) product of the two
schemes' characters (Butcher, *Numerical Methods for ODEs*, Theorem 383A;
Hairer–Lubich–Wanner III.1.4). -/
theorem toCharacter_series_compose
    (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    Series.toCharacter (series (compose rk₁ rk₂)) =
      ForestAlgebra.Character.convolution (Series.toCharacter (series rk₁))
        (Series.toCharacter (series rk₂)) := by
  apply ForestAlgebra.Character.ext_tree
  intro τ
  refine Quotient.inductionOn τ ?_
  intro t
  have hτ : (⟦t⟧ : RootedTree) = RootedTree.ofPTree t := rfl
  rw [hτ, ForestAlgebra.Character.convolution_evalForest,
    RootedForest.convolutionCoeff_singleton_ofPTree,
    toCharacter_series_evalForest, forestWeight_singleton, treeWeight_ofPTree,
    weight_compose_eq_convolutionCoeff]

end RungeKutta

end BSeries
