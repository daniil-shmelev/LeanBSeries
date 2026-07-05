/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.RungeKutta
import BSeries.Series.Labelled

/-!
# Labelled Runge-Kutta B-series

This file defines labelled elementary weights for additive, or coloured,
Runge-Kutta tableaus. The coefficients of a node are selected by its label.

## Main definitions

* `LabelledRungeKutta` - a labelled tableau with one `A` and `b` family per label
* `LabelledRungeKutta.stageWeight` - planar labelled stage weights
* `LabelledRungeKutta.treeWeight` - non-planar labelled tree weights
* `LabelledRungeKutta.series` - the induced labelled B-series
-/

namespace BSeries

open HopfAlgebras

open scoped BigOperators

universe u v w x

/-- A labelled Runge-Kutta tableau with stage type `ι`, labels `α`, and coefficients in `R`. -/
structure LabelledRungeKutta (α : Type u) (ι : Type v) (R : Type w) where
  A : α → ι → ι → R
  b : α → ι → R

namespace LabelledRungeKutta

variable {α : Type u} {ι : Type v} {R : Type w}

/-- Pull a labelled Runge-Kutta tableau back along a relabelling map. -/
def comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) : LabelledRungeKutta α ι R where
  A a := rk.A (f a)
  b a := rk.b (f a)

/-- Restrict a labelled Runge-Kutta tableau to one constant label. -/
def comapConstLabel (a : α) (rk : LabelledRungeKutta α ι R) : RungeKutta ι R where
  A := rk.A a
  b := rk.b a

@[simp]
theorem comapMapLabels_A {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (a : α) (i j : ι) :
    (comapMapLabels f rk).A a i j = rk.A (f a) i j :=
  rfl

@[simp]
theorem comapMapLabels_b {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (a : α) (i : ι) :
    (comapMapLabels f rk).b a i = rk.b (f a) i :=
  rfl

@[simp]
theorem comapConstLabel_A (a : α) (rk : LabelledRungeKutta α ι R) (i j : ι) :
    (comapConstLabel a rk).A i j = rk.A a i j :=
  rfl

@[simp]
theorem comapConstLabel_b (a : α) (rk : LabelledRungeKutta α ι R) (i : ι) :
    (comapConstLabel a rk).b i = rk.b a i :=
  rfl

section Semiring

variable [Fintype ι] [CommSemiring R]

/-- Label-dependent row sum `cᵢᵃ = ∑ⱼ Aᵃᵢⱼ`. -/
def abscissa (rk : LabelledRungeKutta α ι R) (a : α) (i : ι) : R :=
  ∑ j, rk.A a i j

@[simp]
theorem abscissa_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (a : α) (i : ι) :
    abscissa (comapMapLabels f rk) a i = abscissa rk (f a) i := by
  simp [abscissa]

@[simp]
theorem abscissa_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) (i : ι) :
    RungeKutta.abscissa (comapConstLabel a rk) i = abscissa rk a i := by
  simp [RungeKutta.abscissa, abscissa]

mutual

/-- Recursive stage weight of a planar labelled tree. -/
def stageWeight (rk : LabelledRungeKutta α ι R) : PLTree α → ι → R
  | .node _ ts, i => stageWeightList rk ts i

/-- Product of child contributions in the recursive labelled stage weight. -/
def stageWeightList (rk : LabelledRungeKutta α ι R) : List (PLTree α) → ι → R
  | [], _ => 1
  | t :: ts, i =>
      (∑ j, rk.A (PLTree.rootLabel t) i j * stageWeight rk t j) *
        stageWeightList rk ts i

end

@[simp]
theorem stageWeight_node (rk : LabelledRungeKutta α ι R) (a : α)
    (ts : List (PLTree α)) (i : ι) :
    stageWeight rk (.node a ts) i = stageWeightList rk ts i :=
  rfl

@[simp]
theorem stageWeightList_nil (rk : LabelledRungeKutta α ι R) (i : ι) :
    stageWeightList rk [] i = 1 :=
  rfl

@[simp]
theorem stageWeightList_cons (rk : LabelledRungeKutta α ι R)
    (t : PLTree α) (ts : List (PLTree α)) (i : ι) :
    stageWeightList rk (t :: ts) i =
      (∑ j, rk.A (PLTree.rootLabel t) i j * stageWeight rk t j) *
        stageWeightList rk ts i :=
  rfl

@[simp]
theorem stageWeight_singleton (rk : LabelledRungeKutta α ι R) (a : α) (i : ι) :
    stageWeight rk (.node a []) i = 1 := by
  simp

@[simp]
theorem stageWeightList_singleton (rk : LabelledRungeKutta α ι R) (a : α) (i : ι) :
    stageWeightList rk [.node a []] i = abscissa rk a i := by
  simp [abscissa]

@[simp]
theorem stageWeightList_append (rk : LabelledRungeKutta α ι R)
    (ts us : List (PLTree α)) (i : ι) :
    stageWeightList rk (ts ++ us) i =
      stageWeightList rk ts i * stageWeightList rk us i := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      simp [ih, mul_assoc]

theorem stageWeightList_perm (rk : LabelledRungeKutta α ι R) (i : ι)
    {ts us : List (PLTree α)} (h : ts.Perm us) :
    stageWeightList rk ts i = stageWeightList rk us i := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

mutual

theorem stageWeight_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) :
    ∀ (t : PLTree α) (i : ι),
      stageWeight (comapMapLabels f rk) t i =
        stageWeight rk (PLTree.map f t) i
  | .node _ ts, i => by
      simpa using stageWeightList_comapMapLabels f rk ts i

theorem stageWeightList_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) :
    ∀ (ts : List (PLTree α)) (i : ι),
      stageWeightList (comapMapLabels f rk) ts i =
        stageWeightList rk (ts.map (PLTree.map f)) i
  | [], _ => rfl
  | t :: ts, i => by
      simp [stageWeight_comapMapLabels f rk t, stageWeightList_comapMapLabels f rk ts i]

end

mutual

theorem stageWeight_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) :
    ∀ (t : PTree) (i : ι),
      RungeKutta.stageWeight (comapConstLabel a rk) t i =
        stageWeight rk (PLTree.constLabel a t) i
  | .node ts, i => by
      simpa using stageWeightList_comapConstLabel a rk ts i

theorem stageWeightList_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) :
    ∀ (ts : List PTree) (i : ι),
      RungeKutta.stageWeightList (comapConstLabel a rk) ts i =
        stageWeightList rk (ts.map (PLTree.constLabel a)) i
  | [], _ => rfl
  | t :: ts, i => by
      simp [stageWeight_comapConstLabel a rk t,
        stageWeightList_comapConstLabel a rk ts i]

end

mutual

/-- Stage weights are invariant under the labelled non-planar tree relation. -/
theorem stageWeight_perm (rk : LabelledRungeKutta α ι R) (i : ι) :
    ∀ {t u : PLTree α}, PLTree.Perm t u → stageWeight rk t i = stageWeight rk u i
  | _, _, .node hp hf => by
      exact (stageWeightList_perm rk i hp).trans (stageWeightList_eq_of_forall₂ rk i hf)

/-- Stage-weight products are invariant under elementwise equivalent child lists. -/
theorem stageWeightList_eq_of_forall₂ (rk : LabelledRungeKutta α ι R) (i : ι) :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ PLTree.Perm ts us →
      stageWeightList rk ts i = stageWeightList rk us i
  | _, _, .nil => rfl
  | t :: ts, u :: us, .cons h hs => by
      have hroot : PLTree.rootLabel t = PLTree.rootLabel u := PLTree.Perm.rootLabel_eq h
      have hhead :
          (∑ j, rk.A (PLTree.rootLabel t) i j * stageWeight rk t j) =
            ∑ j, rk.A (PLTree.rootLabel u) i j * stageWeight rk u j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hroot, stageWeight_perm rk j h]
      simp [hhead, stageWeightList_eq_of_forall₂ rk i hs]

end

/-- Elementary weight of a planar labelled rooted tree. -/
def weight (rk : LabelledRungeKutta α ι R) : PLTree α → R
  | .node a ts => ∑ i, rk.b a i * stageWeightList rk ts i

/-- Elementary weights are invariant under the labelled non-planar tree relation. -/
theorem weight_perm (rk : LabelledRungeKutta α ι R) :
    ∀ {t u : PLTree α}, PLTree.Perm t u → weight rk t = weight rk u
  | _, _, .node hp hf => by
      rename_i a ts us ts'
      have hlist :
          ∀ i, stageWeightList rk ts i = stageWeightList rk us i := fun i =>
        (stageWeightList_perm rk i hp).trans (stageWeightList_eq_of_forall₂ rk i hf)
      unfold weight
      apply Finset.sum_congr rfl
      intro i _
      rw [hlist i]

/-- Multiplicative extension of labelled elementary weights to planar forests. -/
def weightList (rk : LabelledRungeKutta α ι R) (ts : List (PLTree α)) : R :=
  (ts.map (weight rk)).prod

@[simp]
theorem weightList_nil (rk : LabelledRungeKutta α ι R) :
    weightList rk [] = 1 :=
  rfl

@[simp]
theorem weightList_cons (rk : LabelledRungeKutta α ι R)
    (t : PLTree α) (ts : List (PLTree α)) :
    weightList rk (t :: ts) = weight rk t * weightList rk ts :=
  rfl

@[simp]
theorem weightList_append (rk : LabelledRungeKutta α ι R)
    (ts us : List (PLTree α)) :
    weightList rk (ts ++ us) = weightList rk ts * weightList rk us := by
  simp [weightList, List.map_append]

theorem weightList_perm (rk : LabelledRungeKutta α ι R)
    {ts us : List (PLTree α)} (h : ts.Perm us) :
    weightList rk ts = weightList rk us := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem weight_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) :
    ∀ t : PLTree α, weight (comapMapLabels f rk) t = weight rk (PLTree.map f t)
  | .node _ ts => by
      simp [weight, stageWeightList_comapMapLabels f rk ts]

theorem weightList_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (ts : List (PLTree α)) :
    weightList (comapMapLabels f rk) ts =
      weightList rk (ts.map (PLTree.map f)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [weightList_cons, List.map_cons, weight_comapMapLabels f rk t, ih]

theorem weight_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) :
    ∀ t : PTree,
      RungeKutta.weight (comapConstLabel a rk) t =
        weight rk (PLTree.constLabel a t)
  | .node ts => by
      simp [RungeKutta.weight, weight, stageWeightList_comapConstLabel a rk ts]

theorem weightList_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) (ts : List PTree) :
    RungeKutta.weightList (comapConstLabel a rk) ts =
      weightList rk (ts.map (PLTree.constLabel a)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [RungeKutta.weightList_cons, weightList_cons, List.map_cons,
        weight_comapConstLabel a rk t, ih]

/-- Recursive stage weight of a non-planar labelled rooted tree. -/
def treeStageWeight (rk : LabelledRungeKutta α ι R)
    (τ : LRootedTree α) (i : ι) : R :=
  Quotient.lift (fun t => stageWeight rk t i) (fun _ _ h => stageWeight_perm rk i h) τ

@[simp]
theorem treeStageWeight_ofPLTree (rk : LabelledRungeKutta α ι R)
    (t : PLTree α) (i : ι) :
    treeStageWeight rk (LRootedTree.ofPLTree t) i = stageWeight rk t i :=
  rfl

private theorem treeStageWeight_out (rk : LabelledRungeKutta α ι R)
    (τ : LRootedTree α) (i : ι) :
    stageWeight rk (Quotient.out τ) i = treeStageWeight rk τ i := by
  rw [← treeStageWeight_ofPLTree rk (Quotient.out τ) i]
  rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]

theorem treeStageWeight_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (τ : LRootedTree α) (i : ι) :
    treeStageWeight (comapMapLabels f rk) τ i =
      treeStageWeight rk (LRootedTree.map f τ) i := by
  refine Quotient.inductionOn τ ?_
  intro t
  change
    stageWeight (comapMapLabels f rk) t i =
      treeStageWeight rk (LRootedTree.ofPLTree (PLTree.map f t)) i
  rw [treeStageWeight_ofPLTree]
  exact stageWeight_comapMapLabels f rk t i

theorem treeStageWeight_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) (τ : RootedTree) (i : ι) :
    RungeKutta.treeStageWeight (comapConstLabel a rk) τ i =
      treeStageWeight rk (LRootedTree.constLabel a τ) i := by
  refine Quotient.inductionOn τ ?_
  intro t
  change
    RungeKutta.stageWeight (comapConstLabel a rk) t i =
      treeStageWeight rk (LRootedTree.ofPLTree (PLTree.constLabel a t)) i
  rw [treeStageWeight_ofPLTree]
  exact stageWeight_comapConstLabel a rk t i

/-- Product of child stage contributions over a non-planar labelled rooted forest. -/
def forestStageWeight (rk : LabelledRungeKutta α ι R)
    (φ : LRootedForest α) (i : ι) : R :=
  (φ.map fun τ => ∑ j, rk.A (LRootedTree.rootLabel τ) i j * treeStageWeight rk τ j).prod

@[simp]
theorem forestStageWeight_zero (rk : LabelledRungeKutta α ι R) (i : ι) :
    forestStageWeight rk 0 i = 1 := by
  simp [forestStageWeight]

@[simp]
theorem forestStageWeight_empty (rk : LabelledRungeKutta α ι R) (i : ι) :
    forestStageWeight rk LRootedForest.empty i = 1 := by
  simp [LRootedForest.empty]

@[simp]
theorem forestStageWeight_singleton (rk : LabelledRungeKutta α ι R)
    (τ : LRootedTree α) (i : ι) :
    forestStageWeight rk (LRootedForest.singleton τ) i =
      ∑ j, rk.A (LRootedTree.rootLabel τ) i j * treeStageWeight rk τ j := by
  simp [forestStageWeight, LRootedForest.singleton]

@[simp]
theorem forestStageWeight_add (rk : LabelledRungeKutta α ι R)
    (φ ψ : LRootedForest α) (i : ι) :
    forestStageWeight rk (φ + ψ) i =
      forestStageWeight rk φ i * forestStageWeight rk ψ i := by
  simp [forestStageWeight, Multiset.map_add]

theorem forestStageWeight_ofPLTree_list (rk : LabelledRungeKutta α ι R) :
    ∀ (ts : List (PLTree α)) (i : ι),
      forestStageWeight rk ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) :
        LRootedForest α) i = stageWeightList rk ts i
  | [], _ => by
      simp [forestStageWeight]
  | t :: ts, i => by
      have htail :
          (List.map ((fun τ => ∑ j, rk.A (LRootedTree.rootLabel τ) i j *
              treeStageWeight rk τ j) ∘ LRootedTree.ofPLTree) ts).prod =
            stageWeightList rk ts i := by
        simpa [forestStageWeight] using forestStageWeight_ofPLTree_list rk ts i
      simp [forestStageWeight, htail]

theorem forestStageWeight_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (φ : LRootedForest α) (i : ι) :
    forestStageWeight (comapMapLabels f rk) φ i =
      forestStageWeight rk (LRootedForest.mapLabels f φ) i := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestStageWeight, LRootedForest.mapLabels]
  | cons τ ts ih =>
      have htail :
          (List.map
              (fun x =>
                ∑ j, rk.A (f (LRootedTree.rootLabel x)) i j *
                  treeStageWeight rk (LRootedTree.map f x) j) ts).prod =
            (List.map
              ((fun τ => ∑ j, rk.A (LRootedTree.rootLabel τ) i j *
                treeStageWeight rk τ j) ∘ LRootedTree.map f) ts).prod := by
        apply congrArg List.prod
        apply List.map_congr_left
        intro σ _hσ
        simp [LRootedTree.rootLabel_map]
      simp [forestStageWeight, LRootedForest.mapLabels, LRootedTree.rootLabel_map,
        treeStageWeight_comapMapLabels f rk, htail]

theorem forestStageWeight_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) (φ : RootedForest) (i : ι) :
    RungeKutta.forestStageWeight (comapConstLabel a rk) φ i =
      forestStageWeight rk (LRootedForest.constLabel a φ) i := by
  simp only [RungeKutta.forestStageWeight, forestStageWeight, LRootedForest.constLabel,
    Multiset.map_map, Function.comp_apply, comapConstLabel_A,
    treeStageWeight_comapConstLabel a rk, LRootedTree.rootLabel_constLabel]

private theorem rootLabel_out (τ : LRootedTree α) :
    PLTree.rootLabel (Quotient.out τ) = LRootedTree.rootLabel τ := by
  rw [← LRootedTree.rootLabel_ofPLTree (Quotient.out τ)]
  rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]

private theorem stageWeightList_out (rk : LabelledRungeKutta α ι R) :
    ∀ (ts : List (LRootedTree α)) (i : ι),
      stageWeightList rk (ts.map Quotient.out) i =
        forestStageWeight rk (ts : LRootedForest α) i
  | [], _ => by
      simp [forestStageWeight]
  | τ :: ts, i => by
      simp [forestStageWeight, rootLabel_out τ, treeStageWeight_out rk τ,
        stageWeightList_out rk ts i]

@[simp]
theorem treeStageWeight_graft (rk : LabelledRungeKutta α ι R)
    (a : α) (φ : LRootedForest α) (i : ι) :
    treeStageWeight rk (LRootedForest.graft a φ) i = forestStageWeight rk φ i := by
  refine Quotient.inductionOn φ ?_
  intro ts
  simpa [LRootedForest.graft] using stageWeightList_out rk ts i

@[simp]
theorem treeStageWeight_branches (rk : LabelledRungeKutta α ι R)
    (τ : LRootedTree α) (i : ι) :
    treeStageWeight rk τ i = forestStageWeight rk (LRootedTree.branches τ) i := by
  calc
    treeStageWeight rk τ i =
        treeStageWeight rk
          (LRootedForest.graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ)) i := by
          rw [LRootedForest.graft_branches τ]
    _ = forestStageWeight rk (LRootedTree.branches τ) i := by
          rw [treeStageWeight_graft]

@[simp]
theorem treeStageWeight_butcherProduct (rk : LabelledRungeKutta α ι R)
    (φ : LRootedForest α) (τ : LRootedTree α) (i : ι) :
    treeStageWeight rk (LRootedForest.butcherProduct φ τ) i =
      forestStageWeight rk φ i * treeStageWeight rk τ i := by
  rw [LRootedForest.butcherProduct, treeStageWeight_graft, forestStageWeight_add,
    ← treeStageWeight_branches]

/-- Elementary weight of a non-planar labelled rooted tree. -/
def treeWeight (rk : LabelledRungeKutta α ι R) (τ : LRootedTree α) : R :=
  Quotient.lift (weight rk) (fun _ _ h => weight_perm rk h) τ

@[simp]
theorem treeWeight_ofPLTree (rk : LabelledRungeKutta α ι R) (t : PLTree α) :
    treeWeight rk (LRootedTree.ofPLTree t) = weight rk t :=
  rfl

theorem treeWeight_eq_sum_treeStageWeight (rk : LabelledRungeKutta α ι R)
    (τ : LRootedTree α) :
    treeWeight rk τ =
      ∑ i, rk.b (LRootedTree.rootLabel τ) i * treeStageWeight rk τ i := by
  refine Quotient.inductionOn τ ?_
  intro t
  cases t
  rfl

theorem treeWeight_graft (rk : LabelledRungeKutta α ι R)
    (a : α) (φ : LRootedForest α) :
    treeWeight rk (LRootedForest.graft a φ) =
      ∑ i, rk.b a i * forestStageWeight rk φ i := by
  refine Quotient.inductionOn φ ?_
  intro ts
  change
    (∑ i, rk.b a i * stageWeightList rk (ts.map Quotient.out) i) =
      ∑ i, rk.b a i * forestStageWeight rk (ts : LRootedForest α) i
  apply Finset.sum_congr rfl
  intro i _
  rw [stageWeightList_out rk ts i]

theorem treeWeight_branches (rk : LabelledRungeKutta α ι R) (τ : LRootedTree α) :
    treeWeight rk τ =
      ∑ i, rk.b (LRootedTree.rootLabel τ) i *
        forestStageWeight rk (LRootedTree.branches τ) i := by
  calc
    treeWeight rk τ =
        treeWeight rk
          (LRootedForest.graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ)) := by
          rw [LRootedForest.graft_branches τ]
    _ = ∑ i, rk.b (LRootedTree.rootLabel τ) i *
        forestStageWeight rk (LRootedTree.branches τ) i :=
          treeWeight_graft rk (LRootedTree.rootLabel τ) (LRootedTree.branches τ)

theorem treeWeight_butcherProduct (rk : LabelledRungeKutta α ι R)
    (φ : LRootedForest α) (τ : LRootedTree α) :
    treeWeight rk (LRootedForest.butcherProduct φ τ) =
      ∑ i, rk.b (LRootedTree.rootLabel τ) i *
        (forestStageWeight rk φ i * treeStageWeight rk τ i) := by
  rw [treeWeight_eq_sum_treeStageWeight]
  apply Finset.sum_congr rfl
  intro i _
  rw [LRootedForest.rootLabel_butcherProduct, treeStageWeight_butcherProduct]

theorem treeWeight_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (τ : LRootedTree α) :
    treeWeight (comapMapLabels f rk) τ =
      treeWeight rk (LRootedTree.map f τ) := by
  refine Quotient.inductionOn τ ?_
  intro t
  change
    weight (comapMapLabels f rk) t =
      treeWeight rk (LRootedTree.ofPLTree (PLTree.map f t))
  rw [treeWeight_ofPLTree]
  exact weight_comapMapLabels f rk t

theorem treeWeight_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) (τ : RootedTree) :
    RungeKutta.treeWeight (comapConstLabel a rk) τ =
      treeWeight rk (LRootedTree.constLabel a τ) := by
  refine Quotient.inductionOn τ ?_
  intro t
  change
    RungeKutta.weight (comapConstLabel a rk) t =
      treeWeight rk (LRootedTree.ofPLTree (PLTree.constLabel a t))
  rw [treeWeight_ofPLTree]
  exact weight_comapConstLabel a rk t

/-- Multiplicative extension of labelled elementary weights to non-planar labelled forests. -/
def forestWeight (rk : LabelledRungeKutta α ι R) (φ : LRootedForest α) : R :=
  (φ.map (treeWeight rk)).prod

@[simp]
theorem forestWeight_zero (rk : LabelledRungeKutta α ι R) :
    forestWeight rk 0 = 1 := by
  simp [forestWeight]

@[simp]
theorem forestWeight_empty (rk : LabelledRungeKutta α ι R) :
    forestWeight rk LRootedForest.empty = 1 := by
  simp [LRootedForest.empty]

@[simp]
theorem forestWeight_singleton (rk : LabelledRungeKutta α ι R)
    (τ : LRootedTree α) :
    forestWeight rk (LRootedForest.singleton τ) = treeWeight rk τ := by
  simp [forestWeight, LRootedForest.singleton]

@[simp]
theorem forestWeight_add (rk : LabelledRungeKutta α ι R)
    (φ ψ : LRootedForest α) :
    forestWeight rk (φ + ψ) = forestWeight rk φ * forestWeight rk ψ := by
  simp [forestWeight, Multiset.map_add]

theorem forestWeight_ofPLTree_list (rk : LabelledRungeKutta α ι R) :
    ∀ ts : List (PLTree α),
      forestWeight rk ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) :
        LRootedForest α) = weightList rk ts
  | [] => by
      simp [forestWeight]
  | t :: ts => by
      have htail :
          (List.map (treeWeight rk ∘ LRootedTree.ofPLTree) ts).prod =
          weightList rk ts := by
        simpa [forestWeight] using forestWeight_ofPLTree_list rk ts
      simp [forestWeight, htail]

theorem forestWeight_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) (φ : LRootedForest α) :
    forestWeight (comapMapLabels f rk) φ =
      forestWeight rk (LRootedForest.mapLabels f φ) := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestWeight, LRootedForest.mapLabels]
  | cons τ ts ih =>
      have htail :
          (List.map (fun x => treeWeight rk (LRootedTree.map f x)) ts).prod =
            (List.map (treeWeight rk ∘ LRootedTree.map f) ts).prod := by
        apply congrArg List.prod
        apply List.map_congr_left
        intro σ _hσ
        rfl
      simp [forestWeight, LRootedForest.mapLabels, treeWeight_comapMapLabels f rk,
        htail]

theorem forestWeight_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) (φ : RootedForest) :
    RungeKutta.forestWeight (comapConstLabel a rk) φ =
      forestWeight rk (LRootedForest.constLabel a φ) := by
  simp only [RungeKutta.forestWeight, forestWeight, LRootedForest.constLabel,
    Multiset.map_map, Function.comp_apply, treeWeight_comapConstLabel a rk]

/-- The labelled B-series induced by a labelled Runge-Kutta tableau. -/
def series (rk : LabelledRungeKutta α ι R) : LSeries α R
  | .empty => 1
  | .tree τ => treeWeight rk τ

@[simp]
theorem series_apply_empty (rk : LabelledRungeKutta α ι R) :
    series rk .empty = 1 :=
  rfl

@[simp]
theorem series_apply_tree (rk : LabelledRungeKutta α ι R) (τ : LRootedTree α) :
    series rk (.tree τ) = treeWeight rk τ :=
  rfl

theorem series_butcherProduct (rk : LabelledRungeKutta α ι R)
    (φ : LRootedForest α) (τ : LRootedTree α) :
    LSeries.coeff (series rk) (.tree (LRootedForest.butcherProduct φ τ)) =
      ∑ i, rk.b (LRootedTree.rootLabel τ) i *
        (forestStageWeight rk φ i * treeStageWeight rk τ i) := by
  simpa [LSeries.coeff] using treeWeight_butcherProduct rk φ τ

theorem series_graft (rk : LabelledRungeKutta α ι R)
    (a : α) (φ : LRootedForest α) :
    LSeries.coeff (series rk) (.tree (LRootedForest.graft a φ)) =
      ∑ i, rk.b a i * forestStageWeight rk φ i := by
  simpa [LSeries.coeff] using treeWeight_graft rk a φ

theorem series_branches (rk : LabelledRungeKutta α ι R) (τ : LRootedTree α) :
    LSeries.coeff (series rk) (.tree τ) =
      ∑ i, rk.b (LRootedTree.rootLabel τ) i *
        forestStageWeight rk (LRootedTree.branches τ) i := by
  simpa [LSeries.coeff] using treeWeight_branches rk τ

theorem series_hasUnitConstant (rk : LabelledRungeKutta α ι R) :
    LSeries.HasUnitConstant (series rk) :=
  rfl

theorem series_comapMapLabels {β : Type x} (f : α → β)
    (rk : LabelledRungeKutta β ι R) :
    series (comapMapLabels f rk) = LSeries.comapMapLabels f (series rk) := by
  funext τ
  cases τ with
  | empty => rfl
  | tree τ =>
      simp [series, LSeries.comapMapLabels, LTreeIndex.mapLabels,
        treeWeight_comapMapLabels f rk]

theorem series_comapConstLabel (a : α)
    (rk : LabelledRungeKutta α ι R) :
    RungeKutta.series (comapConstLabel a rk) =
      LSeries.comapConstLabel a (series rk) := by
  funext τ
  cases τ with
  | empty => rfl
  | tree τ =>
      simp [RungeKutta.series, LSeries.comapConstLabel, LTreeIndex.constLabel,
        series, treeWeight_comapConstLabel a rk]

@[simp]
theorem forestCoeff_series (rk : LabelledRungeKutta α ι R) (φ : LRootedForest α) :
    LSeries.forestCoeff (series rk) φ = forestWeight rk φ := by
  simp [LSeries.forestCoeff, forestWeight, series]

@[simp]
theorem toCharacter_series_evalForest (rk : LabelledRungeKutta α ι R)
    (φ : LRootedForest α) :
    (LSeries.toCharacter (series rk)).evalForest φ = forestWeight rk φ := by
  simp [LForestAlgebra.Character.evalForest]

@[simp]
theorem toCharacter_series_ofForest (rk : LabelledRungeKutta α ι R)
    (φ : LRootedForest α) :
    LSeries.toCharacter (series rk) (LForestAlgebra.ofForest (R := R) φ) =
      forestWeight rk φ := by
  simp

/-- Two labelled Runge-Kutta tableaux have matching labelled B-series coefficients
through order `n`. -/
def AgreeUpToOrder {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R)
    (n : Nat) : Prop :=
  LSeries.AgreeUpToOrder (series rk) (series rk') n

theorem agreeUpToOrder_refl (rk : LabelledRungeKutta α ι R) (n : Nat) :
    AgreeUpToOrder rk rk n :=
  LSeries.agreeUpToOrder_refl (series rk) n

theorem AgreeUpToOrder.symm {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) :
    AgreeUpToOrder rk' rk n :=
  LSeries.AgreeUpToOrder.symm h

theorem AgreeUpToOrder.trans {κ η : Type v} [Fintype κ] [Fintype η]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R}
    {rk'' : LabelledRungeKutta α η R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) (h' : AgreeUpToOrder rk' rk'' n) :
    AgreeUpToOrder rk rk'' n :=
  LSeries.AgreeUpToOrder.trans h h'

theorem AgreeUpToOrder.mono {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R}
    {m n : Nat} (h : AgreeUpToOrder rk rk' n) (hmn : m ≤ n) :
    AgreeUpToOrder rk rk' m :=
  LSeries.AgreeUpToOrder.mono h hmn

theorem agreeUpToOrder_iff_treeWeight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ τ : LRootedTree α, LRootedTree.order τ ≤ n →
        treeWeight rk τ = treeWeight rk' τ := by
  constructor
  · intro h τ hτ
    simpa [AgreeUpToOrder, LSeries.coeff] using h (.tree τ) hτ
  · intro h ξ hξ
    cases ξ with
    | empty =>
        rfl
    | tree τ =>
        simpa [AgreeUpToOrder, LSeries.coeff] using h τ hξ

theorem agreeUpToOrder_iff_weight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ t : PLTree α, PLTree.order t ≤ n → weight rk t = weight rk' t := by
  rw [agreeUpToOrder_iff_treeWeight]
  constructor
  · intro h t ht
    simpa using h (LRootedTree.ofPLTree t) ht
  · intro h τ hτ
    let t := Quotient.out τ
    have htout : LRootedTree.ofPLTree t = τ := Quotient.out_eq τ
    have htorder : PLTree.order t ≤ n := by
      have : LRootedTree.order (LRootedTree.ofPLTree t) ≤ n := by
        simpa [htout] using hτ
      simpa using this
    calc
      treeWeight rk τ = treeWeight rk (LRootedTree.ofPLTree t) := by rw [htout]
      _ = weight rk t := rfl
      _ = weight rk' t := h t htorder
      _ = treeWeight rk' (LRootedTree.ofPLTree t) := rfl
      _ = treeWeight rk' τ := by rw [htout]

theorem agreeUpToOrder_iff_forestCoeff {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        LSeries.forestCoeff (series rk) φ = LSeries.forestCoeff (series rk') φ := by
  rw [AgreeUpToOrder, LSeries.agreeUpToOrder_iff_forestCoeff]
  constructor
  · intro h φ hφ
    exact h.2 φ hφ
  · intro h
    exact ⟨by rfl, h⟩

theorem agreeUpToOrder_iff_forestWeight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        forestWeight rk φ = forestWeight rk' φ := by
  rw [agreeUpToOrder_iff_forestCoeff]
  simp

theorem agreeUpToOrder_iff_toCharacter_evalForest {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        (LSeries.toCharacter (series rk)).evalForest φ =
          (LSeries.toCharacter (series rk')).evalForest φ := by
  rw [agreeUpToOrder_iff_forestWeight]
  simp

theorem AgreeUpToOrder.treeWeight {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {τ : LRootedTree α}
    (hτ : LRootedTree.order τ ≤ n) :
    treeWeight rk τ = treeWeight rk' τ :=
  (agreeUpToOrder_iff_treeWeight rk rk' n).1 h τ hτ

theorem AgreeUpToOrder.weight {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {t : PLTree α} (ht : PLTree.order t ≤ n) :
    weight rk t = weight rk' t :=
  (agreeUpToOrder_iff_weight rk rk' n).1 h t ht

theorem AgreeUpToOrder.forestWeight {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {φ : LRootedForest α}
    (hφ : LRootedForest.order φ ≤ n) :
    forestWeight rk φ = forestWeight rk' φ :=
  (agreeUpToOrder_iff_forestWeight rk rk' n).1 h φ hφ

theorem AgreeUpToOrder.toCharacter_evalForest {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {φ : LRootedForest α}
    (hφ : LRootedForest.order φ ≤ n) :
    (LSeries.toCharacter (series rk)).evalForest φ =
      (LSeries.toCharacter (series rk')).evalForest φ :=
  (agreeUpToOrder_iff_toCharacter_evalForest rk rk' n).1 h φ hφ

theorem agreeUpToOrder_succ_iff_treeWeight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) (n : Nat) :
    AgreeUpToOrder rk rk' (n + 1) ↔
      AgreeUpToOrder rk rk' n ∧
        ∀ τ : LRootedTree α, LRootedTree.order τ = n + 1 →
          treeWeight rk τ = treeWeight rk' τ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun τ hτ => h.treeWeight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [agreeUpToOrder_iff_treeWeight]
    intro τ hτ
    by_cases hle : LRootedTree.order τ ≤ n
    · exact hprev.treeWeight hle
    · exact htop τ (by omega)

theorem agreeUpToOrder_succ_iff_weight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) (n : Nat) :
    AgreeUpToOrder rk rk' (n + 1) ↔
      AgreeUpToOrder rk rk' n ∧
        ∀ t : PLTree α, PLTree.order t = n + 1 → weight rk t = weight rk' t := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun t ht => h.weight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [agreeUpToOrder_iff_weight]
    intro t ht
    by_cases hle : PLTree.order t ≤ n
    · exact hprev.weight hle
    · exact htop t (by omega)

theorem agreeUpToOrder_all_iff_series_eq {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔ series rk = series rk' := by
  change (∀ n, LSeries.AgreeUpToOrder (series rk) (series rk') n) ↔
    series rk = series rk'
  exact LSeries.agreeUpToOrder_all_iff_eq

theorem agreeUpToOrder_all_iff_treeWeight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ τ : LRootedTree α, treeWeight rk τ = treeWeight rk' τ := by
  constructor
  · intro h τ
    exact (h (LRootedTree.order τ)).treeWeight le_rfl
  · intro h n
    rw [agreeUpToOrder_iff_treeWeight]
    intro τ _hτ
    exact h τ

theorem agreeUpToOrder_all_iff_weight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ t : PLTree α, weight rk t = weight rk' t := by
  constructor
  · intro h t
    exact (h (PLTree.order t)).weight le_rfl
  · intro h n
    rw [agreeUpToOrder_iff_weight]
    intro t _ht
    exact h t

theorem agreeUpToOrder_all_iff_forestWeight {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ φ : LRootedForest α, forestWeight rk φ = forestWeight rk' φ := by
  constructor
  · intro h φ
    exact (h (LRootedForest.order φ)).forestWeight le_rfl
  · intro h n
    rw [agreeUpToOrder_iff_forestWeight]
    intro φ _hφ
    exact h φ

theorem agreeUpToOrder_all_iff_toCharacter_evalForest {κ : Type v} [Fintype κ]
    (rk : LabelledRungeKutta α ι R) (rk' : LabelledRungeKutta α κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ φ : LRootedForest α,
        (LSeries.toCharacter (series rk)).evalForest φ =
          (LSeries.toCharacter (series rk')).evalForest φ := by
  rw [agreeUpToOrder_all_iff_forestWeight]
  simp

theorem agreeUpToOrder_comapMapLabels {β : Type x} {κ : Type v} [Fintype κ]
    (f : α → β) {rk : LabelledRungeKutta β ι R}
    {rk' : LabelledRungeKutta β κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) :
    AgreeUpToOrder (comapMapLabels f rk) (comapMapLabels f rk') n := by
  change
    LSeries.AgreeUpToOrder (series (comapMapLabels f rk))
      (series (comapMapLabels f rk')) n
  rw [series_comapMapLabels, series_comapMapLabels]
  exact LSeries.agreeUpToOrder_comapMapLabels f h

theorem agreeUpToOrder_comapMapLabels_iff_of_surjective
    {β : Type x} {κ : Type v} [Fintype κ] {f : α → β}
    (hf : Function.Surjective f) (rk : LabelledRungeKutta β ι R)
    (rk' : LabelledRungeKutta β κ R) (n : Nat) :
    AgreeUpToOrder (comapMapLabels f rk) (comapMapLabels f rk') n ↔
      AgreeUpToOrder rk rk' n := by
  change
    LSeries.AgreeUpToOrder (series (comapMapLabels f rk))
      (series (comapMapLabels f rk')) n ↔
        LSeries.AgreeUpToOrder (series rk) (series rk') n
  rw [series_comapMapLabels, series_comapMapLabels]
  exact LSeries.agreeUpToOrder_comapMapLabels_iff_of_surjective hf

theorem agreeUpToOrder_all_comapMapLabels {β : Type x} {κ : Type v} [Fintype κ]
    (f : α → β) {rk : LabelledRungeKutta β ι R}
    {rk' : LabelledRungeKutta β κ R}
    (h : ∀ n, AgreeUpToOrder rk rk' n) :
    ∀ n, AgreeUpToOrder (comapMapLabels f rk) (comapMapLabels f rk') n :=
  fun n => agreeUpToOrder_comapMapLabels f (h n)

theorem agreeUpToOrder_all_comapMapLabels_iff_of_surjective
    {β : Type x} {κ : Type v} [Fintype κ] {f : α → β}
    (hf : Function.Surjective f) (rk : LabelledRungeKutta β ι R)
    (rk' : LabelledRungeKutta β κ R) :
    (∀ n, AgreeUpToOrder (comapMapLabels f rk) (comapMapLabels f rk') n) ↔
      ∀ n, AgreeUpToOrder rk rk' n := by
  constructor
  · intro h n
    exact (agreeUpToOrder_comapMapLabels_iff_of_surjective hf rk rk' n).1 (h n)
  · intro h n
    exact agreeUpToOrder_comapMapLabels f (h n)

theorem agreeUpToOrder_comapConstLabel {κ : Type v} [Fintype κ]
    (a : α) {rk : LabelledRungeKutta α ι R}
    {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) :
    RungeKutta.AgreeUpToOrder (comapConstLabel a rk) (comapConstLabel a rk') n := by
  change
    Series.AgreeUpToOrder (RungeKutta.series (comapConstLabel a rk))
      (RungeKutta.series (comapConstLabel a rk')) n
  rw [series_comapConstLabel, series_comapConstLabel]
  exact LSeries.agreeUpToOrder_comapConstLabel a h

theorem agreeUpToOrder_all_comapConstLabel {κ : Type v} [Fintype κ]
    (a : α) {rk : LabelledRungeKutta α ι R}
    {rk' : LabelledRungeKutta α κ R}
    (h : ∀ n, AgreeUpToOrder rk rk' n) :
    ∀ n, RungeKutta.AgreeUpToOrder
      (comapConstLabel a rk) (comapConstLabel a rk') n :=
  fun n => agreeUpToOrder_comapConstLabel a (h n)

/-- Promote an ordinary Runge-Kutta tableau to a label-independent labelled tableau. -/
def ofRungeKutta (α : Type u) (rk : RungeKutta ι R) : LabelledRungeKutta α ι R where
  A _ := rk.A
  b _ := rk.b

omit [Fintype ι] [CommSemiring R] in
@[simp]
theorem ofRungeKutta_A (rk : RungeKutta ι R) (a : α) (i j : ι) :
    (ofRungeKutta α rk).A a i j = rk.A i j :=
  rfl

omit [Fintype ι] [CommSemiring R] in
@[simp]
theorem ofRungeKutta_b (rk : RungeKutta ι R) (a : α) (i : ι) :
    (ofRungeKutta α rk).b a i = rk.b i :=
  rfl

mutual

theorem stageWeight_ofRungeKutta_erase (rk : RungeKutta ι R) :
    ∀ (t : PLTree α) (i : ι),
      stageWeight (ofRungeKutta α rk) t i =
        RungeKutta.stageWeight rk (PLTree.erase t) i
  | .node _ ts, i => by
      simp [stageWeightList_ofRungeKutta_erase rk ts i]

theorem stageWeightList_ofRungeKutta_erase (rk : RungeKutta ι R) :
    ∀ (ts : List (PLTree α)) (i : ι),
      stageWeightList (ofRungeKutta α rk) ts i =
        RungeKutta.stageWeightList rk (ts.map PLTree.erase) i
  | [], _ => rfl
  | t :: ts, i => by
      simp [stageWeight_ofRungeKutta_erase rk t,
        stageWeightList_ofRungeKutta_erase rk ts i]

end

theorem weight_ofRungeKutta_erase (rk : RungeKutta ι R) :
    ∀ t : PLTree α,
      weight (ofRungeKutta α rk) t = RungeKutta.weight rk (PLTree.erase t)
  | .node _ ts => by
      simp [weight, RungeKutta.weight, stageWeightList_ofRungeKutta_erase rk ts]

theorem treeStageWeight_ofRungeKutta_erase (rk : RungeKutta ι R)
    (τ : LRootedTree α) (i : ι) :
    treeStageWeight (ofRungeKutta α rk) τ i =
      RungeKutta.treeStageWeight rk (LRootedTree.erase τ) i := by
  refine Quotient.inductionOn τ ?_
  intro t
  change
    stageWeight (ofRungeKutta α rk) t i =
      RungeKutta.treeStageWeight rk (RootedTree.ofPTree (PLTree.erase t)) i
  rw [RungeKutta.treeStageWeight_ofPTree]
  exact stageWeight_ofRungeKutta_erase (α := α) rk t i

theorem treeWeight_ofRungeKutta_erase (rk : RungeKutta ι R) (τ : LRootedTree α) :
    treeWeight (ofRungeKutta α rk) τ =
      RungeKutta.treeWeight rk (LRootedTree.erase τ) := by
  refine Quotient.inductionOn τ ?_
  intro t
  change
    weight (ofRungeKutta α rk) t =
      RungeKutta.treeWeight rk (RootedTree.ofPTree (PLTree.erase t))
  rw [RungeKutta.treeWeight_ofPTree]
  exact weight_ofRungeKutta_erase (α := α) rk t

theorem forestStageWeight_ofRungeKutta_erase (rk : RungeKutta ι R)
    (φ : LRootedForest α) (i : ι) :
    forestStageWeight (ofRungeKutta α rk) φ i =
      RungeKutta.forestStageWeight rk (LRootedForest.erase φ) i := by
  simp only [forestStageWeight, RungeKutta.forestStageWeight, LRootedForest.erase,
    ofRungeKutta_A, treeStageWeight_ofRungeKutta_erase, Multiset.map_map,
    Function.comp_apply]

theorem forestWeight_ofRungeKutta_erase (rk : RungeKutta ι R)
    (φ : LRootedForest α) :
    forestWeight (ofRungeKutta α rk) φ =
      RungeKutta.forestWeight rk (LRootedForest.erase φ) := by
  simp only [forestWeight, RungeKutta.forestWeight, LRootedForest.erase,
    treeWeight_ofRungeKutta_erase, Multiset.map_map, Function.comp_apply]

theorem series_ofRungeKutta_erase (rk : RungeKutta ι R) :
    series (ofRungeKutta α rk) =
      LSeries.comapEraseLabels (α := α) (RungeKutta.series rk) := by
  funext ξ
  cases ξ with
  | empty => rfl
  | tree τ =>
      simp [series, LSeries.comapEraseLabels, LTreeIndex.erase, RungeKutta.series,
        treeWeight_ofRungeKutta_erase]

theorem series_ofRungeKutta_labelInvariant (rk : RungeKutta ι R) :
    LSeries.LabelInvariant (series (ofRungeKutta α rk)) := by
  rw [series_ofRungeKutta_erase]
  exact LSeries.labelInvariant_comapEraseLabels (α := α) (RungeKutta.series rk)

theorem oneStage_treeStageWeight (a : R) (τ : LRootedTree α) (i : PUnit) :
    treeStageWeight (ofRungeKutta α (RungeKutta.oneStage R a)) τ i =
      a ^ (LRootedTree.order τ - 1) := by
  refine Quotient.inductionOn τ ?_
  intro t
  change
    stageWeight (ofRungeKutta α (RungeKutta.oneStage R a)) t i =
      a ^ (LRootedTree.order (LRootedTree.ofPLTree t) - 1)
  rw [stageWeight_ofRungeKutta_erase, RungeKutta.oneStage_stageWeight,
    LRootedTree.order_ofPLTree, PLTree.order_erase]

theorem oneStage_treeWeight (a : R) (τ : LRootedTree α) :
    treeWeight (ofRungeKutta α (RungeKutta.oneStage R a)) τ =
      a ^ (LRootedTree.order τ - 1) := by
  rw [treeWeight_ofRungeKutta_erase, RungeKutta.oneStage_treeWeight,
    LRootedTree.order_erase]

theorem oneStage_series_apply_tree (a : R) (τ : LRootedTree α) :
    series (ofRungeKutta α (RungeKutta.oneStage R a)) (.tree τ) =
      a ^ (LRootedTree.order τ - 1) := by
  exact oneStage_treeWeight (α := α) a τ

theorem oneStage_forestWeight (a : R) (φ : LRootedForest α) :
    forestWeight (ofRungeKutta α (RungeKutta.oneStage R a)) φ =
      (φ.map fun τ => a ^ (LRootedTree.order τ - 1)).prod := by
  simp [forestWeight, oneStage_treeWeight]

theorem oneStage_forestCoeff (a : R) (φ : LRootedForest α) :
    LSeries.forestCoeff (series (ofRungeKutta α (RungeKutta.oneStage R a))) φ =
      (φ.map fun τ => a ^ (LRootedTree.order τ - 1)).prod := by
  rw [forestCoeff_series, oneStage_forestWeight]

theorem oneStage_toCharacter_evalForest (a : R) (φ : LRootedForest α) :
    (LSeries.toCharacter (series (ofRungeKutta α (RungeKutta.oneStage R a)))).evalForest φ =
      (φ.map fun τ => a ^ (LRootedTree.order τ - 1)).prod := by
  rw [toCharacter_series_evalForest, oneStage_forestWeight]

theorem toCharacter_series_ofRungeKutta_labelInvariant [Nonempty α]
    (rk : RungeKutta ι R) :
    LForestAlgebra.Character.LabelInvariant
      (LSeries.toCharacter (series (ofRungeKutta α rk))) :=
  (series_ofRungeKutta_labelInvariant (α := α) rk).toCharacter

theorem agreeUpToOrder_ofRungeKutta {κ : Type v} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : RungeKutta.AgreeUpToOrder rk rk' n) :
    AgreeUpToOrder (ofRungeKutta α rk) (ofRungeKutta α rk') n := by
  change
    LSeries.AgreeUpToOrder (series (ofRungeKutta α rk))
      (series (ofRungeKutta α rk')) n
  rw [series_ofRungeKutta_erase, series_ofRungeKutta_erase]
  exact LSeries.agreeUpToOrder_comapEraseLabels h

theorem agreeUpToOrder_ofRungeKutta_iff {κ : Type v} [Fintype κ] [Nonempty α]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder (ofRungeKutta α rk) (ofRungeKutta α rk') n ↔
      RungeKutta.AgreeUpToOrder rk rk' n := by
  change
    LSeries.AgreeUpToOrder (series (ofRungeKutta α rk))
      (series (ofRungeKutta α rk')) n ↔
        Series.AgreeUpToOrder (RungeKutta.series rk) (RungeKutta.series rk') n
  rw [series_ofRungeKutta_erase, series_ofRungeKutta_erase]
  exact LSeries.agreeUpToOrder_comapEraseLabels_iff

theorem agreeUpToOrder_ofRungeKutta_all {κ : Type v} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R}
    (h : ∀ n, RungeKutta.AgreeUpToOrder rk rk' n) :
    ∀ n, AgreeUpToOrder (ofRungeKutta α rk) (ofRungeKutta α rk') n :=
  fun n => agreeUpToOrder_ofRungeKutta (α := α) (h n)

theorem agreeUpToOrder_ofRungeKutta_all_iff {κ : Type v} [Fintype κ]
    [Nonempty α] (rk : RungeKutta ι R) (rk' : RungeKutta κ R) :
    (∀ n, AgreeUpToOrder (ofRungeKutta α rk) (ofRungeKutta α rk') n) ↔
      ∀ n, RungeKutta.AgreeUpToOrder rk rk' n := by
  constructor
  · intro h n
    exact (agreeUpToOrder_ofRungeKutta_iff (α := α) rk rk' n).1 (h n)
  · intro h n
    exact agreeUpToOrder_ofRungeKutta (α := α) (h n)

end Semiring

section Field

variable [Fintype ι] [Field R]

/-- A labelled Runge-Kutta tableau has order `n` when its labelled B-series
agrees with the exact labelled B-series through order `n`. -/
def HasOrder (rk : LabelledRungeKutta α ι R) (n : Nat) : Prop :=
  LSeries.HasOrder (series rk) n

theorem hasOrder_iff_treeWeight (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ τ : LRootedTree α, LRootedTree.order τ ≤ n →
        treeWeight rk τ = (LRootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h τ hτ
    simpa [HasOrder, LSeries.exact] using h (.tree τ) hτ
  · intro h τ hτ
    cases τ with
    | empty =>
        simp [LSeries.exact]
    | tree τ =>
        simpa [HasOrder, LSeries.exact] using h τ hτ

theorem hasOrder_iff_weight (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ t : PLTree α, PLTree.order t ≤ n →
        weight rk t = (PLTree.treeFactorial t : R)⁻¹ := by
  rw [hasOrder_iff_treeWeight]
  constructor
  · intro h t ht
    simpa using h (LRootedTree.ofPLTree t) ht
  · intro h τ hτ
    let t := Quotient.out τ
    have htout : LRootedTree.ofPLTree t = τ := Quotient.out_eq τ
    have htorder : PLTree.order t ≤ n := by
      have : LRootedTree.order (LRootedTree.ofPLTree t) ≤ n := by
        simpa [htout] using hτ
      simpa using this
    have htfactorial : LRootedTree.treeFactorial τ = PLTree.treeFactorial t := by
      rw [← LRootedTree.treeFactorial_ofPLTree t, htout]
    calc
      treeWeight rk τ = treeWeight rk (LRootedTree.ofPLTree t) := by rw [htout]
      _ = weight rk t := rfl
      _ = (PLTree.treeFactorial t : R)⁻¹ := h t htorder
      _ = (LRootedTree.treeFactorial τ : R)⁻¹ := by rw [htfactorial]

theorem hasOrder_iff_forestCoeff (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        LSeries.forestCoeff (series rk) φ =
          (LRootedForest.treeFactorial φ : R)⁻¹ := by
  rw [HasOrder, LSeries.hasOrder_iff_forestCoeff]
  constructor
  · intro h φ hφ
    exact h.2 φ hφ
  · intro h
    exact ⟨series_hasUnitConstant rk, h⟩

theorem hasOrder_iff_forestWeight (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        forestWeight rk φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  rw [hasOrder_iff_forestCoeff]
  simp

theorem hasOrder_iff_weightList (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ ts : List (PLTree α), PLTree.orderList ts ≤ n →
        weightList rk ts = (PLTree.treeFactorialList ts : R)⁻¹ := by
  constructor
  · intro h ts hts
    have horder :
        LRootedForest.order
            ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
          PLTree.orderList ts :=
      LRootedForest.order_ofPLTree_list ts
    have hforest := (hasOrder_iff_forestWeight rk n).1 h
      ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α)
      (by rw [horder]; exact hts)
    have hfactorial :
        LRootedForest.treeFactorial
            ((ts.map LRootedTree.ofPLTree : List (LRootedTree α)) : LRootedForest α) =
          PLTree.treeFactorialList ts :=
      LRootedForest.treeFactorial_ofPLTree_list ts
    simpa [forestWeight_ofPLTree_list, hfactorial] using hforest
  · intro h
    rw [hasOrder_iff_weight]
    intro t ht
    have hsingle := h [t] (by simpa using ht)
    simpa using hsingle

theorem hasOrder_iff_toCharacter_evalForest (rk : LabelledRungeKutta α ι R)
    (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        (LSeries.toCharacter (series rk)).evalForest φ =
          (LRootedForest.treeFactorial φ : R)⁻¹ := by
  rw [hasOrder_iff_forestWeight]
  simp

theorem hasOrder_iff_toCharacter_ofForest (rk : LabelledRungeKutta α ι R)
    (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        LSeries.toCharacter (series rk) (LForestAlgebra.ofForest (R := R) φ) =
          (LRootedForest.treeFactorial φ : R)⁻¹ := by
  rw [hasOrder_iff_forestWeight]
  simp

theorem HasOrder.treeWeight {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {τ : LRootedTree α} (hτ : LRootedTree.order τ ≤ n) :
    treeWeight rk τ = (LRootedTree.treeFactorial τ : R)⁻¹ :=
  (hasOrder_iff_treeWeight rk n).1 h τ hτ

theorem HasOrder.weight {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {t : PLTree α} (ht : PLTree.order t ≤ n) :
    weight rk t = (PLTree.treeFactorial t : R)⁻¹ :=
  (hasOrder_iff_weight rk n).1 h t ht

theorem HasOrder.weightList {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {ts : List (PLTree α)} (hts : PLTree.orderList ts ≤ n) :
    weightList rk ts = (PLTree.treeFactorialList ts : R)⁻¹ :=
  (hasOrder_iff_weightList rk n).1 h ts hts

theorem HasOrder.forestCoeff {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    LSeries.forestCoeff (series rk) φ = (LRootedForest.treeFactorial φ : R)⁻¹ :=
  (hasOrder_iff_forestCoeff rk n).1 h φ hφ

theorem HasOrder.forestWeight {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    forestWeight rk φ = (LRootedForest.treeFactorial φ : R)⁻¹ :=
  (hasOrder_iff_forestWeight rk n).1 h φ hφ

theorem HasOrder.toCharacter_evalForest {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    (LSeries.toCharacter (series rk)).evalForest φ =
      (LRootedForest.treeFactorial φ : R)⁻¹ := by
  rw [toCharacter_series_evalForest]
  exact h.forestWeight hφ

theorem HasOrder.toCharacter_ofForest {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    LSeries.toCharacter (series rk) (LForestAlgebra.ofForest (R := R) φ) =
      (LRootedForest.treeFactorial φ : R)⁻¹ := by
  rw [toCharacter_series_ofForest]
  exact h.forestWeight hφ

theorem HasOrder.of_agreeUpToOrder {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) (hrk : HasOrder rk n) :
    HasOrder rk' n :=
  (LSeries.hasOrder_congr h).1 hrk

theorem hasOrder_congr {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) :
    HasOrder rk n ↔ HasOrder rk' n :=
  LSeries.hasOrder_congr h

theorem hasOrder_all_congr {κ : Type v} [Fintype κ]
    {rk : LabelledRungeKutta α ι R} {rk' : LabelledRungeKutta α κ R}
    (h : ∀ n, AgreeUpToOrder rk rk' n) :
    (∀ n, HasOrder rk n) ↔ ∀ n, HasOrder rk' n :=
  LSeries.hasOrder_all_congr h

theorem HasOrder.treeWeight_graft {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {x : α} {φ : LRootedForest α}
    (hφ : 1 + LRootedForest.order φ ≤ n) :
    (∑ i, rk.b x i * forestStageWeight rk φ i) =
      ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial φ : R)⁻¹ := by
  calc
    (∑ i, rk.b x i * forestStageWeight rk φ i) =
        LSeries.coeff (series rk) (.tree (LRootedForest.graft x φ)) := by
          exact (series_graft rk x φ).symm
    _ = ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial φ : R)⁻¹ := by
          exact LSeries.HasOrder.coeff_tree_graft h hφ

theorem HasOrder.treeWeight_branches {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) {τ : LRootedTree α} (hτ : LRootedTree.order τ ≤ n) :
    (∑ i, rk.b (LRootedTree.rootLabel τ) i *
      forestStageWeight rk (LRootedTree.branches τ) i) =
      (LRootedTree.order τ : R)⁻¹ *
        (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
  calc
    (∑ i, rk.b (LRootedTree.rootLabel τ) i *
      forestStageWeight rk (LRootedTree.branches τ) i) =
        LSeries.coeff (series rk) (.tree τ) := by
          exact (series_branches rk τ).symm
    _ = (LRootedTree.order τ : R)⁻¹ *
        (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
          exact LSeries.HasOrder.coeff_tree_branches h hτ

theorem HasOrder.treeWeight_butcherProduct {rk : LabelledRungeKutta α ι R}
    {n : Nat} (h : HasOrder rk n) {φ : LRootedForest α} {τ : LRootedTree α}
    (horder : LRootedForest.order φ + LRootedTree.order τ ≤ n) :
    (∑ i, rk.b (LRootedTree.rootLabel τ) i *
      (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
      ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  have htree :
      LabelledRungeKutta.treeWeight rk (LRootedForest.butcherProduct φ τ) =
        (LRootedTree.treeFactorial (LRootedForest.butcherProduct φ τ) : R)⁻¹ :=
    (hasOrder_iff_treeWeight rk n).1 h
      (LRootedForest.butcherProduct φ τ) (by simpa using horder)
  calc
    (∑ i, rk.b (LRootedTree.rootLabel τ) i *
      (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
        LabelledRungeKutta.treeWeight rk (LRootedForest.butcherProduct φ τ) := by
          exact (LabelledRungeKutta.treeWeight_butcherProduct rk φ τ).symm
    _ = (LRootedTree.treeFactorial (LRootedForest.butcherProduct φ τ) : R)⁻¹ := htree
    _ = ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
          simp [LRootedForest.treeFactorial_butcherProduct]
          ac_rfl

theorem hasOrder_iff_treeWeight_butcherProduct
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ (φ : LRootedForest α) (τ : LRootedTree α),
        LRootedForest.order φ + LRootedTree.order τ ≤ n →
          (∑ i, rk.b (LRootedTree.rootLabel τ) i *
            (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
            ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
              (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  rw [HasOrder, LSeries.hasOrder_iff_coeff_butcherProduct]
  constructor
  · rintro ⟨_, h⟩ φ τ horder
    have htree := h φ τ horder
    change
      treeWeight rk (LRootedForest.butcherProduct φ τ) =
        ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
          (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ at htree
    calc
      (∑ i, rk.b (LRootedTree.rootLabel τ) i *
        (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
          treeWeight rk (LRootedForest.butcherProduct φ τ) := by
            exact (treeWeight_butcherProduct rk φ τ).symm
      _ = ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
            (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := htree
  · intro h
    exact ⟨series_hasUnitConstant rk, fun φ τ horder => by
      calc
        LSeries.coeff (series rk) (LTreeIndex.tree (LRootedForest.butcherProduct φ τ)) =
            treeWeight rk (LRootedForest.butcherProduct φ τ) := rfl
        _ = ∑ i, rk.b (LRootedTree.rootLabel τ) i *
              (forestStageWeight rk φ i * treeStageWeight rk τ i) := by
            exact treeWeight_butcherProduct rk φ τ
        _ = ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
              (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ :=
            h φ τ horder⟩

theorem hasOrder_iff_treeWeight_graft
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ (x : α) (φ : LRootedForest α), 1 + LRootedForest.order φ ≤ n →
        (∑ i, rk.b x i * forestStageWeight rk φ i) =
          ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
            (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h x φ hφ
    exact h.treeWeight_graft hφ
  · intro h
    rw [hasOrder_iff_treeWeight]
    intro τ hτ
    calc
      treeWeight rk τ =
          ∑ i, rk.b (LRootedTree.rootLabel τ) i *
            forestStageWeight rk (LRootedTree.branches τ) i :=
            treeWeight_branches rk τ
      _ = ((1 + LRootedForest.order (LRootedTree.branches τ) : Nat) : R)⁻¹ *
            (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
            exact h (LRootedTree.rootLabel τ) (LRootedTree.branches τ) (by
              rw [LRootedForest.order_branches τ]
              exact hτ)
      _ = (LRootedTree.treeFactorial τ : R)⁻¹ := by
            simpa [LSeries.coeff, LSeries.exact] using
              (LSeries.coeff_exact_tree_branches (R := R) τ).symm

theorem hasOrder_ofRungeKutta {rk : RungeKutta ι R} {n : Nat}
    (h : RungeKutta.HasOrder rk n) :
    HasOrder (ofRungeKutta α rk) n := by
  change LSeries.HasOrder (series (ofRungeKutta α rk)) n
  rw [series_ofRungeKutta_erase]
  exact LSeries.comapEraseLabels_hasOrder h

theorem hasOrder_ofRungeKutta_iff [Nonempty α]
    (rk : RungeKutta ι R) (n : Nat) :
    HasOrder (ofRungeKutta α rk) n ↔ RungeKutta.HasOrder rk n := by
  change LSeries.HasOrder (series (ofRungeKutta α rk)) n ↔
    Series.HasOrder (RungeKutta.series rk) n
  rw [series_ofRungeKutta_erase]
  exact LSeries.comapEraseLabels_hasOrder_iff

theorem hasOrder_ofRungeKutta_all {rk : RungeKutta ι R}
    (h : ∀ n, RungeKutta.HasOrder rk n) :
    ∀ n, HasOrder (ofRungeKutta α rk) n :=
  fun n => hasOrder_ofRungeKutta (α := α) (h n)

theorem hasOrder_ofRungeKutta_all_iff [Nonempty α]
    (rk : RungeKutta ι R) :
    (∀ n, HasOrder (ofRungeKutta α rk) n) ↔ ∀ n, RungeKutta.HasOrder rk n := by
  constructor
  · intro h n
    exact (hasOrder_ofRungeKutta_iff (α := α) rk n).1 (h n)
  · intro h n
    exact hasOrder_ofRungeKutta (α := α) (h n)

theorem hasOrder_comapMapLabels {β : Type x} (f : α → β)
    {rk : LabelledRungeKutta β ι R} {n : Nat}
    (h : HasOrder rk n) : HasOrder (comapMapLabels f rk) n := by
  change LSeries.HasOrder (series (comapMapLabels f rk)) n
  rw [series_comapMapLabels]
  exact LSeries.comapMapLabels_hasOrder f h

theorem hasOrder_comapMapLabels_iff_of_surjective {β : Type x}
    {f : α → β} (hf : Function.Surjective f)
    (rk : LabelledRungeKutta β ι R) (n : Nat) :
    HasOrder (comapMapLabels f rk) n ↔ HasOrder rk n := by
  change LSeries.HasOrder (series (comapMapLabels f rk)) n ↔
    LSeries.HasOrder (series rk) n
  rw [series_comapMapLabels]
  exact LSeries.comapMapLabels_hasOrder_iff_of_surjective hf

theorem hasOrder_all_comapMapLabels {β : Type x} (f : α → β)
    {rk : LabelledRungeKutta β ι R}
    (h : ∀ n, HasOrder rk n) :
    ∀ n, HasOrder (comapMapLabels f rk) n :=
  fun n => hasOrder_comapMapLabels f (h n)

theorem hasOrder_all_comapMapLabels_iff_of_surjective {β : Type x}
    {f : α → β} (hf : Function.Surjective f)
    (rk : LabelledRungeKutta β ι R) :
    (∀ n, HasOrder (comapMapLabels f rk) n) ↔ ∀ n, HasOrder rk n := by
  constructor
  · intro h n
    exact (hasOrder_comapMapLabels_iff_of_surjective hf rk n).1 (h n)
  · intro h n
    exact hasOrder_comapMapLabels f (h n)

theorem hasOrder_comapConstLabel (a : α)
    {rk : LabelledRungeKutta α ι R} {n : Nat}
    (h : HasOrder rk n) : RungeKutta.HasOrder (comapConstLabel a rk) n := by
  change Series.HasOrder (RungeKutta.series (comapConstLabel a rk)) n
  rw [series_comapConstLabel]
  exact LSeries.comapConstLabel_hasOrder a h

theorem hasOrder_all_comapConstLabel (a : α)
    {rk : LabelledRungeKutta α ι R}
    (h : ∀ n, HasOrder rk n) :
    ∀ n, RungeKutta.HasOrder (comapConstLabel a rk) n :=
  fun n => hasOrder_comapConstLabel a (h n)

theorem hasOrder_zero (rk : LabelledRungeKutta α ι R) : HasOrder rk 0 := by
  rw [hasOrder_iff_treeWeight]
  intro τ hτ
  have hpos := LRootedTree.order_pos τ
  omega

theorem series_eq_exact_of_hasOrder_all {rk : LabelledRungeKutta α ι R}
    (h : ∀ n, HasOrder rk n) : series rk = LSeries.exact α R :=
  LSeries.eq_exact_of_hasOrder_all (fun n => h n)

theorem hasOrder_all_iff_series_eq_exact (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔ series rk = LSeries.exact α R := by
  constructor
  · exact series_eq_exact_of_hasOrder_all
  · intro h n
    change LSeries.HasOrder (series rk) n
    rw [h]
    exact LSeries.exact_hasOrder n

theorem hasOrder_all_iff_coeff (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ ξ : LTreeIndex α,
        LSeries.coeff (series rk) ξ = LSeries.coeff (LSeries.exact α R) ξ := by
  rw [hasOrder_all_iff_series_eq_exact]
  constructor
  · intro h ξ
    rw [h]
  · intro h
    funext ξ
    exact h ξ

theorem series_ofRungeKutta_eq_exact_iff [Nonempty α] (rk : RungeKutta ι R) :
    series (ofRungeKutta α rk) = LSeries.exact α R ↔
      RungeKutta.series rk = Series.exact R := by
  rw [← hasOrder_all_iff_series_eq_exact (rk := ofRungeKutta α rk),
    ← RungeKutta.hasOrder_all_iff_series_eq_exact (rk := rk)]
  exact hasOrder_ofRungeKutta_all_iff (α := α) rk

theorem hasOrder_all_iff_toCharacter_eq_exact (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      LSeries.toCharacter (series rk) = LSeries.toCharacter (LSeries.exact α R) := by
  constructor
  · intro h
    exact ((LSeries.hasOrder_all_iff_toCharacter_eq_exact (a := series rk)).1 h).2
  · intro h n
    change LSeries.HasOrder (series rk) n
    exact ((LSeries.hasOrder_all_iff_toCharacter_eq_exact (a := series rk)).2
      ⟨series_hasUnitConstant rk, h⟩) n

theorem characterEquiv_hasOrder_all_iff_exact (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      LSeries.characterEquiv ⟨series rk, series_hasUnitConstant rk⟩ =
        LSeries.characterEquiv ⟨LSeries.exact α R, LSeries.exact_hasUnitConstant⟩ := by
  change (∀ n, LSeries.HasOrder (series rk) n) ↔
    LSeries.characterEquiv ⟨series rk, series_hasUnitConstant rk⟩ =
      LSeries.characterEquiv ⟨LSeries.exact α R, LSeries.exact_hasUnitConstant⟩
  exact LSeries.characterEquiv_hasOrder_all_iff_exact ⟨series rk, series_hasUnitConstant rk⟩

theorem hasOrder_all_iff_treeWeight (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ τ : LRootedTree α,
        treeWeight rk τ = (LRootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h τ
    exact (h (LRootedTree.order τ)).treeWeight le_rfl
  · intro h n
    rw [hasOrder_iff_treeWeight]
    intro τ _hτ
    exact h τ

theorem hasOrder_all_iff_treeCoeff (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ τ : LRootedTree α,
        LSeries.coeff (series rk) (LTreeIndex.tree τ) =
          (LRootedTree.treeFactorial τ : R)⁻¹ := by
  simpa [LSeries.coeff] using hasOrder_all_iff_treeWeight (R := R) rk

theorem hasOrder_all_iff_weight (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ t : PLTree α, weight rk t = (PLTree.treeFactorial t : R)⁻¹ := by
  constructor
  · intro h t
    exact (h (PLTree.order t)).weight le_rfl
  · intro h n
    rw [hasOrder_iff_weight]
    intro t _ht
    exact h t

theorem hasOrder_all_iff_forestWeight (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : LRootedForest α,
        forestWeight rk φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ
    exact (h (LRootedForest.order φ)).forestWeight le_rfl
  · intro h n
    rw [hasOrder_iff_forestWeight]
    intro φ _hφ
    exact h φ

theorem hasOrder_all_iff_forestCoeff (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : LRootedForest α,
        LSeries.forestCoeff (series rk) φ =
          (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simpa using hasOrder_all_iff_forestWeight (R := R) rk

theorem hasOrder_all_iff_toCharacter_evalForest
    (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : LRootedForest α,
        (LSeries.toCharacter (series rk)).evalForest φ =
          (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ
    exact (h (LRootedForest.order φ)).toCharacter_evalForest le_rfl
  · intro h n
    rw [hasOrder_iff_toCharacter_evalForest]
    intro φ _hφ
    exact h φ

theorem hasOrder_all_iff_toCharacter_ofForest
    (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : LRootedForest α,
        LSeries.toCharacter (series rk) (LForestAlgebra.ofForest (R := R) φ) =
          (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ
    exact (h (LRootedForest.order φ)).toCharacter_ofForest le_rfl
  · intro h n
    rw [hasOrder_iff_toCharacter_ofForest]
    intro φ _hφ
    exact h φ

theorem hasOrder_all_iff_treeWeight_graft
    (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ (x : α) (φ : LRootedForest α),
        (∑ i, rk.b x i * forestStageWeight rk φ i) =
          ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
            (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h x φ
    exact (h (1 + LRootedForest.order φ)).treeWeight_graft le_rfl
  · intro h n
    rw [hasOrder_iff_treeWeight_graft]
    intro x φ _hφ
    exact h x φ

theorem hasOrder_all_iff_treeWeight_branches
    (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ τ : LRootedTree α,
        (∑ i, rk.b (LRootedTree.rootLabel τ) i *
          forestStageWeight rk (LRootedTree.branches τ) i) =
          (LRootedTree.order τ : R)⁻¹ *
            (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h τ
    exact (h (LRootedTree.order τ)).treeWeight_branches le_rfl
  · intro h
    rw [hasOrder_all_iff_treeWeight]
    intro τ
    calc
      treeWeight rk τ =
          ∑ i, rk.b (LRootedTree.rootLabel τ) i *
            forestStageWeight rk (LRootedTree.branches τ) i :=
            treeWeight_branches rk τ
      _ = (LRootedTree.order τ : R)⁻¹ *
            (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ :=
            h τ
      _ = (LRootedTree.treeFactorial τ : R)⁻¹ := by
            simpa [LSeries.coeff, LSeries.exact] using
              (LSeries.coeff_exact_tree_branches (R := R) τ).symm

theorem hasOrder_all_iff_treeWeight_butcherProduct
    (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ (φ : LRootedForest α) (τ : LRootedTree α),
        (∑ i, rk.b (LRootedTree.rootLabel τ) i *
          (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
          ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
            (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h φ τ
    exact (h (LRootedForest.order φ + LRootedTree.order τ)).treeWeight_butcherProduct le_rfl
  · intro h n
    rw [hasOrder_iff_treeWeight_butcherProduct]
    intro φ τ _horder
    exact h φ τ

theorem hasOrder_all_iff_weightList (rk : LabelledRungeKutta α ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ ts : List (PLTree α), weightList rk ts = (PLTree.treeFactorialList ts : R)⁻¹ := by
  constructor
  · intro h ts
    exact (h (PLTree.orderList ts)).weightList le_rfl
  · intro h n
    rw [hasOrder_iff_weightList]
    intro ts _hts
    exact h ts

theorem HasOrder.mono {rk : LabelledRungeKutta α ι R} {m n : Nat}
    (h : HasOrder rk n) (hmn : m ≤ n) : HasOrder rk m :=
  LSeries.HasOrder.mono h hmn

theorem hasOrder_succ_iff_treeWeight
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ τ : LRootedTree α, LRootedTree.order τ = n + 1 →
          treeWeight rk τ = (LRootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun τ hτ => h.treeWeight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_treeWeight]
    intro τ hτ
    by_cases hle : LRootedTree.order τ ≤ n
    · exact hprev.treeWeight hle
    · exact htop τ (by omega)

theorem hasOrder_succ_iff_weight
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ t : PLTree α, PLTree.order t = n + 1 →
          weight rk t = (PLTree.treeFactorial t : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun t ht => h.weight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_weight]
    intro t ht
    by_cases hle : PLTree.order t ≤ n
    · exact hprev.weight hle
    · exact htop t (by omega)

theorem hasOrder_succ_iff_forestWeight
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ = n + 1 →
          forestWeight rk φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun φ hφ => h.forestWeight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_forestWeight]
    intro φ hφ
    by_cases hle : LRootedForest.order φ ≤ n
    · exact hprev.forestWeight hle
    · exact htop φ (by omega)

theorem hasOrder_succ_iff_weightList
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ ts : List (PLTree α), PLTree.orderList ts = n + 1 →
          weightList rk ts = (PLTree.treeFactorialList ts : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun ts hts => h.weightList (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_weightList]
    intro ts hts
    by_cases hle : PLTree.orderList ts ≤ n
    · exact hprev.weightList hle
    · exact htop ts (by omega)

theorem hasOrder_succ_iff_toCharacter_evalForest
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ = n + 1 →
          (LSeries.toCharacter (series rk)).evalForest φ =
            (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n),
      fun φ hφ => h.toCharacter_evalForest (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_toCharacter_evalForest]
    intro φ hφ
    by_cases hle : LRootedForest.order φ ≤ n
    · exact hprev.toCharacter_evalForest hle
    · exact htop φ (by omega)

theorem hasOrder_succ_iff_toCharacter_ofForest
    (rk : LabelledRungeKutta α ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ = n + 1 →
          LSeries.toCharacter (series rk) (LForestAlgebra.ofForest (R := R) φ) =
            (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n),
      fun φ hφ => h.toCharacter_ofForest (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_toCharacter_ofForest]
    intro φ hφ
    by_cases hle : LRootedForest.order φ ≤ n
    · exact hprev.toCharacter_ofForest hle
    · exact htop φ (by omega)

end Field

end LabelledRungeKutta

end BSeries
