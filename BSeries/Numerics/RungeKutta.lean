/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Runge-Kutta Elementary Weights

This file defines Runge-Kutta tableaux and their elementary weights on rooted
trees. The recursive stage weights are first defined for planar trees, then
shown invariant under child permutations so that they descend to non-planar
rooted trees.

## Main definitions

* `RungeKutta` - a Butcher tableau without a fixed stage ordering
* `RungeKutta.stageWeight` - recursive stage weight of a planar tree
* `RungeKutta.weight` - elementary weight of a planar tree
* `RungeKutta.series` - the B-series coefficient family induced by a tableau

## References

* John C. Butcher, *Introduction to Runge-Kutta methods*
* John C. Butcher, *Numerical Methods for Ordinary Differential Equations*
-/

namespace BSeries

open HopfAlgebras

open scoped BigOperators

universe u v

/-- A Runge-Kutta tableau with stage type `ι` and coefficients in `R`. -/
structure RungeKutta (ι : Type u) (R : Type v) where
  A : ι → ι → R
  b : ι → R

namespace RungeKutta

variable {ι : Type u} {R : Type v}

/-- A one-stage Runge-Kutta tableau with stage matrix entry `a` and weight `1`. -/
def oneStage (R : Type v) [One R] (a : R) : RungeKutta PUnit R where
  A _ _ := a
  b _ := 1

/-- Forward Euler as a one-stage Runge-Kutta tableau. -/
def explicitEuler (R : Type v) [Zero R] [One R] : RungeKutta PUnit R :=
  oneStage R 0

/-- Backward Euler as a one-stage Runge-Kutta tableau. -/
def implicitEuler (R : Type v) [One R] : RungeKutta PUnit R :=
  oneStage R 1

/-- A two-stage explicit Runge-Kutta tableau. -/
def twoStageExplicit (R : Type v) [Zero R] (a21 b1 b2 : R) :
    RungeKutta (Fin 2) R where
  A i j := ![![0, 0], ![a21, 0]] i j
  b i := ![b1, b2] i

/-- A three-stage explicit Runge-Kutta tableau. -/
def threeStageExplicit (R : Type v) [Zero R] (a21 a31 a32 b1 b2 b3 : R) :
    RungeKutta (Fin 3) R where
  A i j := ![![0, 0, 0], ![a21, 0, 0], ![a31, a32, 0]] i j
  b i := ![b1, b2, b3] i

section OneStage

variable [One R]

@[simp]
theorem oneStage_A (a : R) (i j : PUnit) :
    (oneStage R a).A i j = a :=
  rfl

@[simp]
theorem oneStage_b (a : R) (i : PUnit) :
    (oneStage R a).b i = 1 :=
  rfl

end OneStage

section Semiring

variable [Fintype ι] [CommSemiring R]

/-- Row sum `cᵢ = ∑ⱼ aᵢⱼ` of the tableau. -/
def abscissa (rk : RungeKutta ι R) (i : ι) : R :=
  ∑ j, rk.A i j

omit [Fintype ι] in
@[simp]
theorem oneStage_abscissa (a : R) (i : PUnit) :
    abscissa (oneStage R a) i = a := by
  simp [abscissa]

omit [Fintype ι] in
@[simp]
theorem explicitEuler_abscissa (i : PUnit) :
    abscissa (explicitEuler R) i = 0 := by
  simp [explicitEuler]

omit [Fintype ι] in
@[simp]
theorem implicitEuler_abscissa (i : PUnit) :
    abscissa (implicitEuler R) i = 1 := by
  simp [implicitEuler]

omit [Fintype ι] in
@[simp]
theorem twoStageExplicit_abscissa_zero (a21 b1 b2 : R) :
    abscissa (twoStageExplicit R a21 b1 b2) 0 = 0 := by
  simp [abscissa, twoStageExplicit, Fin.sum_univ_two]

omit [Fintype ι] in
@[simp]
theorem twoStageExplicit_abscissa_one (a21 b1 b2 : R) :
    abscissa (twoStageExplicit R a21 b1 b2) 1 = a21 := by
  simp [abscissa, twoStageExplicit, Fin.sum_univ_two]

omit [Fintype ι] in
@[simp]
theorem threeStageExplicit_abscissa_zero (a21 a31 a32 b1 b2 b3 : R) :
    abscissa (threeStageExplicit R a21 a31 a32 b1 b2 b3) 0 = 0 := by
  simp [abscissa, threeStageExplicit, Fin.sum_univ_three]

omit [Fintype ι] in
@[simp]
theorem threeStageExplicit_abscissa_one (a21 a31 a32 b1 b2 b3 : R) :
    abscissa (threeStageExplicit R a21 a31 a32 b1 b2 b3) 1 = a21 := by
  simp [abscissa, threeStageExplicit, Fin.sum_univ_three]

omit [Fintype ι] in
@[simp]
theorem threeStageExplicit_abscissa_two (a21 a31 a32 b1 b2 b3 : R) :
    abscissa (threeStageExplicit R a21 a31 a32 b1 b2 b3) 2 = a31 + a32 := by
  simp [abscissa, threeStageExplicit, Fin.sum_univ_three]

mutual

/-- Recursive stage weight of a planar tree. -/
def stageWeight (rk : RungeKutta ι R) : PTree → ι → R
  | .node ts, i => stageWeightList rk ts i

/-- Product of child contributions in the recursive stage weight. -/
def stageWeightList (rk : RungeKutta ι R) : List PTree → ι → R
  | [], _ => 1
  | t :: ts, i => (∑ j, rk.A i j * stageWeight rk t j) * stageWeightList rk ts i

end

@[simp]
theorem stageWeight_node (rk : RungeKutta ι R) (ts : List PTree) (i : ι) :
    stageWeight rk (.node ts) i = stageWeightList rk ts i :=
  rfl

@[simp]
theorem stageWeightList_nil (rk : RungeKutta ι R) (i : ι) :
    stageWeightList rk [] i = 1 :=
  rfl

@[simp]
theorem stageWeightList_cons (rk : RungeKutta ι R) (t : PTree)
    (ts : List PTree) (i : ι) :
    stageWeightList rk (t :: ts) i =
      (∑ j, rk.A i j * stageWeight rk t j) * stageWeightList rk ts i :=
  rfl

@[simp]
theorem stageWeight_bullet (rk : RungeKutta ι R) (i : ι) :
    stageWeight rk PTree.bullet i = 1 := by
  simp [PTree.bullet]

@[simp]
theorem stageWeight_chain2 (rk : RungeKutta ι R) (i : ι) :
    stageWeight rk PTree.chain2 i = abscissa rk i := by
  simp [PTree.chain2, PTree.bullet, abscissa]

@[simp]
theorem stageWeight_chain3 (rk : RungeKutta ι R) (i : ι) :
    stageWeight rk PTree.chain3 i = ∑ j, rk.A i j * abscissa rk j := by
  simp [PTree.chain3, abscissa]

@[simp]
theorem stageWeight_cherry (rk : RungeKutta ι R) (i : ι) :
    stageWeight rk PTree.cherry i = abscissa rk i * abscissa rk i := by
  simp [PTree.cherry, PTree.bullet, abscissa]

/-- Elementary weight of a planar rooted tree. -/
def weight (rk : RungeKutta ι R) (t : PTree) : R :=
  ∑ i, rk.b i * stageWeight rk t i

/-- Elementary weight of the one-node tree. -/
def weightBullet (rk : RungeKutta ι R) : R :=
  ∑ i, rk.b i

@[simp]
theorem weight_bullet (rk : RungeKutta ι R) :
    weight rk PTree.bullet = weightBullet rk := by
  simp [weight, weightBullet]

@[simp]
theorem oneStage_weightBullet (a : R) :
    weightBullet (oneStage R a) = 1 := by
  simp [weightBullet]

@[simp]
theorem explicitEuler_weightBullet :
    weightBullet (explicitEuler R) = 1 := by
  simp [explicitEuler]

@[simp]
theorem implicitEuler_weightBullet :
    weightBullet (implicitEuler R) = 1 := by
  simp [implicitEuler]

private theorem oneStage_pow_step (a : R) (t : PTree) :
    a * a ^ (PTree.order t - 1) = a ^ PTree.order t := by
  have ht : 0 < PTree.order t := PTree.order_pos t
  calc
    a * a ^ (PTree.order t - 1) = a ^ ((PTree.order t - 1) + 1) :=
      (pow_succ' a (PTree.order t - 1)).symm
    _ = a ^ PTree.order t := by
      rw [Nat.sub_one_add_one_eq_of_pos ht]

private theorem oneStage_stageWeight_unit (a : R) (t : PTree) :
    stageWeight (oneStage R a) t PUnit.unit = a ^ (PTree.order t - 1) := by
  exact
    @PTree.rec
      (fun t => stageWeight (oneStage R a) t PUnit.unit = a ^ (PTree.order t - 1))
      (fun ts => stageWeightList (oneStage R a) ts PUnit.unit = a ^ PTree.orderList ts)
      (fun _ hts => by
        simpa [stageWeight, PTree.order] using hts)
      (by
        simp [PTree.orderList])
      (fun head _ hhead htail => by
        simp [PTree.orderList, htail, pow_add]
        rw [hhead, oneStage_pow_step])
      t

@[simp]
theorem oneStage_stageWeight (a : R) (t : PTree) (i : PUnit) :
    stageWeight (oneStage R a) t i = a ^ (PTree.order t - 1) := by
  cases i
  exact oneStage_stageWeight_unit (R := R) a t

@[simp]
theorem oneStage_stageWeightList (a : R) (ts : List PTree) (i : PUnit) :
    stageWeightList (oneStage R a) ts i = a ^ PTree.orderList ts := by
  cases i
  exact
    @PTree.rec_1
      (fun t => stageWeight (oneStage R a) t PUnit.unit = a ^ (PTree.order t - 1))
      (fun ts => stageWeightList (oneStage R a) ts PUnit.unit = a ^ PTree.orderList ts)
      (fun _ hts => by
        simpa [stageWeight, PTree.order] using hts)
      (by
        simp [PTree.orderList])
      (fun head _ hhead htail => by
        simp [PTree.orderList, htail, pow_add]
        rw [oneStage_pow_step])
      ts

@[simp]
theorem oneStage_weight (a : R) (t : PTree) :
    weight (oneStage R a) t = a ^ (PTree.order t - 1) := by
  simp [weight]

@[simp]
theorem oneStage_weight_chain2 (a : R) :
    weight (oneStage R a) PTree.chain2 = a := by
  simp [PTree.chain2, PTree.bullet]

@[simp]
theorem weight_chain3 (rk : RungeKutta ι R) :
    weight rk PTree.chain3 = ∑ i, rk.b i * (∑ j, rk.A i j * abscissa rk j) := by
  simp [weight]

@[simp]
theorem weight_cherry (rk : RungeKutta ι R) :
    weight rk PTree.cherry = ∑ i, rk.b i * (abscissa rk i * abscissa rk i) := by
  simp [weight]

@[simp]
theorem twoStageExplicit_weightBullet (a21 b1 b2 : R) :
    weightBullet (twoStageExplicit R a21 b1 b2) = b1 + b2 := by
  simp [weightBullet, twoStageExplicit, Fin.sum_univ_two]

@[simp]
theorem twoStageExplicit_weight_chain2 (a21 b1 b2 : R) :
    weight (twoStageExplicit R a21 b1 b2) PTree.chain2 = b2 * a21 := by
  simp [weight, twoStageExplicit, PTree.chain2, PTree.bullet, Fin.sum_univ_two]

@[simp]
theorem threeStageExplicit_weightBullet (a21 a31 a32 b1 b2 b3 : R) :
    weightBullet (threeStageExplicit R a21 a31 a32 b1 b2 b3) = b1 + b2 + b3 := by
  simp [weightBullet, threeStageExplicit, Fin.sum_univ_three]

@[simp]
theorem threeStageExplicit_weight_chain2 (a21 a31 a32 b1 b2 b3 : R) :
    weight (threeStageExplicit R a21 a31 a32 b1 b2 b3) PTree.chain2 =
      b2 * a21 + b3 * (a31 + a32) := by
  simp [weight, threeStageExplicit, PTree.chain2, PTree.bullet, Fin.sum_univ_three]

@[simp]
theorem threeStageExplicit_weight_chain3 (a21 a31 a32 b1 b2 b3 : R) :
    weight (threeStageExplicit R a21 a31 a32 b1 b2 b3) PTree.chain3 =
      b3 * (a32 * a21) := by
  simp [weight_chain3, threeStageExplicit, abscissa, Fin.sum_univ_three]

@[simp]
theorem threeStageExplicit_weight_cherry (a21 a31 a32 b1 b2 b3 : R) :
    weight (threeStageExplicit R a21 a31 a32 b1 b2 b3) PTree.cherry =
      b2 * (a21 * a21) + b3 * ((a31 + a32) * (a31 + a32)) := by
  simp [weight_cherry, threeStageExplicit, abscissa, Fin.sum_univ_three]

/-- Multiplicative elementary weight of a planar rooted forest. -/
def weightList (rk : RungeKutta ι R) (ts : List PTree) : R :=
  (ts.map (weight rk)).prod

@[simp]
theorem weightList_nil (rk : RungeKutta ι R) :
    weightList rk [] = 1 :=
  rfl

@[simp]
theorem weightList_cons (rk : RungeKutta ι R) (t : PTree) (ts : List PTree) :
    weightList rk (t :: ts) = weight rk t * weightList rk ts :=
  rfl

@[simp]
theorem weightList_append (rk : RungeKutta ι R) (ts us : List PTree) :
    weightList rk (ts ++ us) = weightList rk ts * weightList rk us := by
  simp [weightList, List.map_append]

theorem weightList_perm (rk : RungeKutta ι R) {ts us : List PTree}
    (h : ts.Perm us) : weightList rk ts = weightList rk us := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem stageWeightList_perm (rk : RungeKutta ι R) (i : ι)
    {ts us : List PTree} (h : ts.Perm us) :
    stageWeightList rk ts i = stageWeightList rk us i := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap _ _ _ => simp [mul_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

@[simp]
theorem stageWeightList_append (rk : RungeKutta ι R) (ts us : List PTree)
    (i : ι) :
    stageWeightList rk (ts ++ us) i =
      stageWeightList rk ts i * stageWeightList rk us i := by
  induction ts with
  | nil =>
      simp
  | cons t ts ih =>
      simp [ih, mul_assoc]

mutual

/-- Stage weights are invariant under the non-planar tree relation. -/
theorem stageWeight_perm (rk : RungeKutta ι R) (i : ι) :
    ∀ {t u : PTree}, PTree.Perm t u → stageWeight rk t i = stageWeight rk u i
  | _, _, .node hp hf => by
      simp [
        stageWeightList_perm rk i hp,
        stageWeightList_eq_of_forall₂ rk i hf
      ]

/-- Stage-weight products are invariant under elementwise equivalent child lists. -/
theorem stageWeightList_eq_of_forall₂ (rk : RungeKutta ι R) (i : ι) :
    ∀ {ts us : List PTree}, List.Forall₂ PTree.Perm ts us →
      stageWeightList rk ts i = stageWeightList rk us i
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
      rename_i t u ts us
      have hhead :
          (∑ j, rk.A i j * stageWeight rk t j) =
            ∑ j, rk.A i j * stageWeight rk u j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [stageWeight_perm rk j h]
      simp [hhead, stageWeightList_eq_of_forall₂ rk i hs]

end

/-- Elementary weights are invariant under the non-planar tree relation. -/
theorem weight_perm (rk : RungeKutta ι R) :
    ∀ {t u : PTree}, PTree.Perm t u → weight rk t = weight rk u
  | t, u, h => by
      unfold weight
      apply Finset.sum_congr rfl
      intro i _
      rw [stageWeight_perm rk i h]

/-- Recursive stage weight of a non-planar rooted tree. -/
def treeStageWeight (rk : RungeKutta ι R) (τ : RootedTree) (i : ι) : R :=
  Quotient.lift (fun t => stageWeight rk t i) (fun _ _ h => stageWeight_perm rk i h) τ

@[simp]
theorem treeStageWeight_ofPTree (rk : RungeKutta ι R) (t : PTree) (i : ι) :
    treeStageWeight rk (RootedTree.ofPTree t) i = stageWeight rk t i :=
  rfl

@[simp]
theorem treeStageWeight_bullet (rk : RungeKutta ι R) (i : ι) :
    treeStageWeight rk RootedTree.bullet i = 1 := by
  simp [RootedTree.bullet]

private theorem treeStageWeight_out (rk : RungeKutta ι R) (τ : RootedTree) (i : ι) :
    stageWeight rk (Quotient.out τ) i = treeStageWeight rk τ i := by
  rw [← treeStageWeight_ofPTree rk (Quotient.out τ) i]
  rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ]

/-- Product of child stage contributions over a non-planar rooted forest. -/
def forestStageWeight (rk : RungeKutta ι R) (φ : RootedForest) (i : ι) : R :=
  (φ.map fun τ => ∑ j, rk.A i j * treeStageWeight rk τ j).prod

@[simp]
theorem forestStageWeight_zero (rk : RungeKutta ι R) (i : ι) :
    forestStageWeight rk 0 i = 1 := by
  simp [forestStageWeight]

@[simp]
theorem forestStageWeight_empty (rk : RungeKutta ι R) (i : ι) :
    forestStageWeight rk RootedForest.empty i = 1 := by
  simp [RootedForest.empty]

@[simp]
theorem forestStageWeight_singleton (rk : RungeKutta ι R) (τ : RootedTree) (i : ι) :
    forestStageWeight rk (RootedForest.singleton τ) i =
      ∑ j, rk.A i j * treeStageWeight rk τ j := by
  simp [forestStageWeight, RootedForest.singleton]

@[simp]
theorem forestStageWeight_add (rk : RungeKutta ι R) (φ ψ : RootedForest) (i : ι) :
    forestStageWeight rk (φ + ψ) i =
      forestStageWeight rk φ i * forestStageWeight rk ψ i := by
  simp [forestStageWeight, Multiset.map_add]

theorem forestStageWeight_ofPTree_list (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (i : ι),
      forestStageWeight rk ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) i =
        stageWeightList rk ts i
  | [], _ => by
      simp [forestStageWeight]
  | t :: ts, i => by
      have htail :
          (List.map ((fun τ => ∑ j, rk.A i j * treeStageWeight rk τ j) ∘
              RootedTree.ofPTree) ts).prod =
            stageWeightList rk ts i := by
        simpa [forestStageWeight] using forestStageWeight_ofPTree_list rk ts i
      simp [forestStageWeight, htail]

private theorem stageWeightList_out (rk : RungeKutta ι R) :
    ∀ (ts : List RootedTree) (i : ι),
      stageWeightList rk (ts.map Quotient.out) i =
        forestStageWeight rk (ts : RootedForest) i
  | [], _ => by
      simp [forestStageWeight]
  | τ :: ts, i => by
      simp [forestStageWeight, treeStageWeight_out rk τ, stageWeightList_out rk ts i]

@[simp]
theorem treeStageWeight_graft (rk : RungeKutta ι R) (φ : RootedForest) (i : ι) :
    treeStageWeight rk (RootedForest.graft φ) i = forestStageWeight rk φ i := by
  refine Quotient.inductionOn φ ?_
  intro ts
  simpa [RootedForest.graft] using stageWeightList_out rk ts i

@[simp]
theorem treeStageWeight_branches (rk : RungeKutta ι R) (τ : RootedTree) (i : ι) :
    treeStageWeight rk τ i = forestStageWeight rk (RootedTree.branches τ) i := by
  calc
    treeStageWeight rk τ i =
        treeStageWeight rk (RootedForest.graft (RootedTree.branches τ)) i := by
          rw [RootedForest.graft_branches τ]
    _ = forestStageWeight rk (RootedTree.branches τ) i := by
          rw [treeStageWeight_graft]

@[simp]
theorem treeStageWeight_butcherProduct (rk : RungeKutta ι R)
    (φ : RootedForest) (τ : RootedTree) (i : ι) :
    treeStageWeight rk (RootedForest.butcherProduct φ τ) i =
      forestStageWeight rk φ i * treeStageWeight rk τ i := by
  rw [RootedForest.butcherProduct, treeStageWeight_graft, forestStageWeight_add,
    ← treeStageWeight_branches]

/-- Elementary weight of a non-planar rooted tree. -/
def treeWeight (rk : RungeKutta ι R) : RootedTree → R :=
  Quotient.lift (weight rk) (fun _ _ h => weight_perm rk h)

@[simp]
theorem treeWeight_ofPTree (rk : RungeKutta ι R) (t : PTree) :
    treeWeight rk (RootedTree.ofPTree t) = weight rk t :=
  rfl

@[simp]
theorem oneStage_treeWeight (a : R) (τ : RootedTree) :
    treeWeight (oneStage R a) τ = a ^ (RootedTree.order τ - 1) := by
  refine Quotient.inductionOn τ ?_
  intro t
  change weight (oneStage R a) t =
    a ^ (RootedTree.order (RootedTree.ofPTree t) - 1)
  rw [RootedTree.order_ofPTree]
  exact oneStage_weight (R := R) a t

theorem treeWeight_eq_sum_treeStageWeight (rk : RungeKutta ι R) (τ : RootedTree) :
    treeWeight rk τ = ∑ i, rk.b i * treeStageWeight rk τ i := by
  refine Quotient.inductionOn τ ?_
  intro t
  rfl

theorem treeWeight_graft (rk : RungeKutta ι R) (φ : RootedForest) :
    treeWeight rk (RootedForest.graft φ) =
      ∑ i, rk.b i * forestStageWeight rk φ i := by
  rw [treeWeight_eq_sum_treeStageWeight]
  apply Finset.sum_congr rfl
  intro i _
  rw [treeStageWeight_graft]

theorem treeWeight_branches (rk : RungeKutta ι R) (τ : RootedTree) :
    treeWeight rk τ =
      ∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i := by
  calc
    treeWeight rk τ = treeWeight rk (RootedForest.graft (RootedTree.branches τ)) := by
      rw [RootedForest.graft_branches τ]
    _ = ∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i :=
      treeWeight_graft rk (RootedTree.branches τ)

theorem treeWeight_butcherProduct (rk : RungeKutta ι R)
    (φ : RootedForest) (τ : RootedTree) :
    treeWeight rk (RootedForest.butcherProduct φ τ) =
      ∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i) := by
  rw [treeWeight_eq_sum_treeStageWeight]
  apply Finset.sum_congr rfl
  intro i _
  rw [treeStageWeight_butcherProduct]

@[simp]
theorem treeWeight_bullet (rk : RungeKutta ι R) :
    treeWeight rk RootedTree.bullet = weightBullet rk := by
  simp [RootedTree.bullet]

/-- Multiplicative elementary weight of a non-planar rooted forest. -/
def forestWeight (rk : RungeKutta ι R) (φ : RootedForest) : R :=
  (φ.map (treeWeight rk)).prod

@[simp]
theorem forestWeight_zero (rk : RungeKutta ι R) :
    forestWeight rk 0 = 1 := by
  simp [forestWeight]

@[simp]
theorem forestWeight_empty (rk : RungeKutta ι R) :
    forestWeight rk RootedForest.empty = 1 := by
  simp [forestWeight, RootedForest.empty]

@[simp]
theorem forestWeight_singleton (rk : RungeKutta ι R) (τ : RootedTree) :
    forestWeight rk (RootedForest.singleton τ) = treeWeight rk τ := by
  simp [forestWeight, RootedForest.singleton]

@[simp]
theorem forestWeight_add (rk : RungeKutta ι R) (φ ψ : RootedForest) :
    forestWeight rk (φ + ψ) = forestWeight rk φ * forestWeight rk ψ := by
  simp [forestWeight, Multiset.map_add]

@[simp]
theorem forestWeight_ofPTree_list (rk : RungeKutta ι R) :
    ∀ ts : List PTree,
      forestWeight rk ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) =
        weightList rk ts
  | [] => by
      simp [forestWeight, weightList]
  | t :: ts => by
      change
        forestWeight rk
            (RootedForest.singleton (RootedTree.ofPTree t) +
              ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest)) =
          weight rk t * weightList rk ts
      rw [forestWeight_add, forestWeight_singleton, treeWeight_ofPTree,
        forestWeight_ofPTree_list]

/-- B-series coefficient family induced by a Runge-Kutta tableau. -/
def series (rk : RungeKutta ι R) : Series R
  | .empty => 1
  | .tree τ => treeWeight rk τ

@[simp]
theorem series_apply_empty (rk : RungeKutta ι R) :
    series rk TreeIndex.empty = 1 :=
  rfl

@[simp]
theorem series_apply_tree (rk : RungeKutta ι R) (τ : RootedTree) :
    series rk (.tree τ) = treeWeight rk τ :=
  rfl

@[simp]
theorem oneStage_series_apply_tree (a : R) (τ : RootedTree) :
    series (oneStage R a) (.tree τ) = a ^ (RootedTree.order τ - 1) := by
  simp

@[simp]
theorem series_apply_bullet (rk : RungeKutta ι R) :
    series rk TreeIndex.bullet = weightBullet rk := by
  simp [TreeIndex.bullet]

@[simp]
theorem series_empty (rk : RungeKutta ι R) :
    Series.coeff (series rk) TreeIndex.empty = 1 :=
  rfl

@[simp]
theorem series_bullet (rk : RungeKutta ι R) :
    Series.coeff (series rk) TreeIndex.bullet = weightBullet rk := by
  simp [series, TreeIndex.bullet]

theorem series_butcherProduct (rk : RungeKutta ι R)
    (φ : RootedForest) (τ : RootedTree) :
    Series.coeff (series rk) (.tree (RootedForest.butcherProduct φ τ)) =
      ∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i) := by
  simpa [Series.coeff] using treeWeight_butcherProduct rk φ τ

theorem series_graft (rk : RungeKutta ι R) (φ : RootedForest) :
    Series.coeff (series rk) (.tree (RootedForest.graft φ)) =
      ∑ i, rk.b i * forestStageWeight rk φ i := by
  simpa [Series.coeff] using treeWeight_graft rk φ

theorem series_branches (rk : RungeKutta ι R) (τ : RootedTree) :
    Series.coeff (series rk) (.tree τ) =
      ∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i := by
  simpa [Series.coeff] using treeWeight_branches rk τ

@[simp]
theorem forestCoeff_series (rk : RungeKutta ι R) (φ : RootedForest) :
    Series.forestCoeff (series rk) φ = forestWeight rk φ := by
  simp [Series.forestCoeff, forestWeight, Series.coeff]

@[simp]
theorem toCharacter_series_evalForest (rk : RungeKutta ι R) (φ : RootedForest) :
    (Series.toCharacter (series rk)).evalForest φ = forestWeight rk φ := by
  simp [ForestAlgebra.Character.evalForest]

@[simp]
theorem toCharacter_series_ofForest (rk : RungeKutta ι R) (φ : RootedForest) :
    Series.toCharacter (series rk) (ForestAlgebra.ofForest (R := R) φ) =
      forestWeight rk φ := by
  simp

theorem series_hasUnitConstant (rk : RungeKutta ι R) :
    Series.HasUnitConstant (series rk) := rfl

/-- Two Runge-Kutta tableaux have matching B-series coefficients through order `n`. -/
def AgreeUpToOrder {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) : Prop :=
  Series.AgreeUpToOrder (series rk) (series rk') n

theorem agreeUpToOrder_refl (rk : RungeKutta ι R) (n : Nat) :
    AgreeUpToOrder rk rk n :=
  Series.agreeUpToOrder_refl (series rk) n

theorem AgreeUpToOrder.symm {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) :
    AgreeUpToOrder rk' rk n :=
  Series.AgreeUpToOrder.symm h

theorem AgreeUpToOrder.trans {κ η : Type u} [Fintype κ] [Fintype η]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {rk'' : RungeKutta η R}
    {n : Nat} (h : AgreeUpToOrder rk rk' n) (h' : AgreeUpToOrder rk' rk'' n) :
    AgreeUpToOrder rk rk'' n :=
  Series.AgreeUpToOrder.trans h h'

theorem AgreeUpToOrder.mono {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {m n : Nat}
    (h : AgreeUpToOrder rk rk' n) (hmn : m ≤ n) :
    AgreeUpToOrder rk rk' m :=
  Series.AgreeUpToOrder.mono h hmn

theorem agreeUpToOrder_iff_treeWeight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ τ : RootedTree, RootedTree.order τ ≤ n →
        treeWeight rk τ = treeWeight rk' τ := by
  constructor
  · intro h τ hτ
    simpa [AgreeUpToOrder, Series.coeff] using h (.tree τ) hτ
  · intro h ξ hξ
    cases ξ with
    | empty =>
        rfl
    | tree τ =>
        simpa [AgreeUpToOrder, Series.coeff] using h τ hξ

theorem agreeUpToOrder_iff_weight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ t : PTree, PTree.order t ≤ n → weight rk t = weight rk' t := by
  rw [agreeUpToOrder_iff_treeWeight]
  constructor
  · intro h t ht
    simpa using h (RootedTree.ofPTree t) ht
  · intro h τ hτ
    let t := Quotient.out τ
    have htout : RootedTree.ofPTree t = τ := Quotient.out_eq τ
    have htorder : PTree.order t ≤ n := by
      have : RootedTree.order (RootedTree.ofPTree t) ≤ n := by
        simpa [htout] using hτ
      simpa using this
    calc
      treeWeight rk τ = treeWeight rk (RootedTree.ofPTree t) := by rw [htout]
      _ = weight rk t := rfl
      _ = weight rk' t := h t htorder
      _ = treeWeight rk' (RootedTree.ofPTree t) := rfl
      _ = treeWeight rk' τ := by rw [htout]

theorem agreeUpToOrder_iff_forestCoeff {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        Series.forestCoeff (series rk) φ = Series.forestCoeff (series rk') φ := by
  rw [AgreeUpToOrder, Series.agreeUpToOrder_iff_forestCoeff]
  constructor
  · intro h φ hφ
    exact h.2 φ hφ
  · intro h
    exact ⟨by rfl, h⟩

theorem agreeUpToOrder_iff_forestWeight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        forestWeight rk φ = forestWeight rk' φ := by
  rw [agreeUpToOrder_iff_forestCoeff]
  simp

theorem agreeUpToOrder_iff_toCharacter_evalForest {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder rk rk' n ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        (Series.toCharacter (series rk)).evalForest φ =
          (Series.toCharacter (series rk')).evalForest φ := by
  rw [agreeUpToOrder_iff_forestWeight]
  simp

theorem AgreeUpToOrder.treeWeight {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {τ : RootedTree} (hτ : RootedTree.order τ ≤ n) :
    treeWeight rk τ = treeWeight rk' τ :=
  (agreeUpToOrder_iff_treeWeight rk rk' n).1 h τ hτ

theorem AgreeUpToOrder.weight {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {t : PTree} (ht : PTree.order t ≤ n) :
    weight rk t = weight rk' t :=
  (agreeUpToOrder_iff_weight rk rk' n).1 h t ht

theorem AgreeUpToOrder.forestWeight {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    forestWeight rk φ = forestWeight rk' φ :=
  (agreeUpToOrder_iff_forestWeight rk rk' n).1 h φ hφ

theorem AgreeUpToOrder.toCharacter_evalForest {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    (Series.toCharacter (series rk)).evalForest φ =
      (Series.toCharacter (series rk')).evalForest φ :=
  (agreeUpToOrder_iff_toCharacter_evalForest rk rk' n).1 h φ hφ

theorem agreeUpToOrder_succ_iff_treeWeight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder rk rk' (n + 1) ↔
      AgreeUpToOrder rk rk' n ∧
        ∀ τ : RootedTree, RootedTree.order τ = n + 1 →
          treeWeight rk τ = treeWeight rk' τ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun τ hτ => h.treeWeight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [agreeUpToOrder_iff_treeWeight]
    intro τ hτ
    by_cases hle : RootedTree.order τ ≤ n
    · exact hprev.treeWeight hle
    · exact htop τ (by omega)

theorem agreeUpToOrder_succ_iff_weight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) (n : Nat) :
    AgreeUpToOrder rk rk' (n + 1) ↔
      AgreeUpToOrder rk rk' n ∧
        ∀ t : PTree, PTree.order t = n + 1 → weight rk t = weight rk' t := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun t ht => h.weight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [agreeUpToOrder_iff_weight]
    intro t ht
    by_cases hle : PTree.order t ≤ n
    · exact hprev.weight hle
    · exact htop t (by omega)

theorem agreeUpToOrder_all_iff_series_eq {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔ series rk = series rk' := by
  change (∀ n, Series.AgreeUpToOrder (series rk) (series rk') n) ↔
    series rk = series rk'
  exact Series.agreeUpToOrder_all_iff_eq

theorem agreeUpToOrder_all_iff_treeWeight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ τ : RootedTree, treeWeight rk τ = treeWeight rk' τ := by
  constructor
  · intro h τ
    exact (h (RootedTree.order τ)).treeWeight le_rfl
  · intro h n
    rw [agreeUpToOrder_iff_treeWeight]
    intro τ hτ
    exact h τ

theorem agreeUpToOrder_all_iff_weight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ t : PTree, weight rk t = weight rk' t := by
  constructor
  · intro h t
    exact (h (PTree.order t)).weight le_rfl
  · intro h n
    rw [agreeUpToOrder_iff_weight]
    intro t ht
    exact h t

theorem agreeUpToOrder_all_iff_forestWeight {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ φ : RootedForest, forestWeight rk φ = forestWeight rk' φ := by
  constructor
  · intro h φ
    exact (h (RootedForest.order φ)).forestWeight le_rfl
  · intro h n
    rw [agreeUpToOrder_iff_forestWeight]
    intro φ hφ
    exact h φ

theorem agreeUpToOrder_all_iff_toCharacter_evalForest {κ : Type u} [Fintype κ]
    (rk : RungeKutta ι R) (rk' : RungeKutta κ R) :
    (∀ n, AgreeUpToOrder rk rk' n) ↔
      ∀ φ : RootedForest,
        (Series.toCharacter (series rk)).evalForest φ =
          (Series.toCharacter (series rk')).evalForest φ := by
  rw [agreeUpToOrder_all_iff_forestWeight]
  simp

/-- First order condition for a Runge-Kutta tableau. -/
def HasOrderOne (rk : RungeKutta ι R) : Prop :=
  weightBullet rk = 1

theorem oneStage_hasOrderOne (a : R) :
    HasOrderOne (oneStage R a) := by
  simp [HasOrderOne]

theorem explicitEuler_hasOrderOne :
    HasOrderOne (explicitEuler R) := by
  simp [HasOrderOne, explicitEuler]

theorem implicitEuler_hasOrderOne :
    HasOrderOne (implicitEuler R) := by
  simp [HasOrderOne, implicitEuler]

theorem twoStageExplicit_hasOrderOne {a21 b1 b2 : R}
    (hsum : b1 + b2 = 1) :
    HasOrderOne (twoStageExplicit R a21 b1 b2) := by
  simpa [HasOrderOne] using hsum

end Semiring

section Field

variable [Fintype ι] [Field R]

/-- The explicit midpoint tableau. -/
def explicitMidpoint (R : Type v) [Field R] : RungeKutta (Fin 2) R :=
  twoStageExplicit R ((2 : R)⁻¹) 0 1

/-- Heun's explicit trapezoidal tableau. -/
def heun (R : Type v) [Field R] : RungeKutta (Fin 2) R :=
  twoStageExplicit R 1 ((2 : R)⁻¹) ((2 : R)⁻¹)

/-- Kutta's classical three-stage third-order tableau. -/
def kuttaThirdOrder (R : Type v) [Field R] : RungeKutta (Fin 3) R :=
  threeStageExplicit R ((2 : R)⁻¹) (-1) 2 ((6 : R)⁻¹) (2 * (3 : R)⁻¹) ((6 : R)⁻¹)

/-- The one-stage implicit midpoint tableau. -/
def implicitMidpoint (R : Type v) [Field R] : RungeKutta PUnit R :=
  oneStage R ((2 : R)⁻¹)

/-- A Runge-Kutta tableau has order `n` when its induced B-series has order `n`. -/
def HasOrder (rk : RungeKutta ι R) (n : Nat) : Prop :=
  Series.HasOrder (series rk) n

theorem hasOrder_iff_treeWeight (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ τ : RootedTree, RootedTree.order τ ≤ n →
        treeWeight rk τ = (RootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h τ hτ
    simpa [HasOrder, Series.exact] using h (.tree τ) hτ
  · intro h τ hτ
    cases τ with
    | empty =>
        simp [Series.exact]
    | tree τ =>
        simpa [HasOrder, Series.exact] using h τ hτ

theorem hasOrder_iff_weight (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ t : PTree, PTree.order t ≤ n →
        weight rk t = (PTree.treeFactorial t : R)⁻¹ := by
  rw [hasOrder_iff_treeWeight]
  constructor
  · intro h t ht
    simpa using h (RootedTree.ofPTree t) ht
  · intro h τ hτ
    let t := Quotient.out τ
    have htout : RootedTree.ofPTree t = τ := Quotient.out_eq τ
    have htorder : PTree.order t ≤ n := by
      have : RootedTree.order (RootedTree.ofPTree t) ≤ n := by
        simpa [htout] using hτ
      simpa using this
    have htfactorial : RootedTree.treeFactorial τ = PTree.treeFactorial t := by
      rw [← RootedTree.treeFactorial_ofPTree t, htout]
    calc
      treeWeight rk τ = treeWeight rk (RootedTree.ofPTree t) := by rw [htout]
      _ = weight rk t := rfl
      _ = (PTree.treeFactorial t : R)⁻¹ := h t htorder
      _ = (RootedTree.treeFactorial τ : R)⁻¹ := by rw [htfactorial]

theorem hasOrder_iff_forestCoeff (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        Series.forestCoeff (series rk) φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  rw [HasOrder, Series.hasOrder_iff_forestCoeff]
  constructor
  · intro h φ hφ
    exact h.2 φ hφ
  · intro h
    exact ⟨series_hasUnitConstant rk, h⟩

theorem hasOrder_iff_forestWeight (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        forestWeight rk φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  rw [hasOrder_iff_forestCoeff]
  simp

theorem hasOrder_iff_weightList (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ ts : List PTree, PTree.orderList ts ≤ n →
        weightList rk ts = (PTree.treeFactorialList ts : R)⁻¹ := by
  constructor
  · intro h ts hts
    have hforest := (hasOrder_iff_forestWeight rk n).1 h
      ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) (by simpa using hts)
    have hfactorial :
        RootedForest.treeFactorial
            ((ts.map RootedTree.ofPTree : List RootedTree) : RootedForest) =
          PTree.treeFactorialList ts :=
      RootedForest.treeFactorial_ofPTree_list ts
    simpa [hfactorial] using hforest
  · intro h
    rw [hasOrder_iff_weight]
    intro t ht
    have hsingle := h [t] (by simpa using ht)
    simpa using hsingle

theorem hasOrder_iff_toCharacter_evalForest (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        (Series.toCharacter (series rk)).evalForest φ =
          (RootedForest.treeFactorial φ : R)⁻¹ := by
  rw [hasOrder_iff_forestWeight]
  simp

theorem hasOrder_iff_toCharacter_ofForest (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        Series.toCharacter (series rk) (ForestAlgebra.ofForest (R := R) φ) =
          (RootedForest.treeFactorial φ : R)⁻¹ := by
  rw [hasOrder_iff_forestWeight]
  simp

theorem hasOrder_one_iff_hasOrderOne (rk : RungeKutta ι R) :
    HasOrder rk 1 ↔ HasOrderOne rk := by
  rw [HasOrder, Series.hasOrder_one_iff]
  constructor
  · intro h
    simpa [HasOrderOne, TreeIndex.bullet, Series.coeff] using h.2
  · intro h
    exact ⟨series_hasUnitConstant rk, by simpa [HasOrderOne, TreeIndex.bullet, Series.coeff] using h⟩

theorem hasOrder_two_iff_hasOrderOne_and_weight_chain2 (rk : RungeKutta ι R) :
    HasOrder rk 2 ↔ HasOrderOne rk ∧ weight rk PTree.chain2 = (2 : R)⁻¹ := by
  constructor
  · intro h
    have hfirst : HasOrder rk 1 := Series.HasOrder.mono h (by norm_num)
    have hchain := (hasOrder_iff_weight rk 2).1 h PTree.chain2 (by simp)
    exact ⟨(hasOrder_one_iff_hasOrderOne rk).1 hfirst, by simpa using hchain⟩
  · rintro ⟨hfirst, hchain⟩
    rw [hasOrder_iff_weight]
    intro t ht
    have hpos := PTree.order_pos t
    have horder : PTree.order t = 1 ∨ PTree.order t = 2 := by omega
    rcases horder with horder | horder
    · rw [(PTree.order_eq_one_iff t).1 horder]
      simpa [HasOrderOne] using hfirst
    · rw [(PTree.order_eq_two_iff t).1 horder]
      simpa using hchain

theorem hasOrder_three_iff_hasOrder_two_and_weight_chain3_and_cherry
    (rk : RungeKutta ι R) :
    HasOrder rk 3 ↔
      HasOrder rk 2 ∧
        weight rk PTree.chain3 = (6 : R)⁻¹ ∧
          weight rk PTree.cherry = (3 : R)⁻¹ := by
  constructor
  · intro h
    have htwo : HasOrder rk 2 := Series.HasOrder.mono h (by norm_num)
    have hchain := (hasOrder_iff_weight rk 3).1 h PTree.chain3 (by rw [PTree.order_chain3])
    have hcherry := (hasOrder_iff_weight rk 3).1 h PTree.cherry (by rw [PTree.order_cherry])
    exact ⟨htwo, by simpa [PTree.chain3] using hchain, by simpa [PTree.cherry] using hcherry⟩
  · rintro ⟨htwo, hchain, hcherry⟩
    rw [hasOrder_iff_weight]
    intro t ht
    have horder : PTree.order t ≤ 2 ∨ PTree.order t = 3 := by omega
    rcases horder with hle | hthree
    · exact (hasOrder_iff_weight rk 2).1 htwo t hle
    · rcases (PTree.order_eq_three_iff t).1 hthree with h | h
      · rw [h]
        simpa [PTree.chain3] using hchain
      · rw [h]
        simpa [PTree.cherry] using hcherry

theorem kuttaThirdOrder_hasOrder_three [CharZero R] :
    HasOrder (kuttaThirdOrder R) 3 := by
  rw [hasOrder_three_iff_hasOrder_two_and_weight_chain3_and_cherry]
  refine ⟨?_, ?_, ?_⟩
  · rw [hasOrder_two_iff_hasOrderOne_and_weight_chain2]
    constructor
    · simp [HasOrderOne, kuttaThirdOrder]
      norm_num
    · dsimp [kuttaThirdOrder]
      rw [threeStageExplicit_weight_chain2]
      norm_num
  · dsimp [kuttaThirdOrder]
    rw [threeStageExplicit_weight_chain3]
    norm_num
  · dsimp [kuttaThirdOrder]
    rw [threeStageExplicit_weight_cherry]
    norm_num

theorem oneStage_hasOrder_one (a : R) :
    HasOrder (oneStage R a) 1 := by
  rw [hasOrder_one_iff_hasOrderOne]
  exact oneStage_hasOrderOne (R := R) a

theorem oneStage_hasOrder_two_iff (a : R) :
    HasOrder (oneStage R a) 2 ↔ a = (2 : R)⁻¹ := by
  rw [hasOrder_two_iff_hasOrderOne_and_weight_chain2]
  constructor
  · intro h
    simpa using h.2
  · intro h
    exact ⟨oneStage_hasOrderOne (R := R) a, by simp [h]⟩

theorem oneStage_not_hasOrder_three [CharZero R] (a : R) :
    ¬ HasOrder (oneStage R a) 3 := by
  intro h
  rw [hasOrder_three_iff_hasOrder_two_and_weight_chain3_and_cherry] at h
  have hchain := h.2.1
  have hcherry := h.2.2
  have hbad : (6 : R)⁻¹ = (3 : R)⁻¹ := by
    calc
      (6 : R)⁻¹ = weight (oneStage R a) PTree.chain3 := hchain.symm
      _ = a ^ 2 := by simp [PTree.chain3]
      _ = weight (oneStage R a) PTree.cherry := by simp [PTree.cherry]
      _ = (3 : R)⁻¹ := hcherry
  norm_num at hbad

theorem explicitEuler_hasOrder_one :
    HasOrder (explicitEuler R) 1 := by
  rw [hasOrder_one_iff_hasOrderOne]
  exact explicitEuler_hasOrderOne (R := R)

theorem implicitEuler_hasOrder_one :
    HasOrder (implicitEuler R) 1 := by
  rw [hasOrder_one_iff_hasOrderOne]
  exact implicitEuler_hasOrderOne (R := R)

theorem twoStageExplicit_hasOrder_one {a21 b1 b2 : R}
    (hsum : b1 + b2 = 1) :
    HasOrder (twoStageExplicit R a21 b1 b2) 1 := by
  rw [hasOrder_one_iff_hasOrderOne]
  exact twoStageExplicit_hasOrderOne (R := R) hsum

theorem implicitMidpoint_weight_chain2 :
    weight (implicitMidpoint R) PTree.chain2 = (2 : R)⁻¹ := by
  simp [implicitMidpoint]

theorem implicitMidpoint_hasOrder_two :
    HasOrder (implicitMidpoint R) 2 := by
  rw [hasOrder_two_iff_hasOrderOne_and_weight_chain2]
  exact ⟨oneStage_hasOrderOne (R := R) ((2 : R)⁻¹), implicitMidpoint_weight_chain2 (R := R)⟩

theorem twoStageExplicit_hasOrder_two {a21 b1 b2 : R}
    (hsum : b1 + b2 = 1) (hprod : b2 * a21 = (2 : R)⁻¹) :
    HasOrder (twoStageExplicit R a21 b1 b2) 2 := by
  rw [hasOrder_two_iff_hasOrderOne_and_weight_chain2]
  exact ⟨twoStageExplicit_hasOrderOne (R := R) hsum, by simpa using hprod⟩

theorem explicitMidpoint_hasOrder_two :
    HasOrder (explicitMidpoint R) 2 := by
  apply twoStageExplicit_hasOrder_two
  · simp
  · simp

theorem heun_hasOrder_two_of_half_add_half
    (hhalf : (2 : R)⁻¹ + (2 : R)⁻¹ = 1) :
    HasOrder (heun R) 2 := by
  apply twoStageExplicit_hasOrder_two
  · simpa [heun] using hhalf
  · simp

theorem heun_hasOrder_two [CharZero R] :
    HasOrder (heun R) 2 := by
  apply heun_hasOrder_two_of_half_add_half
  norm_num

theorem HasOrder.treeWeight {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {τ : RootedTree} (hτ : RootedTree.order τ ≤ n) :
    treeWeight rk τ = (RootedTree.treeFactorial τ : R)⁻¹ :=
  (hasOrder_iff_treeWeight rk n).1 h τ hτ

theorem HasOrder.weight {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {t : PTree} (ht : PTree.order t ≤ n) :
    weight rk t = (PTree.treeFactorial t : R)⁻¹ :=
  (hasOrder_iff_weight rk n).1 h t ht

theorem HasOrder.weightList {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {ts : List PTree} (hts : PTree.orderList ts ≤ n) :
    weightList rk ts = (PTree.treeFactorialList ts : R)⁻¹ :=
  (hasOrder_iff_weightList rk n).1 h ts hts

theorem HasOrder.forestCoeff {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    Series.forestCoeff (series rk) φ = (RootedForest.treeFactorial φ : R)⁻¹ :=
  (hasOrder_iff_forestCoeff rk n).1 h φ hφ

theorem HasOrder.forestWeight {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    forestWeight rk φ = (RootedForest.treeFactorial φ : R)⁻¹ :=
  (hasOrder_iff_forestWeight rk n).1 h φ hφ

theorem HasOrder.toCharacter_evalForest {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    (Series.toCharacter (series rk)).evalForest φ =
      (RootedForest.treeFactorial φ : R)⁻¹ := by
  rw [toCharacter_series_evalForest]
  exact h.forestWeight hφ

theorem HasOrder.toCharacter_ofForest {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    Series.toCharacter (series rk) (ForestAlgebra.ofForest (R := R) φ) =
      (RootedForest.treeFactorial φ : R)⁻¹ := by
  rw [toCharacter_series_ofForest]
  exact h.forestWeight hφ

theorem HasOrder.of_agreeUpToOrder {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) (hrk : HasOrder rk n) :
    HasOrder rk' n :=
  (Series.hasOrder_congr h).1 hrk

theorem hasOrder_congr {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R} {n : Nat}
    (h : AgreeUpToOrder rk rk' n) :
    HasOrder rk n ↔ HasOrder rk' n :=
  Series.hasOrder_congr h

theorem hasOrder_all_congr {κ : Type u} [Fintype κ]
    {rk : RungeKutta ι R} {rk' : RungeKutta κ R}
    (h : ∀ n, AgreeUpToOrder rk rk' n) :
    (∀ n, HasOrder rk n) ↔ ∀ n, HasOrder rk' n :=
  Series.hasOrder_all_congr h

theorem HasOrder.treeWeight_graft {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {φ : RootedForest} (hφ : 1 + RootedForest.order φ ≤ n) :
    (∑ i, rk.b i * forestStageWeight rk φ i) =
      ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial φ : R)⁻¹ := by
  calc
    (∑ i, rk.b i * forestStageWeight rk φ i) =
        Series.coeff (series rk) (.tree (RootedForest.graft φ)) := by
          exact (series_graft rk φ).symm
    _ = ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial φ : R)⁻¹ := by
          exact Series.HasOrder.coeff_tree_graft h hφ

theorem HasOrder.treeWeight_branches {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {τ : RootedTree} (hτ : RootedTree.order τ ≤ n) :
    (∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i) =
      (RootedTree.order τ : R)⁻¹ *
        (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
  calc
    (∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i) =
        Series.coeff (series rk) (.tree τ) := by
          exact (series_branches rk τ).symm
    _ = (RootedTree.order τ : R)⁻¹ *
        (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
          exact Series.HasOrder.coeff_tree_branches h hτ

theorem HasOrder.treeWeight_butcherProduct {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) {φ : RootedForest} {τ : RootedTree}
    (horder : RootedForest.order φ + RootedTree.order τ ≤ n) :
    (∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
      ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  have htree :
      BSeries.RungeKutta.treeWeight rk (RootedForest.butcherProduct φ τ) =
        (RootedTree.treeFactorial (RootedForest.butcherProduct φ τ) : R)⁻¹ :=
    (hasOrder_iff_treeWeight rk n).1 h
      (RootedForest.butcherProduct φ τ) (by simpa using horder)
  calc
    (∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
        BSeries.RungeKutta.treeWeight rk (RootedForest.butcherProduct φ τ) := by
          exact (BSeries.RungeKutta.treeWeight_butcherProduct rk φ τ).symm
    _ = (RootedTree.treeFactorial (RootedForest.butcherProduct φ τ) : R)⁻¹ := htree
    _ = ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
          simp [RootedForest.treeFactorial_butcherProduct]
          ac_rfl

theorem hasOrder_iff_treeWeight_butcherProduct (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ (φ : RootedForest) (τ : RootedTree),
        RootedForest.order φ + RootedTree.order τ ≤ n →
          (∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
            ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
              (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  rw [HasOrder, Series.hasOrder_iff_coeff_butcherProduct]
  constructor
  · rintro ⟨_, h⟩ φ τ horder
    have htree := h φ τ horder
    change
      treeWeight rk (RootedForest.butcherProduct φ τ) =
        ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
          (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ at htree
    calc
      (∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
          treeWeight rk (RootedForest.butcherProduct φ τ) := by
            exact (treeWeight_butcherProduct rk φ τ).symm
      _ = ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
            (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := htree
  · intro h
    exact ⟨series_hasUnitConstant rk, fun φ τ horder => by
      calc
        Series.coeff (series rk) (TreeIndex.tree (RootedForest.butcherProduct φ τ)) =
            treeWeight rk (RootedForest.butcherProduct φ τ) := rfl
        _ = ∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i) := by
            exact treeWeight_butcherProduct rk φ τ
        _ = ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
              (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ :=
            h φ τ horder⟩

theorem hasOrder_iff_treeWeight_graft (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk n ↔
      ∀ φ : RootedForest, 1 + RootedForest.order φ ≤ n →
        (∑ i, rk.b i * forestStageWeight rk φ i) =
          ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
            (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ hφ
    exact h.treeWeight_graft hφ
  · intro h
    rw [hasOrder_iff_treeWeight]
    intro τ hτ
    calc
      treeWeight rk τ =
          ∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i :=
            treeWeight_branches rk τ
      _ = ((1 + RootedForest.order (RootedTree.branches τ) : Nat) : R)⁻¹ *
            (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
            exact h (RootedTree.branches τ) (by
              rw [RootedForest.order_branches τ]
              exact hτ)
      _ = (RootedTree.treeFactorial τ : R)⁻¹ := by
            simpa [Series.coeff, Series.exact] using
              (Series.coeff_exact_tree_branches (R := R) τ).symm

theorem hasOrder_zero (rk : RungeKutta ι R) : HasOrder rk 0 := by
  rw [hasOrder_iff_treeWeight]
  intro τ hτ
  have hpos := RootedTree.order_pos τ
  omega

theorem series_eq_exact_of_hasOrder_all {rk : RungeKutta ι R}
    (h : ∀ n, HasOrder rk n) : series rk = Series.exact R :=
  Series.eq_exact_of_hasOrder_all (fun n => h n)

theorem hasOrder_all_iff_series_eq_exact (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔ series rk = Series.exact R := by
  constructor
  · exact series_eq_exact_of_hasOrder_all
  · intro h n
    change Series.HasOrder (series rk) n
    rw [h]
    exact Series.exact_hasOrder n

theorem hasOrder_all_iff_coeff (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ ξ : TreeIndex, Series.coeff (series rk) ξ = Series.coeff (Series.exact R) ξ := by
  rw [hasOrder_all_iff_series_eq_exact]
  constructor
  · intro h ξ
    rw [h]
  · intro h
    funext ξ
    exact h ξ

theorem hasOrder_all_iff_toCharacter_eq_exact (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      Series.toCharacter (series rk) = Series.toCharacter (Series.exact R) := by
  constructor
  · intro h
    exact ((Series.hasOrder_all_iff_toCharacter_eq_exact (a := series rk)).1 h).2
  · intro h n
    change Series.HasOrder (series rk) n
    exact ((Series.hasOrder_all_iff_toCharacter_eq_exact (a := series rk)).2
      ⟨series_hasUnitConstant rk, h⟩) n

theorem characterEquiv_hasOrder_all_iff_exact (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      Series.characterEquiv ⟨series rk, series_hasUnitConstant rk⟩ =
        Series.characterEquiv ⟨Series.exact R, Series.exact_hasUnitConstant⟩ := by
  change (∀ n, Series.HasOrder (series rk) n) ↔
    Series.characterEquiv ⟨series rk, series_hasUnitConstant rk⟩ =
      Series.characterEquiv ⟨Series.exact R, Series.exact_hasUnitConstant⟩
  exact Series.characterEquiv_hasOrder_all_iff_exact ⟨series rk, series_hasUnitConstant rk⟩

theorem hasOrder_all_iff_treeWeight (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ τ : RootedTree,
        treeWeight rk τ = (RootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h τ
    exact (h (RootedTree.order τ)).treeWeight le_rfl
  · intro h n
    rw [hasOrder_iff_treeWeight]
    intro τ hτ
    exact h τ

theorem hasOrder_all_iff_treeCoeff (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ τ : RootedTree,
        Series.coeff (series rk) (TreeIndex.tree τ) =
          (RootedTree.treeFactorial τ : R)⁻¹ := by
  simpa [Series.coeff] using hasOrder_all_iff_treeWeight (R := R) rk

theorem hasOrder_all_iff_weight (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ t : PTree, weight rk t = (PTree.treeFactorial t : R)⁻¹ := by
  constructor
  · intro h t
    exact (h (PTree.order t)).weight le_rfl
  · intro h n
    rw [hasOrder_iff_weight]
    intro t ht
    exact h t

theorem hasOrder_all_iff_forestWeight (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : RootedForest,
        forestWeight rk φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ
    exact (h (RootedForest.order φ)).forestWeight le_rfl
  · intro h n
    rw [hasOrder_iff_forestWeight]
    intro φ hφ
    exact h φ

theorem hasOrder_all_iff_forestCoeff (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : RootedForest,
        Series.forestCoeff (series rk) φ =
          (RootedForest.treeFactorial φ : R)⁻¹ := by
  simpa using hasOrder_all_iff_forestWeight (R := R) rk

theorem hasOrder_all_iff_toCharacter_evalForest (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : RootedForest,
        (Series.toCharacter (series rk)).evalForest φ =
          (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ
    exact (h (RootedForest.order φ)).toCharacter_evalForest le_rfl
  · intro h n
    rw [hasOrder_iff_toCharacter_evalForest]
    intro φ hφ
    exact h φ

theorem hasOrder_all_iff_toCharacter_ofForest (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : RootedForest,
        Series.toCharacter (series rk) (ForestAlgebra.ofForest (R := R) φ) =
          (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ
    exact (h (RootedForest.order φ)).toCharacter_ofForest le_rfl
  · intro h n
    rw [hasOrder_iff_toCharacter_ofForest]
    intro φ hφ
    exact h φ

theorem hasOrder_all_iff_treeWeight_graft (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ φ : RootedForest,
        (∑ i, rk.b i * forestStageWeight rk φ i) =
          ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
            (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h φ
    exact (h (1 + RootedForest.order φ)).treeWeight_graft le_rfl
  · intro h n
    rw [hasOrder_iff_treeWeight_graft]
    intro φ hφ
    exact h φ

theorem hasOrder_all_iff_treeWeight_branches (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ τ : RootedTree,
        (∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i) =
          (RootedTree.order τ : R)⁻¹ *
            (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h τ
    exact (h (RootedTree.order τ)).treeWeight_branches le_rfl
  · intro h
    rw [hasOrder_all_iff_treeWeight]
    intro τ
    calc
      treeWeight rk τ =
          ∑ i, rk.b i * forestStageWeight rk (RootedTree.branches τ) i :=
            treeWeight_branches rk τ
      _ = (RootedTree.order τ : R)⁻¹ *
            (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ :=
            h τ
      _ = (RootedTree.treeFactorial τ : R)⁻¹ := by
            simpa [Series.coeff, Series.exact] using
              (Series.coeff_exact_tree_branches (R := R) τ).symm

theorem hasOrder_all_iff_treeWeight_butcherProduct (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ (φ : RootedForest) (τ : RootedTree),
        (∑ i, rk.b i * (forestStageWeight rk φ i * treeStageWeight rk τ i)) =
          ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
            (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h φ τ
    exact (h (RootedForest.order φ + RootedTree.order τ)).treeWeight_butcherProduct le_rfl
  · intro h n
    rw [hasOrder_iff_treeWeight_butcherProduct]
    intro φ τ horder
    exact h φ τ

theorem hasOrder_all_iff_weightList (rk : RungeKutta ι R) :
    (∀ n, HasOrder rk n) ↔
      ∀ ts : List PTree, weightList rk ts = (PTree.treeFactorialList ts : R)⁻¹ := by
  constructor
  · intro h ts
    exact (h (PTree.orderList ts)).weightList le_rfl
  · intro h n
    rw [hasOrder_iff_weightList]
    intro ts hts
    exact h ts

theorem HasOrder.mono {rk : RungeKutta ι R} {m n : Nat}
    (h : HasOrder rk n) (hmn : m ≤ n) : HasOrder rk m :=
  Series.HasOrder.mono h hmn

theorem oneStage_hasOrder_iff [CharZero R] (a : R) (n : Nat) :
    HasOrder (oneStage R a) n ↔
      n ≤ 1 ∨ n = 2 ∧ a = (2 : R)⁻¹ := by
  constructor
  · intro h
    by_cases hn1 : n ≤ 1
    · exact Or.inl hn1
    · by_cases hn2 : n = 2
      · have htwo : HasOrder (oneStage R a) 2 := h.mono (by omega)
        exact Or.inr ⟨hn2, (oneStage_hasOrder_two_iff (R := R) a).1 htwo⟩
      · have hn3 : 3 ≤ n := by omega
        exact False.elim ((oneStage_not_hasOrder_three (R := R) a) (h.mono hn3))
  · rintro (hn | ⟨rfl, ha⟩)
    · exact (oneStage_hasOrder_one (R := R) a).mono hn
    · exact (oneStage_hasOrder_two_iff (R := R) a).2 ha

theorem hasOrder_succ_iff_treeWeight (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ τ : RootedTree, RootedTree.order τ = n + 1 →
          treeWeight rk τ = (RootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun τ hτ => h.treeWeight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_treeWeight]
    intro τ hτ
    by_cases hle : RootedTree.order τ ≤ n
    · exact hprev.treeWeight hle
    · exact htop τ (by omega)

theorem hasOrder_succ_iff_weight (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ t : PTree, PTree.order t = n + 1 →
          weight rk t = (PTree.treeFactorial t : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun t ht => h.weight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_weight]
    intro t ht
    by_cases hle : PTree.order t ≤ n
    · exact hprev.weight hle
    · exact htop t (by omega)

theorem hasOrder_succ_iff_forestWeight (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ φ : RootedForest, RootedForest.order φ = n + 1 →
          forestWeight rk φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun φ hφ => h.forestWeight (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_forestWeight]
    intro φ hφ
    by_cases hle : RootedForest.order φ ≤ n
    · exact hprev.forestWeight hle
    · exact htop φ (by omega)

theorem hasOrder_succ_iff_weightList (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ ts : List PTree, PTree.orderList ts = n + 1 →
          weightList rk ts = (PTree.treeFactorialList ts : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun ts hts => h.weightList (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_weightList]
    intro ts hts
    by_cases hle : PTree.orderList ts ≤ n
    · exact hprev.weightList hle
    · exact htop ts (by omega)

theorem hasOrder_succ_iff_toCharacter_evalForest
    (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ φ : RootedForest, RootedForest.order φ = n + 1 →
          (Series.toCharacter (series rk)).evalForest φ =
            (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n),
      fun φ hφ => h.toCharacter_evalForest (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_toCharacter_evalForest]
    intro φ hφ
    by_cases hle : RootedForest.order φ ≤ n
    · exact hprev.toCharacter_evalForest hle
    · exact htop φ (by omega)

theorem hasOrder_succ_iff_toCharacter_ofForest
    (rk : RungeKutta ι R) (n : Nat) :
    HasOrder rk (n + 1) ↔
      HasOrder rk n ∧
        ∀ φ : RootedForest, RootedForest.order φ = n + 1 →
          Series.toCharacter (series rk) (ForestAlgebra.ofForest (R := R) φ) =
            (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n),
      fun φ hφ => h.toCharacter_ofForest (by omega)⟩
  · rintro ⟨hprev, htop⟩
    rw [hasOrder_iff_toCharacter_ofForest]
    intro φ hφ
    by_cases hle : RootedForest.order φ ≤ n
    · exact hprev.toCharacter_ofForest hle
    · exact htop φ (by omega)

theorem HasOrder.hasOrderOne {rk : RungeKutta ι R} {n : Nat}
    (h : HasOrder rk n) (hn : 1 ≤ n) : HasOrderOne rk :=
  (hasOrder_one_iff_hasOrderOne rk).1 (h.mono hn)

end Field

end RungeKutta

end BSeries
