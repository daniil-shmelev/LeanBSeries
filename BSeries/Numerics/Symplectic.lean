/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.RungeKutta

/-!
# Symplecticity of Runge–Kutta methods

The algebraic theory of symplectic Runge–Kutta schemes (Sanz-Serna;
Hairer–Lubich–Wanner VI.4, VI.7):

* `RungeKutta.IsSymplectic` — the tableau condition
  `bᵢaᵢⱼ + bⱼaⱼᵢ = bᵢbⱼ`;
* `symplectic_defect` — the **Calvo–Sanz-Serna defect identity**: for
  all rooted trees `u, v`,
  `Φ(u ∘ v) + Φ(v ∘ u) − Φ(u)·Φ(v) = ∑ᵢⱼ (bᵢaᵢⱼ + bⱼaⱼᵢ − bᵢbⱼ)·Φᵢ(u)·Φⱼ(v)`
  where `u ∘ v` is the Butcher product (grafting `v` onto the root of
  `u`) and `Φᵢ` are the stage weights;
* `IsSymplectic.isSymplecticCharacter` — a symplectic tableau
  therefore has a **symplectic B-series**: its elementary weights
  satisfy the pair condition `a(u∘v) + a(v∘u) = a(u)·a(v)`
  (`IsSymplecticCharacter`), which characterises symplectic B-series
  methods;
* the implicit midpoint rule is symplectic, the explicit Euler method
  is not.

The analytic statement — that the numerical flow of a symplectic
method preserves the symplectic form for Hamiltonian systems — is
outside the current scope; this file provides the complete tableau- and
B-series-level theory.
-/

namespace BSeries

open HopfAlgebras

universe u v

namespace RungeKutta

variable {ι : Type u} {R : Type v} [Fintype ι]

/-- The **symplecticity condition** on a Runge–Kutta tableau:
`bᵢaᵢⱼ + bⱼaⱼᵢ = bᵢbⱼ` for all stages `i, j`. -/
def IsSymplectic [Mul R] [Add R] (rk : RungeKutta ι R) : Prop :=
  ∀ i j : ι, rk.b i * rk.A i j + rk.b j * rk.A j i = rk.b i * rk.b j

/-- A coefficient system on rooted trees is a **symplectic character**
when it satisfies the Calvo–Sanz-Serna pair condition
`a(u ∘ v) + a(v ∘ u) = a(u)·a(v)` for the Butcher product. -/
def IsSymplecticCharacter [Mul R] [Add R] (a : RootedTree → R) : Prop :=
  ∀ u v : RootedTree,
    a (RootedForest.butcherProduct (RootedForest.singleton v) u) +
      a (RootedForest.butcherProduct (RootedForest.singleton u) v) =
    a u * a v

section CommRing

variable [CommRing R]

/-- Elementary weight of a Butcher product, as a double stage sum. -/
private theorem treeWeight_butcherProduct_expand (rk : RungeKutta ι R)
    (x y : RootedTree) :
    treeWeight rk (RootedForest.butcherProduct
        (RootedForest.singleton y) x) =
      ∑ i, ∑ j, rk.b i * rk.A i j *
        (treeStageWeight rk x i * treeStageWeight rk y j) := by
  rw [treeWeight_butcherProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [forestStageWeight_singleton, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The Calvo–Sanz-Serna defect identity**: the failure of the
elementary weights to be a symplectic character is the tableau defect
`bᵢaᵢⱼ + bⱼaⱼᵢ − bᵢbⱼ` paired against the stage weights. -/
theorem symplectic_defect (rk : RungeKutta ι R) (u v : RootedTree) :
    treeWeight rk (RootedForest.butcherProduct
        (RootedForest.singleton v) u) +
      treeWeight rk (RootedForest.butcherProduct
        (RootedForest.singleton u) v) -
      treeWeight rk u * treeWeight rk v =
    ∑ i, ∑ j, (rk.b i * rk.A i j + rk.b j * rk.A j i -
        rk.b i * rk.b j) *
      (treeStageWeight rk u i * treeStageWeight rk v j) := by
  have h1 := treeWeight_butcherProduct_expand rk u v
  have h2 : treeWeight rk (RootedForest.butcherProduct
      (RootedForest.singleton u) v) =
      ∑ i, ∑ j, rk.b j * rk.A j i *
        (treeStageWeight rk u i * treeStageWeight rk v j) := by
    rw [treeWeight_butcherProduct_expand rk v u, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : treeWeight rk u * treeWeight rk v =
      ∑ i, ∑ j, rk.b i * rk.b j *
        (treeStageWeight rk u i * treeStageWeight rk v j) := by
    rw [treeWeight_eq_sum_treeStageWeight, treeWeight_eq_sum_treeStageWeight,
      Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Symplectic tableaux have symplectic B-series**: under the
tableau condition, the elementary weights satisfy the pair condition
`Φ(u∘v) + Φ(v∘u) = Φ(u)·Φ(v)`. -/
theorem IsSymplectic.isSymplecticCharacter {rk : RungeKutta ι R}
    (h : rk.IsSymplectic) :
    IsSymplecticCharacter (treeWeight rk) := by
  intro u v
  have hd := symplectic_defect rk u v
  have hz : (∑ i, ∑ j, (rk.b i * rk.A i j + rk.b j * rk.A j i -
      rk.b i * rk.b j) *
      (treeStageWeight rk u i * treeStageWeight rk v j)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [show rk.b i * rk.A i j + rk.b j * rk.A j i - rk.b i * rk.b j =
      0 from by rw [h i j]; ring, zero_mul]
  rw [hz] at hd
  exact sub_eq_zero.mp hd

end CommRing

/-! ### Examples: the implicit midpoint rule is symplectic, the
explicit Euler method is not -/

/-- **The implicit midpoint rule** `oneStage ℚ (1/2)` satisfies the
symplecticity condition. -/
theorem oneStage_half_isSymplectic :
    IsSymplectic (oneStage ℚ (1 / 2)) := by
  intro i j
  show (1 : ℚ) * (1 / 2) + 1 * (1 / 2) = 1 * 1
  norm_num

/-- **The explicit Euler method** `oneStage ℚ 0` violates the
symplecticity condition. -/
theorem oneStage_zero_not_isSymplectic :
    ¬ IsSymplectic (oneStage ℚ 0) := by
  intro h
  have := h PUnit.unit PUnit.unit
  rw [show (oneStage ℚ 0).b PUnit.unit = 1 from rfl,
    show (oneStage ℚ 0).A PUnit.unit PUnit.unit = 0 from rfl] at this
  norm_num at this

end RungeKutta

end BSeries
