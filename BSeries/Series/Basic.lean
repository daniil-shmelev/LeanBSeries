/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Algebra.Forest

/-!
# B-Series

This file defines B-series and their algebraic structure.

## Main definitions

* `Series` - coefficient families indexed by rooted trees
* `Series.toCharacter` - multiplicative extension to the rooted-forest algebra
* `Series.characterEquiv` - equivalence between unit-constant series and forest characters
* `Series.unit` - convolution identity coefficients
* `Series.exact` - exact-flow B-series coefficients
* `Series.scaledExact` - exact-flow coefficients with a time/step-size parameter
* `Series.AgreeUpToOrder` - coefficient agreement through a tree order
* `Series.HasOrder` - order conditions relative to the exact-flow coefficients

## References

* John C. Butcher, *Numerical Methods for Ordinary Differential Equations*
* Philippe Chartier, Ernst Hairer, Gilles Vilmart,
  *Algebraic Structures of B-series*
-/

namespace BSeries

open HopfAlgebras

universe u v

/-- A B-series over `R`, represented by its coefficients indexed by `TreeIndex`. -/
abbrev Series (R : Type u) : Type u :=
  TreeIndex → R

namespace Series

variable {R : Type u} {S : Type v}

/-- The coefficient of a rooted tree index in a B-series. -/
def coeff (a : Series R) (τ : TreeIndex) : R :=
  a τ

@[simp]
theorem coeff_apply (a : Series R) (τ : TreeIndex) : coeff a τ = a τ :=
  rfl

@[ext]
theorem ext {a b : Series R} (h : ∀ τ, coeff a τ = coeff b τ) : a = b := by
  funext τ
  exact h τ

/-- The coefficient of the empty tree. -/
def constantCoeff (a : Series R) : R :=
  coeff a TreeIndex.empty

@[simp]
theorem coeff_empty (a : Series R) : coeff a TreeIndex.empty = constantCoeff a :=
  rfl

section Pointwise

@[simp]
theorem coeff_zero [Zero R] (τ : TreeIndex) : coeff (0 : Series R) τ = 0 :=
  rfl

@[simp]
theorem coeff_add [Add R] (a b : Series R) (τ : TreeIndex) :
    coeff (a + b) τ = coeff a τ + coeff b τ :=
  rfl

@[simp]
theorem coeff_neg [Neg R] (a : Series R) (τ : TreeIndex) :
    coeff (-a) τ = -coeff a τ :=
  rfl

@[simp]
theorem coeff_sub [Sub R] (a b : Series R) (τ : TreeIndex) :
    coeff (a - b) τ = coeff a τ - coeff b τ :=
  rfl

@[simp]
theorem coeff_smul [SMul S R] (c : S) (a : Series R) (τ : TreeIndex) :
    coeff (c • a) τ = c • coeff a τ :=
  rfl

end Pointwise

@[simp]
theorem constantCoeff_zero [Zero R] : constantCoeff (0 : Series R) = 0 :=
  rfl

@[simp]
theorem constantCoeff_add [Add R] (a b : Series R) :
    constantCoeff (a + b) = constantCoeff a + constantCoeff b :=
  rfl

@[simp]
theorem constantCoeff_neg [Neg R] (a : Series R) :
    constantCoeff (-a) = -constantCoeff a :=
  rfl

@[simp]
theorem constantCoeff_sub [Sub R] (a b : Series R) :
    constantCoeff (a - b) = constantCoeff a - constantCoeff b :=
  rfl

@[simp]
theorem constantCoeff_smul [SMul S R] (c : S) (a : Series R) :
    constantCoeff (c • a) = c • constantCoeff a :=
  rfl

/-- The condition `a(∅) = 1`, used for B-series considered as maps. -/
def HasUnitConstant [One R] (a : Series R) : Prop :=
  constantCoeff a = 1

theorem HasUnitConstant.coeff_empty [One R] {a : Series R}
    (h : HasUnitConstant a) : coeff a TreeIndex.empty = 1 :=
  h

/-- The condition `a(∅) = 0`, used for B-series considered as vector fields. -/
def HasZeroConstant [Zero R] (a : Series R) : Prop :=
  constantCoeff a = 0

theorem HasZeroConstant.coeff_empty [Zero R] {a : Series R}
    (h : HasZeroConstant a) : coeff a TreeIndex.empty = 0 :=
  h

theorem zero_hasZeroConstant [Zero R] : HasZeroConstant (0 : Series R) :=
  rfl

theorem HasZeroConstant.add [AddMonoid R] {a b : Series R}
    (ha : HasZeroConstant a) (hb : HasZeroConstant b) :
    HasZeroConstant (a + b) := by
  change constantCoeff a + constantCoeff b = 0
  rw [ha, hb]
  simp

theorem HasZeroConstant.neg [AddGroup R] {a : Series R}
    (ha : HasZeroConstant a) : HasZeroConstant (-a) := by
  change -constantCoeff a = 0
  rw [ha]
  simp

theorem HasZeroConstant.sub [AddGroup R] {a b : Series R}
    (ha : HasZeroConstant a) (hb : HasZeroConstant b) :
    HasZeroConstant (a - b) := by
  change constantCoeff a - constantCoeff b = 0
  rw [ha, hb]
  simp

theorem HasZeroConstant.smul [Zero R] [SMulZeroClass S R] {a : Series R}
    (c : S) (ha : HasZeroConstant a) : HasZeroConstant (c • a) := by
  change c • constantCoeff a = 0
  rw [ha]
  simp

section ForestCharacter

noncomputable section

variable [CommSemiring R]

/-- Multiplicative coefficient of a rooted forest induced by a tree-indexed series. -/
def forestCoeff (a : Series R) (φ : RootedForest) : R :=
  (φ.map fun τ => coeff a (.tree τ)).prod

@[simp]
theorem forestCoeff_zero (a : Series R) : forestCoeff a 0 = 1 := by
  simp [forestCoeff]

@[simp]
theorem forestCoeff_empty (a : Series R) :
    forestCoeff a RootedForest.empty = 1 := by
  simp [RootedForest.empty]

@[simp]
theorem forestCoeff_singleton (a : Series R) (τ : RootedTree) :
    forestCoeff a (RootedForest.singleton τ) = coeff a (.tree τ) := by
  simp [forestCoeff, RootedForest.singleton]

@[simp]
theorem forestCoeff_singleton_mset (a : Series R) (τ : RootedTree) :
    forestCoeff a ({τ} : RootedForest) = coeff a (.tree τ) := by
  simp [forestCoeff]

@[simp]
theorem forestCoeff_add (a : Series R) (φ ψ : RootedForest) :
    forestCoeff a (φ + ψ) = forestCoeff a φ * forestCoeff a ψ := by
  simp [forestCoeff, Multiset.map_add]

private def forestCoeffMonoidHom (a : Series R) :
    Multiplicative RootedForest →* R where
  toFun φ := forestCoeff a (Multiplicative.toAdd φ)
  map_one' := by
    change forestCoeff a (0 : RootedForest) = 1
    simp
  map_mul' φ ψ := by
    change
      forestCoeff a (Multiplicative.toAdd (φ * ψ)) =
        forestCoeff a (Multiplicative.toAdd φ) * forestCoeff a (Multiplicative.toAdd ψ)
    change
      forestCoeff a (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) =
        forestCoeff a (Multiplicative.toAdd φ) * forestCoeff a (Multiplicative.toAdd ψ)
    simp

/-- The forest-algebra character induced by the tree coefficients of a series. -/
def toCharacter (a : Series R) : ForestAlgebra.Character R :=
  (AddMonoidAlgebra.lift R R RootedForest) (forestCoeffMonoidHom a)

@[simp]
theorem toCharacter_ofForest (a : Series R) (φ : RootedForest) :
    toCharacter a (ForestAlgebra.ofForest (R := R) φ) = forestCoeff a φ := by
  simp [toCharacter, ForestAlgebra.ofForest, forestCoeffMonoidHom]

@[simp]
theorem toCharacter_evalForest (a : Series R) (φ : RootedForest) :
    (toCharacter a).evalForest φ = forestCoeff a φ := by
  simp [ForestAlgebra.Character.evalForest]

@[simp]
theorem toCharacter_ofForest_zero (a : Series R) :
    toCharacter a (ForestAlgebra.ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem toCharacter_ofForest_singleton (a : Series R) (τ : RootedTree) :
    toCharacter a (ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ)) =
      coeff a (.tree τ) := by
  simp

/-- Unit-constant series are determined by their induced forest-algebra characters. -/
theorem ext_of_toCharacter_eq {a b : Series R}
    (ha : HasUnitConstant a) (hb : HasUnitConstant b)
    (h : toCharacter a = toCharacter b) : a = b := by
  funext τ
  cases τ with
  | empty =>
      change constantCoeff a = constantCoeff b
      exact ha.trans hb.symm
  | tree τ =>
      have hτ :=
        congrArg
          (fun χ : ForestAlgebra.Character R =>
            χ (ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ))) h
      simpa using hτ

theorem toCharacter_eq_iff {a b : Series R}
    (ha : HasUnitConstant a) (hb : HasUnitConstant b) :
    toCharacter a = toCharacter b ↔ a = b := by
  constructor
  · exact ext_of_toCharacter_eq ha hb
  · intro h
    rw [h]

/-- Recover the unit-constant B-series determined by a forest-algebra character. -/
def ofCharacter (χ : ForestAlgebra.Character R) : Series R
  | .empty => 1
  | .tree τ => χ.evalForest (RootedForest.singleton τ)

@[simp]
theorem ofCharacter_empty (χ : ForestAlgebra.Character R) :
    coeff (ofCharacter χ) TreeIndex.empty = 1 :=
  rfl

@[simp]
theorem ofCharacter_tree (χ : ForestAlgebra.Character R) (τ : RootedTree) :
    coeff (ofCharacter χ) (.tree τ) = χ.evalForest (RootedForest.singleton τ) :=
  rfl

theorem ofCharacter_hasUnitConstant (χ : ForestAlgebra.Character R) :
    HasUnitConstant (ofCharacter χ) :=
  rfl

@[simp]
theorem toCharacter_ofCharacter (χ : ForestAlgebra.Character R) :
    toCharacter (ofCharacter χ) = χ := by
  apply ForestAlgebra.Character.ext_tree
  intro τ
  change
    toCharacter (ofCharacter χ)
        (ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ)) =
      χ (ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ))
  rw [toCharacter_ofForest_singleton]
  rfl

theorem ofCharacter_toCharacter {a : Series R} (ha : HasUnitConstant a) :
    ofCharacter (toCharacter a) = a := by
  funext τ
  cases τ with
  | empty =>
      change 1 = a TreeIndex.empty
      exact ha.symm
  | tree τ =>
      change
        toCharacter a (ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ)) =
          a (TreeIndex.tree τ)
      rw [toCharacter_ofForest_singleton]
      rfl

theorem forestCoeff_ofCharacter (χ : ForestAlgebra.Character R) (φ : RootedForest) :
    forestCoeff (ofCharacter χ) φ = χ.evalForest φ := by
  rw [← toCharacter_ofForest (ofCharacter χ) φ]
  rw [toCharacter_ofCharacter]
  rfl

/-- Unit-constant B-series are equivalent to forest-algebra characters. -/
def characterEquiv : {a : Series R // HasUnitConstant a} ≃ ForestAlgebra.Character R where
  toFun a := toCharacter a.1
  invFun χ := ⟨ofCharacter χ, ofCharacter_hasUnitConstant χ⟩
  left_inv a := by
    cases a with
    | mk a ha =>
        apply Subtype.ext
        exact ofCharacter_toCharacter ha
  right_inv χ := toCharacter_ofCharacter χ

@[simp]
theorem characterEquiv_apply (a : {a : Series R // HasUnitConstant a}) :
    characterEquiv a = toCharacter a.1 :=
  rfl

@[simp]
theorem characterEquiv_symm_apply (χ : ForestAlgebra.Character R) :
    ((characterEquiv (R := R)).symm χ).1 = ofCharacter χ :=
  rfl

theorem characterEquiv_symm_forestCoeff
    (χ : ForestAlgebra.Character R) (φ : RootedForest) :
    forestCoeff ((characterEquiv (R := R)).symm χ).1 φ = χ.evalForest φ := by
  simp [forestCoeff_ofCharacter]

end

end ForestCharacter

/-- The convolution identity B-series: `1` on the empty tree and `0` on every tree. -/
def unit (R : Type u) [Zero R] [One R] : Series R
  | .empty => 1
  | .tree _ => 0

@[simp]
theorem coeff_unit_empty [Zero R] [One R] :
    coeff (unit R) TreeIndex.empty = 1 :=
  rfl

@[simp]
theorem coeff_unit_tree [Zero R] [One R] (τ : RootedTree) :
    coeff (unit R) (.tree τ) = 0 :=
  rfl

theorem unit_hasUnitConstant [Zero R] [One R] : HasUnitConstant (unit R) :=
  rfl

theorem forestCoeff_unit [CommSemiring R] (φ : RootedForest) :
    forestCoeff (unit R) φ = ForestAlgebra.counitCoeff (R := R) φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  cases ts with
  | nil =>
      simp [forestCoeff, unit, ForestAlgebra.counitCoeff]
  | cons τ ts =>
      have hne : (((τ :: ts) : List RootedTree) : RootedForest) ≠ 0 :=
        (RootedForest.order_pos_iff_ne_zero _).1 (RootedForest.order_coe_cons_pos τ ts)
      simp [forestCoeff, unit, ForestAlgebra.counitCoeff, hne]

@[simp]
theorem toCharacter_unit_ofForest [CommSemiring R] (φ : RootedForest) :
    toCharacter (unit R) (ForestAlgebra.ofForest (R := R) φ) =
      ForestAlgebra.counitCoeff (R := R) φ := by
  simp [forestCoeff_unit]

theorem toCharacter_unit [CommSemiring R] :
    toCharacter (unit R) = ForestAlgebra.counit R := by
  apply ForestAlgebra.Character.ext
  intro φ
  simp [ForestAlgebra.Character.evalForest, forestCoeff_unit]

theorem ofCharacter_counit [CommSemiring R] :
    ofCharacter (ForestAlgebra.counit R) = unit R := by
  apply ext_of_toCharacter_eq
  · exact ofCharacter_hasUnitConstant _
  · exact unit_hasUnitConstant
  · rw [toCharacter_ofCharacter, toCharacter_unit]

theorem characterEquiv_unit_counit [CommSemiring R] :
    characterEquiv ⟨unit R, unit_hasUnitConstant⟩ = ForestAlgebra.counit R := by
  exact toCharacter_unit

theorem characterEquiv_symm_counit [CommSemiring R] :
    ((characterEquiv (R := R)).symm (ForestAlgebra.counit R)).1 = unit R := by
  simpa [characterEquiv_symm_apply] using ofCharacter_counit (R := R)

/-- Exact-flow B-series coefficients, recursively given by the inverse tree factorial. -/
def exact (R : Type u) [DivisionSemiring R] : Series R :=
  fun τ => (TreeIndex.treeFactorial τ : R)⁻¹

@[simp]
theorem coeff_exact [DivisionSemiring R] (τ : TreeIndex) :
    coeff (exact R) τ = (TreeIndex.treeFactorial τ : R)⁻¹ :=
  rfl

/-- Exact-flow B-series coefficients at time/step-size `h`. -/
def scaledExact [DivisionSemiring R] (h : R) : Series R :=
  fun τ => h ^ TreeIndex.order τ * (TreeIndex.treeFactorial τ : R)⁻¹

@[simp]
theorem coeff_scaledExact [DivisionSemiring R] (h : R) (τ : TreeIndex) :
    coeff (scaledExact h) τ =
      h ^ TreeIndex.order τ * (TreeIndex.treeFactorial τ : R)⁻¹ :=
  rfl

@[simp]
theorem scaledExact_one [DivisionSemiring R] : scaledExact (1 : R) = exact R := by
  funext τ
  simp [scaledExact, exact]

@[simp]
theorem scaledExact_zero [DivisionSemiring R] : scaledExact (0 : R) = unit R := by
  funext τ
  cases τ with
  | empty =>
      simp [scaledExact, unit]
  | tree τ =>
      have hτ : RootedTree.order τ ≠ 0 := Nat.ne_of_gt (RootedTree.order_pos τ)
      simp [scaledExact, unit, hτ]

theorem scaledExact_hasUnitConstant [DivisionSemiring R] (h : R) :
    HasUnitConstant (scaledExact h) := by
  simp [HasUnitConstant, constantCoeff, coeff, scaledExact]

theorem coeff_exact_tree_graft [Field R] (φ : RootedForest) :
    coeff (exact R) (.tree (RootedForest.graft φ)) =
      ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial φ : R)⁻¹ := by
  simp [exact, RootedForest.treeFactorial_graft]
  ac_rfl

theorem coeff_scaledExact_tree_graft [Field R] (h : R) (φ : RootedForest) :
    coeff (scaledExact h) (.tree (RootedForest.graft φ)) =
      h ^ (1 + RootedForest.order φ) *
        ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
          (RootedForest.treeFactorial φ : R)⁻¹ := by
  simp [scaledExact, RootedForest.treeFactorial_graft]
  ring

theorem coeff_exact_tree_branches [Field R] (τ : RootedTree) :
    coeff (exact R) (.tree τ) =
      (RootedTree.order τ : R)⁻¹ *
        (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
  calc
    coeff (exact R) (.tree τ) =
        coeff (exact R) (.tree (RootedForest.graft (RootedTree.branches τ))) := by
          rw [RootedForest.graft_branches τ]
    _ = ((1 + RootedForest.order (RootedTree.branches τ) : Nat) : R)⁻¹ *
          (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
          exact coeff_exact_tree_graft (R := R) (RootedTree.branches τ)
    _ = (RootedTree.order τ : R)⁻¹ *
          (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
          rw [RootedForest.order_branches τ]

theorem coeff_scaledExact_tree_branches [Field R] (h : R) (τ : RootedTree) :
    coeff (scaledExact h) (.tree τ) =
      h ^ RootedTree.order τ *
        (RootedTree.order τ : R)⁻¹ *
          (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
  calc
    coeff (scaledExact h) (.tree τ) =
        coeff (scaledExact h) (.tree (RootedForest.graft (RootedTree.branches τ))) := by
          rw [RootedForest.graft_branches τ]
    _ = h ^ (1 + RootedForest.order (RootedTree.branches τ)) *
          ((1 + RootedForest.order (RootedTree.branches τ) : Nat) : R)⁻¹ *
            (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
          exact coeff_scaledExact_tree_graft h (RootedTree.branches τ)
    _ = h ^ RootedTree.order τ *
          (RootedTree.order τ : R)⁻¹ *
            (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
          rw [RootedForest.order_branches τ]

theorem coeff_exact_tree_butcherProduct [Field R] (φ : RootedForest) (τ : RootedTree) :
    coeff (exact R) (.tree (RootedForest.butcherProduct φ τ)) =
      ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  simp [exact, RootedForest.treeFactorial_butcherProduct]
  ac_rfl

theorem coeff_scaledExact_tree_butcherProduct [Field R] (h : R)
    (φ : RootedForest) (τ : RootedTree) :
    coeff (scaledExact h) (.tree (RootedForest.butcherProduct φ τ)) =
      h ^ (RootedForest.order φ + RootedTree.order τ) *
        ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
          (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  simp [scaledExact, RootedForest.treeFactorial_butcherProduct]
  ring

theorem exact_hasUnitConstant [DivisionSemiring R] : HasUnitConstant (exact R) := by
  simp [HasUnitConstant, constantCoeff, coeff, exact]

theorem forestCoeff_exact [Field R] (φ : RootedForest) :
    forestCoeff (exact R) φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestCoeff, RootedForest.treeFactorial]
  | cons τ ts ih =>
      have ih' :
          (List.map (fun x => (RootedTree.treeFactorial x : R)⁻¹) ts).prod =
            ((List.map (Nat.cast ∘ RootedTree.treeFactorial) ts).prod)⁻¹ := by
        simpa [forestCoeff, RootedForest.treeFactorial, exact] using ih
      simp [forestCoeff, RootedForest.treeFactorial, exact]
      rw [ih']
      ring

theorem forestCoeff_scaledExact [Field R] (h : R) (φ : RootedForest) :
    forestCoeff (scaledExact h) φ =
      h ^ RootedForest.order φ * (RootedForest.treeFactorial φ : R)⁻¹ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestCoeff, RootedForest.order, RootedForest.treeFactorial]
  | cons τ ts ih =>
      have hprod :
          (List.map
              (fun x =>
                h ^ RootedTree.order x * (RootedTree.treeFactorial x : R)⁻¹) ts).prod =
            (List.map (fun x => h ^ RootedTree.order x) ts).prod *
              (List.map (fun x => (RootedTree.treeFactorial x : R)⁻¹) ts).prod := by
        induction ts with
        | nil =>
            simp
        | cons ξ ts ih =>
            simp [mul_assoc, mul_left_comm]
      have ih' :
          (List.map (fun x => h ^ RootedTree.order x) ts).prod *
              (List.map (fun x => (RootedTree.treeFactorial x : R)⁻¹) ts).prod =
            h ^ (List.map RootedTree.order ts).sum *
              ((List.map (Nat.cast ∘ RootedTree.treeFactorial) ts).prod)⁻¹ := by
        rw [← hprod]
        simpa [forestCoeff, RootedForest.order, RootedForest.treeFactorial,
          scaledExact] using ih
      simp [forestCoeff, RootedForest.order, RootedForest.treeFactorial, scaledExact]
      rw [ih', pow_add]
      ring

@[simp]
theorem forestCoeff_scaledExact_zero [Field R] (φ : RootedForest) :
    forestCoeff (scaledExact (0 : R)) φ = ForestAlgebra.counitCoeff (R := R) φ := by
  rw [scaledExact_zero]
  exact forestCoeff_unit φ

@[simp]
theorem toCharacter_exact_ofForest [Field R] (φ : RootedForest) :
    toCharacter (exact R) (ForestAlgebra.ofForest (R := R) φ) =
      (RootedForest.treeFactorial φ : R)⁻¹ := by
  simp [forestCoeff_exact]

@[simp]
theorem toCharacter_scaledExact_ofForest [Field R] (h : R) (φ : RootedForest) :
    toCharacter (scaledExact h) (ForestAlgebra.ofForest (R := R) φ) =
      h ^ RootedForest.order φ * (RootedForest.treeFactorial φ : R)⁻¹ := by
  simp [forestCoeff_scaledExact]

@[simp]
theorem toCharacter_scaledExact_zero [Field R] :
    toCharacter (scaledExact (0 : R)) = ForestAlgebra.counit R := by
  rw [scaledExact_zero]
  exact toCharacter_unit

/-- Two B-series agree through order `n` if their coefficients agree on all trees of order at most `n`. -/
def AgreeUpToOrder (a b : Series R) (n : Nat) : Prop :=
  ∀ τ, TreeIndex.order τ ≤ n → coeff a τ = coeff b τ

theorem agreeUpToOrder_refl (a : Series R) (n : Nat) : AgreeUpToOrder a a n := by
  intro τ hτ
  rfl

theorem AgreeUpToOrder.symm {a b : Series R} {n : Nat} (h : AgreeUpToOrder a b n) :
    AgreeUpToOrder b a n := by
  intro τ hτ
  exact (h τ hτ).symm

theorem AgreeUpToOrder.trans {a b c : Series R} {n : Nat}
    (hab : AgreeUpToOrder a b n) (hbc : AgreeUpToOrder b c n) :
    AgreeUpToOrder a c n := by
  intro τ hτ
  exact (hab τ hτ).trans (hbc τ hτ)

theorem AgreeUpToOrder.mono {a b : Series R} {m n : Nat}
    (h : AgreeUpToOrder a b n) (hmn : m ≤ n) : AgreeUpToOrder a b m := by
  intro τ hτ
  exact h τ (hτ.trans hmn)

theorem agreeUpToOrder_succ_iff {a b : Series R} {n : Nat} :
    AgreeUpToOrder a b (n + 1) ↔
      AgreeUpToOrder a b n ∧
        ∀ τ, TreeIndex.order τ = n + 1 → coeff a τ = coeff b τ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun τ hτ => h τ (by omega)⟩
  · rintro ⟨hprev, htop⟩ τ hτ
    by_cases hle : TreeIndex.order τ ≤ n
    · exact hprev τ hle
    · exact htop τ (by omega)

theorem AgreeUpToOrder.add [Add R] {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (a + b) (a' + b') n := by
  intro τ hτ
  change a τ + b τ = a' τ + b' τ
  rw [show a τ = a' τ by simpa [Series.coeff] using ha τ hτ]
  rw [show b τ = b' τ by simpa [Series.coeff] using hb τ hτ]

theorem AgreeUpToOrder.neg [Neg R] {a b : Series R} {n : Nat}
    (h : AgreeUpToOrder a b n) : AgreeUpToOrder (-a) (-b) n := by
  intro τ hτ
  change -a τ = -b τ
  rw [show a τ = b τ by simpa [Series.coeff] using h τ hτ]

theorem AgreeUpToOrder.sub [Sub R] {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (a - b) (a' - b') n := by
  intro τ hτ
  change a τ - b τ = a' τ - b' τ
  rw [show a τ = a' τ by simpa [Series.coeff] using ha τ hτ]
  rw [show b τ = b' τ by simpa [Series.coeff] using hb τ hτ]

theorem AgreeUpToOrder.smul [SMul S R] {a b : Series R} {n : Nat}
    (c : S) (h : AgreeUpToOrder a b n) :
    AgreeUpToOrder (c • a) (c • b) n := by
  intro τ hτ
  change c • a τ = c • b τ
  rw [show a τ = b τ by simpa [Series.coeff] using h τ hτ]

theorem agreeUpToOrder_iff_treeCoeff {a b : Series R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ τ : RootedTree, RootedTree.order τ ≤ n →
          coeff a (.tree τ) = coeff b (.tree τ) := by
  constructor
  · intro h
    exact
      ⟨by simpa [constantCoeff] using h TreeIndex.empty (Nat.zero_le n),
        fun τ hτ => h (.tree τ) hτ⟩
  · rintro ⟨hconst, htree⟩ τ hτ
    cases τ with
    | empty =>
        simpa [constantCoeff] using hconst
    | tree τ =>
        exact htree τ hτ

theorem AgreeUpToOrder.forestCoeff [CommSemiring R] {a b : Series R} {n : Nat}
    (h : AgreeUpToOrder a b n) {φ : RootedForest}
    (hφ : RootedForest.order φ ≤ n) :
    Series.forestCoeff a φ = Series.forestCoeff b φ := by
  suffices hforest :
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        Series.forestCoeff a φ = Series.forestCoeff b φ from
    hforest φ hφ
  intro φ
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      intro hts
      simp [Series.forestCoeff]
  | cons τ ts ih =>
      intro hts
      have hτ : TreeIndex.order (.tree τ) ≤ n := by
        have hle :
            RootedTree.order τ ≤
              RootedForest.order (((τ :: ts) : List RootedTree) : RootedForest) := by
          simp [RootedForest.order]
        simpa using hle.trans hts
      have htail : RootedForest.order (ts : RootedForest) ≤ n := by
        have hle :
            RootedForest.order (ts : RootedForest) ≤
              RootedForest.order (((τ :: ts) : List RootedTree) : RootedForest) := by
          simp [RootedForest.order]
        exact hle.trans hts
      have hhead : coeff a (.tree τ) = coeff b (.tree τ) :=
        h (.tree τ) hτ
      have hhead' : a (.tree τ) = b (.tree τ) := by
        simpa [Series.coeff] using hhead
      have htail_eq :
          (List.map (fun x => a (.tree x)) ts).prod =
            (List.map (fun x => b (.tree x)) ts).prod := by
        simpa [Series.forestCoeff] using ih htail
      simp [Series.forestCoeff, hhead', htail_eq]

theorem AgreeUpToOrder.toCharacter_evalForest [CommSemiring R] {a b : Series R}
    {n : Nat} (h : AgreeUpToOrder a b n) {φ : RootedForest}
    (hφ : RootedForest.order φ ≤ n) :
    (toCharacter a).evalForest φ = (toCharacter b).evalForest φ := by
  simpa [toCharacter_evalForest] using h.forestCoeff hφ

theorem AgreeUpToOrder.toCharacter_ofForest [CommSemiring R] {a b : Series R}
    {n : Nat} (h : AgreeUpToOrder a b n) {φ : RootedForest}
    (hφ : RootedForest.order φ ≤ n) :
    toCharacter a (ForestAlgebra.ofForest (R := R) φ) =
      toCharacter b (ForestAlgebra.ofForest (R := R) φ) := by
  simpa [toCharacter_ofForest] using h.forestCoeff hφ

theorem agreeUpToOrder_iff_forestCoeff [CommSemiring R] {a b : Series R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ φ : RootedForest, RootedForest.order φ ≤ n →
          forestCoeff a φ = forestCoeff b φ := by
  constructor
  · intro h
    exact
      ⟨by simpa [constantCoeff] using h TreeIndex.empty (Nat.zero_le n),
        fun φ hφ => h.forestCoeff hφ⟩
  · rintro ⟨hconst, hforest⟩ τ hτ
    cases τ with
    | empty =>
        simpa [constantCoeff] using hconst
    | tree τ =>
        have hsingleton := hforest (RootedForest.singleton τ) (by simpa using hτ)
        simpa using hsingleton

theorem agreeUpToOrder_iff_toCharacter_evalForest [CommSemiring R]
    {a b : Series R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ φ : RootedForest, RootedForest.order φ ≤ n →
          (toCharacter a).evalForest φ = (toCharacter b).evalForest φ := by
  simpa [toCharacter_evalForest] using
    (agreeUpToOrder_iff_forestCoeff (a := a) (b := b) (n := n))

theorem agreeUpToOrder_iff_toCharacter_ofForest [CommSemiring R]
    {a b : Series R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ φ : RootedForest, RootedForest.order φ ≤ n →
          toCharacter a (ForestAlgebra.ofForest (R := R) φ) =
            toCharacter b (ForestAlgebra.ofForest (R := R) φ) := by
  simpa [toCharacter_ofForest] using
    (agreeUpToOrder_iff_forestCoeff (a := a) (b := b) (n := n))

theorem agreeUpToOrder_of_eq {a b : Series R} (h : a = b) (n : Nat) :
    AgreeUpToOrder a b n := by
  subst b
  exact agreeUpToOrder_refl a n

theorem eq_of_agreeUpToOrder_all {a b : Series R}
    (h : ∀ n, AgreeUpToOrder a b n) : a = b := by
  funext τ
  exact h (TreeIndex.order τ) τ le_rfl

theorem agreeUpToOrder_all_iff_eq {a b : Series R} :
    (∀ n, AgreeUpToOrder a b n) ↔ a = b := by
  constructor
  · exact eq_of_agreeUpToOrder_all
  · intro h n
    exact agreeUpToOrder_of_eq h n

theorem agreeUpToOrder_all_iff_constantCoeff_toCharacter [CommSemiring R]
    {a b : Series R} :
    (∀ n, AgreeUpToOrder a b n) ↔ constantCoeff a = constantCoeff b ∧
      toCharacter a = toCharacter b := by
  constructor
  · intro h
    rw [(agreeUpToOrder_all_iff_eq).1 h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hconst, hchar⟩ n
    rw [agreeUpToOrder_iff_toCharacter_ofForest]
    exact ⟨hconst, fun _ _ => by rw [hchar]⟩

/-- Coefficient-level order conditions for a B-series. -/
def HasOrder [DivisionSemiring R] (a : Series R) (n : Nat) : Prop :=
  AgreeUpToOrder a (exact R) n

theorem hasOrder_iff [DivisionSemiring R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      ∀ τ, TreeIndex.order τ ≤ n → coeff a τ = (TreeIndex.treeFactorial τ : R)⁻¹ :=
  Iff.rfl

theorem HasOrder.coeff [DivisionSemiring R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {τ : TreeIndex} (hτ : TreeIndex.order τ ≤ n) :
    Series.coeff a τ = (TreeIndex.treeFactorial τ : R)⁻¹ :=
  h τ hτ

theorem HasOrder.treeCoeff [DivisionSemiring R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {τ : RootedTree} (hτ : RootedTree.order τ ≤ n) :
    Series.coeff a (TreeIndex.tree τ) = (RootedTree.treeFactorial τ : R)⁻¹ :=
  h.coeff (τ := TreeIndex.tree τ) hτ

theorem HasOrder.coeff_tree_graft [Field R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {φ : RootedForest} (hφ : 1 + RootedForest.order φ ≤ n) :
    Series.coeff a (TreeIndex.tree (RootedForest.graft φ)) =
      ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial φ : R)⁻¹ := by
  calc
    Series.coeff a (TreeIndex.tree (RootedForest.graft φ)) =
        Series.coeff (exact R) (TreeIndex.tree (RootedForest.graft φ)) := by
          exact h.treeCoeff (by simpa using hφ)
    _ = ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial φ : R)⁻¹ := by
          exact coeff_exact_tree_graft (R := R) φ

theorem HasOrder.coeff_tree_branches [Field R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {τ : RootedTree} (hτ : RootedTree.order τ ≤ n) :
    Series.coeff a (TreeIndex.tree τ) =
      (RootedTree.order τ : R)⁻¹ *
        (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
  calc
    Series.coeff a (TreeIndex.tree τ) =
        Series.coeff (exact R) (TreeIndex.tree τ) := by
          exact h.treeCoeff hτ
    _ = (RootedTree.order τ : R)⁻¹ *
        (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
          exact coeff_exact_tree_branches (R := R) τ

theorem HasOrder.hasUnitConstant [DivisionSemiring R] {a : Series R} {n : Nat}
    (h : HasOrder a n) : HasUnitConstant a := by
  simpa [HasUnitConstant, constantCoeff, exact] using h.coeff (τ := TreeIndex.empty) (Nat.zero_le n)

theorem hasOrder_iff_treeCoeff [DivisionSemiring R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ τ : RootedTree, RootedTree.order τ ≤ n →
          Series.coeff a (TreeIndex.tree τ) = (RootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun τ hτ => h.treeCoeff hτ⟩
  · rintro ⟨ha, htree⟩ τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        simpa [exact] using htree τ hτ

theorem HasOrder.mono [DivisionSemiring R] {a : Series R} {m n : Nat}
    (h : HasOrder a n) (hmn : m ≤ n) : HasOrder a m :=
  AgreeUpToOrder.mono h hmn

theorem hasOrder_succ_iff [DivisionSemiring R] {a : Series R} {n : Nat} :
    HasOrder a (n + 1) ↔
      HasOrder a n ∧
        ∀ τ, TreeIndex.order τ = n + 1 →
          Series.coeff a τ = (TreeIndex.treeFactorial τ : R)⁻¹ := by
  exact agreeUpToOrder_succ_iff

theorem HasOrder.of_agreeUpToOrder [DivisionSemiring R] {a b : Series R} {n : Nat}
    (hab : AgreeUpToOrder a b n) (ha : HasOrder a n) : HasOrder b n :=
  hab.symm.trans ha

theorem hasOrder_congr [DivisionSemiring R] {a b : Series R} {n : Nat}
    (hab : AgreeUpToOrder a b n) : HasOrder a n ↔ HasOrder b n := by
  constructor
  · exact HasOrder.of_agreeUpToOrder hab
  · exact HasOrder.of_agreeUpToOrder hab.symm

theorem hasOrder_all_congr [DivisionSemiring R] {a b : Series R}
    (hab : ∀ n, AgreeUpToOrder a b n) :
    (∀ n, HasOrder a n) ↔ ∀ n, HasOrder b n := by
  constructor
  · intro ha n
    exact (hasOrder_congr (hab n)).1 (ha n)
  · intro hb n
    exact (hasOrder_congr (hab n)).2 (hb n)

theorem HasOrder.agreeUpToOrder [DivisionSemiring R] {a b : Series R} {n : Nat}
    (ha : HasOrder a n) (hb : HasOrder b n) : AgreeUpToOrder a b n :=
  ha.trans hb.symm

theorem hasOrder_zero_iff [DivisionSemiring R] {a : Series R} :
    HasOrder a 0 ↔ HasUnitConstant a := by
  constructor
  · intro h
    exact h.hasUnitConstant
  · intro ha τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have hpos := RootedTree.order_pos τ
        simp at hτ
        omega

theorem HasOrder.bulletCoeff [DivisionSemiring R] {a : Series R} {n : Nat}
    (h : HasOrder a n) (hn : 1 ≤ n) :
    Series.coeff a TreeIndex.bullet = 1 := by
  simpa [TreeIndex.bullet] using
    HasOrder.coeff h (τ := TreeIndex.bullet) (by simpa using hn)

theorem hasOrder_one_iff [DivisionSemiring R] {a : Series R} :
    HasOrder a 1 ↔ HasUnitConstant a ∧ Series.coeff a TreeIndex.bullet = 1 := by
  constructor
  · intro h
    exact ⟨HasOrder.hasUnitConstant h, HasOrder.bulletCoeff h le_rfl⟩
  · rintro ⟨ha, hbullet⟩ τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have horder : RootedTree.order τ = 1 := by
          have hpos := RootedTree.order_pos τ
          simp at hτ
          omega
        rw [(RootedTree.order_eq_one_iff τ).1 horder]
        simpa [TreeIndex.bullet, exact] using hbullet

theorem exact_hasOrder [DivisionSemiring R] (n : Nat) : HasOrder (exact R) n :=
  agreeUpToOrder_refl (exact R) n

theorem eq_exact_of_hasOrder_all [DivisionSemiring R] {a : Series R}
    (h : ∀ n, HasOrder a n) : a = exact R := by
  funext τ
  exact h (TreeIndex.order τ) τ le_rfl

theorem hasOrder_all_iff_eq_exact [DivisionSemiring R] {a : Series R} :
    (∀ n, HasOrder a n) ↔ a = exact R := by
  constructor
  · exact eq_exact_of_hasOrder_all
  · intro h n
    rw [h]
    exact exact_hasOrder n

theorem hasOrder_all_iff_treeCoeff [DivisionSemiring R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ τ : RootedTree,
          Series.coeff a (TreeIndex.tree τ) = (RootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun τ => (h (RootedTree.order τ)).treeCoeff le_rfl⟩
  · rintro ⟨ha, htree⟩ n
    rw [hasOrder_iff_treeCoeff]
    exact ⟨ha, fun τ _ => htree τ⟩

theorem hasOrder_iff_forestCoeff [Field R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest, RootedForest.order φ ≤ n →
          forestCoeff a φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    constructor
    · simpa [HasUnitConstant, constantCoeff, exact] using
        h TreeIndex.empty (Nat.zero_le n)
    · intro φ hφ
      have hforest :
          ∀ φ : RootedForest, RootedForest.order φ ≤ n →
            forestCoeff a φ = forestCoeff (exact R) φ := by
        intro φ
        refine Quotient.inductionOn φ ?_
        intro ts
        induction ts with
        | nil =>
            intro hts
            simp [forestCoeff]
        | cons τ ts ih =>
            intro hts
            have hτ : TreeIndex.order (.tree τ) ≤ n := by
              have hle :
                  RootedTree.order τ ≤
                    RootedForest.order (((τ :: ts) : List RootedTree) : RootedForest) := by
                simp [RootedForest.order]
              simpa using hle.trans hts
            have htail : RootedForest.order (ts : RootedForest) ≤ n := by
              have hle :
                  RootedForest.order (ts : RootedForest) ≤
                    RootedForest.order (((τ :: ts) : List RootedTree) : RootedForest) := by
                simp [RootedForest.order]
              exact hle.trans hts
            have hhead : a (.tree τ) = exact R (.tree τ) := by
              simpa [coeff] using h (.tree τ) hτ
            have htail_eq :
                (List.map (fun x => a (.tree x)) ts).prod =
                  (List.map (fun x => exact R (.tree x)) ts).prod := by
              simpa [forestCoeff] using ih htail
            simp [forestCoeff, hhead, htail_eq]
      rw [hforest φ hφ, forestCoeff_exact]
  · rintro ⟨ha, hforest⟩ τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have hsingleton :
            forestCoeff a (RootedForest.singleton τ) =
              (RootedForest.treeFactorial (RootedForest.singleton τ) : R)⁻¹ :=
          hforest (RootedForest.singleton τ) (by simpa using hτ)
        simpa [exact] using hsingleton

theorem hasOrder_iff_toCharacter_evalForest [Field R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest, RootedForest.order φ ≤ n →
          (toCharacter a).evalForest φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_evalForest] using (hasOrder_iff_forestCoeff (a := a) (n := n))

theorem hasOrder_iff_toCharacter_ofForest [Field R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest, RootedForest.order φ ≤ n →
          toCharacter a (ForestAlgebra.ofForest (R := R) φ) =
            (RootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_ofForest] using (hasOrder_iff_forestCoeff (a := a) (n := n))

theorem HasOrder.forestCoeff [Field R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    forestCoeff a φ = (RootedForest.treeFactorial φ : R)⁻¹ :=
  ((hasOrder_iff_forestCoeff (a := a) (n := n)).1 h).2 φ hφ

theorem HasOrder.toCharacter_evalForest [Field R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    (toCharacter a).evalForest φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_evalForest] using h.forestCoeff hφ

theorem HasOrder.toCharacter_ofForest [Field R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    toCharacter a (ForestAlgebra.ofForest (R := R) φ) =
      (RootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_ofForest] using h.forestCoeff hφ

theorem hasOrder_iff_coeff_tree_graft [Field R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest, 1 + RootedForest.order φ ≤ n →
          Series.coeff a (TreeIndex.tree (RootedForest.graft φ)) =
            ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
              (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun φ hφ => h.coeff_tree_graft hφ⟩
  · rintro ⟨ha, hgraft⟩ ξ hξ
    cases ξ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        calc
          Series.coeff a (TreeIndex.tree τ) =
              Series.coeff a (TreeIndex.tree (RootedForest.graft (RootedTree.branches τ))) := by
                rw [RootedForest.graft_branches τ]
          _ = ((1 + RootedForest.order (RootedTree.branches τ) : Nat) : R)⁻¹ *
                (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
                exact hgraft (RootedTree.branches τ) (by
                  rw [RootedForest.order_branches τ]
                  exact hξ)
          _ = (TreeIndex.treeFactorial (TreeIndex.tree τ) : R)⁻¹ := by
                simpa [Series.coeff, Series.exact, RootedForest.order_branches] using
                  (Series.coeff_exact_tree_branches (R := R) τ).symm

theorem hasOrder_iff_coeff_tree_branches [Field R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ τ : RootedTree, RootedTree.order τ ≤ n →
          Series.coeff a (TreeIndex.tree τ) =
            (RootedTree.order τ : R)⁻¹ *
              (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun τ hτ => h.coeff_tree_branches hτ⟩
  · rintro ⟨ha, hbranches⟩ ξ hξ
    cases ξ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        calc
          Series.coeff a (TreeIndex.tree τ) =
              (RootedTree.order τ : R)⁻¹ *
                (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ :=
                hbranches τ hξ
          _ = (TreeIndex.treeFactorial (TreeIndex.tree τ) : R)⁻¹ := by
                simpa [Series.coeff, Series.exact] using
                  (Series.coeff_exact_tree_branches (R := R) τ).symm

theorem HasOrder.coeff_butcherProduct [Field R] {a : Series R} {n : Nat}
    (h : HasOrder a n) {φ : RootedForest} {τ : RootedTree}
    (horder : RootedForest.order φ + RootedTree.order τ ≤ n) :
    Series.coeff a (TreeIndex.tree (RootedForest.butcherProduct φ τ)) =
      ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  calc
    Series.coeff a (TreeIndex.tree (RootedForest.butcherProduct φ τ)) =
        Series.coeff (exact R) (TreeIndex.tree (RootedForest.butcherProduct φ τ)) := by
          exact h.treeCoeff (by simpa using horder)
    _ = ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
        (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
          exact coeff_exact_tree_butcherProduct (R := R) φ τ

theorem hasOrder_iff_coeff_butcherProduct [Field R] {a : Series R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ (φ : RootedForest) (τ : RootedTree),
          RootedForest.order φ + RootedTree.order τ ≤ n →
            Series.coeff a (TreeIndex.tree (RootedForest.butcherProduct φ τ)) =
              ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
                (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun φ τ horder => h.coeff_butcherProduct horder⟩
  · rintro ⟨ha, h⟩
    rw [hasOrder_iff]
    intro ξ hξ
    cases ξ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have horder :
            RootedForest.order (RootedTree.branches τ) + RootedTree.order RootedTree.bullet ≤ n := by
          have hbranches :
              RootedForest.order (RootedTree.branches τ) + RootedTree.order RootedTree.bullet =
                RootedTree.order τ := by
            rw [RootedTree.order_bullet]
            have h := RootedForest.order_branches τ
            omega
          rw [hbranches]
          exact hξ
        have hcondition := h (RootedTree.branches τ) RootedTree.bullet horder
        calc
          Series.coeff a (TreeIndex.tree τ) =
              Series.coeff a
                (TreeIndex.tree
                  (RootedForest.butcherProduct (RootedTree.branches τ) RootedTree.bullet)) := by
                simp [RootedForest.butcherProduct]
          _ = ((RootedForest.order (RootedTree.branches τ) + RootedTree.order RootedTree.bullet :
                Nat) : R)⁻¹ *
                (RootedForest.treeFactorial
                  (RootedTree.branches τ + RootedTree.branches RootedTree.bullet) : R)⁻¹ :=
                hcondition
          _ = (TreeIndex.treeFactorial (TreeIndex.tree τ) : R)⁻¹ := by
                have hexact :=
                  (coeff_exact_tree_butcherProduct (R := R)
                    (RootedTree.branches τ) RootedTree.bullet).symm
                simpa [Series.coeff, Series.exact, RootedForest.butcherProduct] using hexact

theorem hasOrder_all_iff_forestCoeff [Field R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest,
          forestCoeff a φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun φ => (h (RootedForest.order φ)).forestCoeff le_rfl⟩
  · rintro ⟨ha, hforest⟩ n
    rw [hasOrder_iff_forestCoeff]
    exact ⟨ha, fun φ _ => hforest φ⟩

theorem hasOrder_all_iff_coeff_tree_graft [Field R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest,
          Series.coeff a (TreeIndex.tree (RootedForest.graft φ)) =
            ((1 + RootedForest.order φ : Nat) : R)⁻¹ *
              (RootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun φ =>
      (h (1 + RootedForest.order φ)).coeff_tree_graft le_rfl⟩
  · rintro ⟨ha, hgraft⟩ n
    rw [hasOrder_iff_coeff_tree_graft]
    exact ⟨ha, fun φ _ => hgraft φ⟩

theorem hasOrder_all_iff_coeff_tree_branches [Field R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ τ : RootedTree,
          Series.coeff a (TreeIndex.tree τ) =
            (RootedTree.order τ : R)⁻¹ *
              (RootedForest.treeFactorial (RootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun τ =>
      (h (RootedTree.order τ)).coeff_tree_branches le_rfl⟩
  · rintro ⟨ha, hbranches⟩ n
    rw [hasOrder_iff_coeff_tree_branches]
    exact ⟨ha, fun τ _ => hbranches τ⟩

theorem hasOrder_all_iff_toCharacter_evalForest [Field R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest,
          (toCharacter a).evalForest φ = (RootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_evalForest] using (hasOrder_all_iff_forestCoeff (a := a))

theorem hasOrder_all_iff_toCharacter_ofForest [Field R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ φ : RootedForest,
          toCharacter a (ForestAlgebra.ofForest (R := R) φ) =
            (RootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_ofForest] using (hasOrder_all_iff_forestCoeff (a := a))

theorem hasOrder_all_iff_toCharacter_eq_exact [Field R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧ toCharacter a = toCharacter (exact R) := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, by rw [eq_exact_of_hasOrder_all h]⟩
  · rintro ⟨ha, hchar⟩
    rw [hasOrder_all_iff_eq_exact]
    exact ext_of_toCharacter_eq ha exact_hasUnitConstant hchar

theorem characterEquiv_hasOrder_all_iff_exact [Field R]
    (a : {a : Series R // HasUnitConstant a}) :
    (∀ n, HasOrder a.1 n) ↔
      characterEquiv a = characterEquiv ⟨exact R, exact_hasUnitConstant⟩ := by
  constructor
  · intro h
    apply congrArg characterEquiv
    apply Subtype.ext
    exact (hasOrder_all_iff_eq_exact).1 h
  · intro h
    rw [hasOrder_all_iff_toCharacter_eq_exact]
    exact ⟨a.2, by simpa [characterEquiv_apply] using h⟩

theorem hasOrder_all_iff_coeff_butcherProduct [Field R] {a : Series R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ (φ : RootedForest) (τ : RootedTree),
          Series.coeff a (TreeIndex.tree (RootedForest.butcherProduct φ τ)) =
            ((RootedForest.order φ + RootedTree.order τ : Nat) : R)⁻¹ *
              (RootedForest.treeFactorial (φ + RootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun φ τ =>
      (h (RootedForest.order φ + RootedTree.order τ)).coeff_butcherProduct le_rfl⟩
  · rintro ⟨ha, h⟩ n
    rw [hasOrder_iff_coeff_butcherProduct]
    exact ⟨ha, fun φ τ _ => h φ τ⟩

end Series

end BSeries
