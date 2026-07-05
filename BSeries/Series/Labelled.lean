/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.Basic
import HopfAlgebras.Algebra.LabelledForest

/-!
# Labelled B-Series

This file defines labelled B-series coefficient families and their
multiplicative extension to the labelled rooted-forest algebra.

## Main definitions

* `LTreeIndex α` - labelled rooted trees with an adjoined empty tree
* `LSeries α R` - coefficient families indexed by labelled rooted trees
* `LSeries.toCharacter` - multiplicative extension to labelled forest characters
* `LSeries.ofCharacter` - recover labelled coefficients from a forest character
* `LSeries.characterEquiv` - equivalence between unit-constant series and characters
* `LSeries.unit` - convolution identity coefficients
* `LSeries.exact` - exact-flow coefficients, ignoring labels
* `LSeries.scaledExact` - exact-flow coefficients with a time/step-size parameter
* `LSeries.AgreeUpToOrder` - coefficient agreement through a labelled tree order
* `LSeries.HasOrder` - order conditions relative to exact labelled coefficients
* `LSeries.comapMapLabels` - pull back labelled coefficients by relabelling
* `LSeries.comapConstLabel` - restrict labelled coefficients to one constant label
* `LSeries.comapEraseLabels` - pull back unlabelled coefficients by erasing labels
* `LSeries.LabelInvariant` - labelled coefficients that descend to unlabelled trees
-/

namespace BSeries

open HopfAlgebras

universe u v w x y

/-- Labelled rooted trees with an adjoined empty tree. -/
inductive LTreeIndex (α : Type u) : Type u where
  | empty : LTreeIndex α
  | tree : LRootedTree α → LTreeIndex α

namespace LTreeIndex

variable {α : Type u} {β : Type v} {γ : Type x}

/-- The order of a labelled B-series tree index. -/
def order : LTreeIndex α → Nat
  | .empty => 0
  | .tree τ => LRootedTree.order τ

/-- Predicate for labelled B-series tree indices of a fixed order. -/
def IsOfOrder (τ : LTreeIndex α) (n : Nat) : Prop :=
  order τ = n

/-- Butcher's tree factorial for labelled B-series tree indices. -/
def treeFactorial : LTreeIndex α → Nat
  | .empty => 1
  | .tree τ => LRootedTree.treeFactorial τ

/-- Forget labels from a labelled B-series tree index. -/
def erase : LTreeIndex α → TreeIndex
  | .empty => .empty
  | .tree τ => .tree (LRootedTree.erase τ)

/-- Relabel a labelled B-series tree index. -/
def mapLabels (f : α → β) : LTreeIndex α → LTreeIndex β
  | .empty => .empty
  | .tree τ => .tree (LRootedTree.map f τ)

/-- Label every vertex of an unlabelled B-series tree index by the same label. -/
def constLabel (a : α) : TreeIndex → LTreeIndex α
  | .empty => .empty
  | .tree τ => .tree (LRootedTree.constLabel a τ)

@[simp]
theorem order_empty : order (.empty : LTreeIndex α) = 0 :=
  rfl

@[simp]
theorem order_tree (τ : LRootedTree α) : order (.tree τ) = LRootedTree.order τ :=
  rfl

@[simp]
theorem treeFactorial_empty : treeFactorial (.empty : LTreeIndex α) = 1 :=
  rfl

@[simp]
theorem treeFactorial_tree (τ : LRootedTree α) :
    treeFactorial (.tree τ) = LRootedTree.treeFactorial τ :=
  rfl

@[simp]
theorem erase_empty : erase (.empty : LTreeIndex α) = TreeIndex.empty :=
  rfl

@[simp]
theorem erase_tree (τ : LRootedTree α) :
    erase (.tree τ) = TreeIndex.tree (LRootedTree.erase τ) :=
  rfl

@[simp]
theorem constLabel_empty (a : α) : constLabel a TreeIndex.empty = .empty :=
  rfl

@[simp]
theorem constLabel_tree (a : α) (τ : RootedTree) :
    constLabel a (TreeIndex.tree τ) = .tree (LRootedTree.constLabel a τ) :=
  rfl

@[simp]
theorem mapLabels_empty (f : α → β) : mapLabels f .empty = .empty :=
  rfl

@[simp]
theorem mapLabels_tree (f : α → β) (τ : LRootedTree α) :
    mapLabels f (.tree τ) = .tree (LRootedTree.map f τ) :=
  rfl

@[simp]
theorem order_erase (τ : LTreeIndex α) : TreeIndex.order (erase τ) = order τ := by
  cases τ <;> simp [erase, order]

@[simp]
theorem treeFactorial_erase (τ : LTreeIndex α) :
    TreeIndex.treeFactorial (erase τ) = treeFactorial τ := by
  cases τ <;> simp [erase, treeFactorial]

@[simp]
theorem erase_constLabel (a : α) (τ : TreeIndex) :
    erase (constLabel a τ) = τ := by
  cases τ <;> simp [erase, constLabel]

theorem constLabel_injective (a : α) : Function.Injective (constLabel a) := by
  intro σ τ h
  have hErase := congrArg erase h
  simpa using hErase

@[simp]
theorem constLabel_eq_constLabel_iff (a : α) {σ τ : TreeIndex} :
    constLabel a σ = constLabel a τ ↔ σ = τ := by
  constructor
  · intro h
    exact constLabel_injective a h
  · intro h
    rw [h]

@[simp]
theorem order_mapLabels (f : α → β) (τ : LTreeIndex α) :
    order (mapLabels f τ) = order τ := by
  cases τ <;> simp [mapLabels, order]

@[simp]
theorem treeFactorial_mapLabels (f : α → β) (τ : LTreeIndex α) :
    treeFactorial (mapLabels f τ) = treeFactorial τ := by
  cases τ <;> simp [mapLabels, treeFactorial]

@[simp]
theorem order_constLabel (a : α) (τ : TreeIndex) :
    order (constLabel a τ) = TreeIndex.order τ := by
  cases τ <;> simp [constLabel, order]

@[simp]
theorem treeFactorial_constLabel (a : α) (τ : TreeIndex) :
    treeFactorial (constLabel a τ) = TreeIndex.treeFactorial τ := by
  cases τ <;> simp [constLabel, treeFactorial]

@[simp]
theorem erase_mapLabels (f : α → β) (τ : LTreeIndex α) :
    erase (mapLabels f τ) = erase τ := by
  cases τ <;> simp [erase, mapLabels]

@[simp]
theorem mapLabels_constLabel (f : α → β) (a : α) (τ : TreeIndex) :
    mapLabels f (constLabel a τ) = constLabel (f a) τ := by
  cases τ <;> simp [mapLabels, constLabel]

@[simp]
theorem mapLabels_id (τ : LTreeIndex α) : mapLabels id τ = τ := by
  cases τ <;> simp [mapLabels]

@[simp]
theorem mapLabels_comp (g : β → γ) (f : α → β) (τ : LTreeIndex α) :
    mapLabels g (mapLabels f τ) = mapLabels (g ∘ f) τ := by
  cases τ <;> simp [mapLabels]

theorem mapLabels_comp_eq_id (f : α → β) (g : β → α)
    (h : ∀ x, f (g x) = x) (τ : LTreeIndex β) :
    mapLabels f (mapLabels g τ) = τ := by
  rw [mapLabels_comp]
  have hfg : f ∘ g = id := funext h
  rw [hfg, mapLabels_id]

theorem mapLabels_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (mapLabels f : LTreeIndex α → LTreeIndex β) := by
  intro σ τ h
  cases σ <;> cases τ <;> simp [mapLabels] at h ⊢
  exact LRootedTree.map_injective f hf h

theorem mapLabels_eq_mapLabels_iff_of_injective (f : α → β) (hf : Function.Injective f)
    {σ τ : LTreeIndex α} :
    mapLabels f σ = mapLabels f τ ↔ σ = τ := by
  constructor
  · intro h
    exact mapLabels_injective f hf h
  · intro h
    rw [h]

@[simp]
theorem order_eq_zero_iff : ∀ τ : LTreeIndex α, order τ = 0 ↔ τ = .empty
  | .empty => by simp
  | .tree τ => by
      constructor
      · intro h
        exact False.elim ((Nat.ne_of_gt (LRootedTree.order_pos τ)) h)
      · intro h
        cases h

theorem order_pos_iff_ne_empty (τ : LTreeIndex α) : 0 < order τ ↔ τ ≠ .empty := by
  constructor
  · intro h hτ
    rw [hτ] at h
    simp at h
  · intro h
    cases τ with
    | empty => exact False.elim (h rfl)
    | tree τ => exact LRootedTree.order_pos τ

theorem order_eq_one_iff_exists_tree_graft_zero (τ : LTreeIndex α) :
    order τ = 1 ↔ ∃ a : α, τ = .tree (LRootedForest.graft a 0) := by
  cases τ with
  | empty =>
      constructor
      · intro h
        cases h
      · rintro ⟨a, h⟩
        cases h
  | tree τ =>
      constructor
      · intro h
        exact
          ⟨LRootedTree.rootLabel τ,
            congrArg LTreeIndex.tree
              ((LRootedForest.order_eq_one_iff_eq_graft_root_zero τ).1 h)⟩
      · rintro ⟨a, h⟩
        rw [h]
        simp

theorem treeFactorial_pos : ∀ τ : LTreeIndex α, 0 < treeFactorial τ
  | .empty => by simp
  | .tree τ => LRootedTree.treeFactorial_pos τ

theorem treeFactorial_ne_zero (τ : LTreeIndex α) : treeFactorial τ ≠ 0 :=
  Nat.ne_of_gt (treeFactorial_pos τ)

end LTreeIndex

/-- A labelled B-series over `R`, represented by labelled-tree coefficients. -/
abbrev LSeries (α : Type u) (R : Type v) : Type (max u v) :=
  LTreeIndex α → R

namespace LSeries

variable {α : Type u} {β : Type v} {γ : Type x} {R : Type w} {S : Type y}

/-- The coefficient of a labelled rooted tree index in a labelled B-series. -/
def coeff (a : LSeries α R) (τ : LTreeIndex α) : R :=
  a τ

@[simp]
theorem coeff_apply (a : LSeries α R) (τ : LTreeIndex α) : coeff a τ = a τ :=
  rfl

@[ext]
theorem ext {a b : LSeries α R} (h : ∀ τ, coeff a τ = coeff b τ) : a = b := by
  funext τ
  exact h τ

/-- The coefficient of the empty labelled tree. -/
def constantCoeff (a : LSeries α R) : R :=
  coeff a LTreeIndex.empty

@[simp]
theorem coeff_empty (a : LSeries α R) :
    coeff a LTreeIndex.empty = constantCoeff a :=
  rfl

section Pointwise

@[simp]
theorem coeff_zero [Zero R] (τ : LTreeIndex α) : coeff (0 : LSeries α R) τ = 0 :=
  rfl

@[simp]
theorem coeff_add [Add R] (a b : LSeries α R) (τ : LTreeIndex α) :
    coeff (a + b) τ = coeff a τ + coeff b τ :=
  rfl

@[simp]
theorem coeff_neg [Neg R] (a : LSeries α R) (τ : LTreeIndex α) :
    coeff (-a) τ = -coeff a τ :=
  rfl

@[simp]
theorem coeff_sub [Sub R] (a b : LSeries α R) (τ : LTreeIndex α) :
    coeff (a - b) τ = coeff a τ - coeff b τ :=
  rfl

@[simp]
theorem coeff_smul [SMul S R] (c : S) (a : LSeries α R) (τ : LTreeIndex α) :
    coeff (c • a) τ = c • coeff a τ :=
  rfl

end Pointwise

@[simp]
theorem constantCoeff_zero [Zero R] : constantCoeff (0 : LSeries α R) = 0 :=
  rfl

@[simp]
theorem constantCoeff_add [Add R] (a b : LSeries α R) :
    constantCoeff (a + b) = constantCoeff a + constantCoeff b :=
  rfl

@[simp]
theorem constantCoeff_neg [Neg R] (a : LSeries α R) :
    constantCoeff (-a) = -constantCoeff a :=
  rfl

@[simp]
theorem constantCoeff_sub [Sub R] (a b : LSeries α R) :
    constantCoeff (a - b) = constantCoeff a - constantCoeff b :=
  rfl

@[simp]
theorem constantCoeff_smul [SMul S R] (c : S) (a : LSeries α R) :
    constantCoeff (c • a) = c • constantCoeff a :=
  rfl

/-- The condition `a(∅) = 1`, used for labelled B-series considered as maps. -/
def HasUnitConstant [One R] (a : LSeries α R) : Prop :=
  constantCoeff a = 1

theorem HasUnitConstant.coeff_empty [One R] {a : LSeries α R}
    (h : HasUnitConstant a) : coeff a LTreeIndex.empty = 1 :=
  h

/-- The condition `a(∅) = 0`, used for labelled B-series considered as vector fields. -/
def HasZeroConstant [Zero R] (a : LSeries α R) : Prop :=
  constantCoeff a = 0

theorem HasZeroConstant.coeff_empty [Zero R] {a : LSeries α R}
    (h : HasZeroConstant a) : coeff a LTreeIndex.empty = 0 :=
  h

theorem zero_hasZeroConstant [Zero R] : HasZeroConstant (0 : LSeries α R) :=
  rfl

theorem HasZeroConstant.add [AddMonoid R] {a b : LSeries α R}
    (ha : HasZeroConstant a) (hb : HasZeroConstant b) :
    HasZeroConstant (a + b) := by
  change constantCoeff a + constantCoeff b = 0
  rw [ha, hb]
  simp

theorem HasZeroConstant.neg [AddGroup R] {a : LSeries α R}
    (ha : HasZeroConstant a) : HasZeroConstant (-a) := by
  change -constantCoeff a = 0
  rw [ha]
  simp

theorem HasZeroConstant.sub [AddGroup R] {a b : LSeries α R}
    (ha : HasZeroConstant a) (hb : HasZeroConstant b) :
    HasZeroConstant (a - b) := by
  change constantCoeff a - constantCoeff b = 0
  rw [ha, hb]
  simp

theorem HasZeroConstant.smul [Zero R] [SMulZeroClass S R] {a : LSeries α R}
    (c : S) (ha : HasZeroConstant a) : HasZeroConstant (c • a) := by
  change c • constantCoeff a = 0
  rw [ha]
  simp

section ForestCharacter

noncomputable section

variable [CommSemiring R]

/-- Multiplicative coefficient of a labelled rooted forest induced by a series. -/
def forestCoeff (a : LSeries α R) (φ : LRootedForest α) : R :=
  (φ.map fun τ => coeff a (.tree τ)).prod

@[simp]
theorem forestCoeff_zero (a : LSeries α R) : forestCoeff a 0 = 1 := by
  simp [forestCoeff]

@[simp]
theorem forestCoeff_empty (a : LSeries α R) :
    forestCoeff a LRootedForest.empty = 1 := by
  simp [LRootedForest.empty, forestCoeff]

@[simp]
theorem forestCoeff_singleton (a : LSeries α R) (τ : LRootedTree α) :
    forestCoeff a (LRootedForest.singleton τ) = coeff a (.tree τ) := by
  simp [forestCoeff, LRootedForest.singleton]

@[simp]
theorem forestCoeff_singleton_mset (a : LSeries α R) (τ : LRootedTree α) :
    forestCoeff a ({τ} : LRootedForest α) = coeff a (.tree τ) := by
  simp [forestCoeff]

@[simp]
theorem forestCoeff_add (a : LSeries α R) (φ ψ : LRootedForest α) :
    forestCoeff a (φ + ψ) = forestCoeff a φ * forestCoeff a ψ := by
  simp [forestCoeff, Multiset.map_add]

private def forestCoeffMonoidHom (a : LSeries α R) :
    Multiplicative (LRootedForest α) →* R where
  toFun φ := forestCoeff a (Multiplicative.toAdd φ)
  map_one' := by
    change forestCoeff a (0 : LRootedForest α) = 1
    simp
  map_mul' φ ψ := by
    change
      forestCoeff a (Multiplicative.toAdd (φ * ψ)) =
        forestCoeff a (Multiplicative.toAdd φ) * forestCoeff a (Multiplicative.toAdd ψ)
    change
      forestCoeff a (Multiplicative.toAdd φ + Multiplicative.toAdd ψ) =
        forestCoeff a (Multiplicative.toAdd φ) * forestCoeff a (Multiplicative.toAdd ψ)
    simp

/-- The labelled forest-algebra character induced by the tree coefficients of a series. -/
def toCharacter (a : LSeries α R) : LForestAlgebra.Character α R :=
  (AddMonoidAlgebra.lift R R (LRootedForest α)) (forestCoeffMonoidHom a)

@[simp]
theorem toCharacter_ofForest (a : LSeries α R) (φ : LRootedForest α) :
    toCharacter a (LForestAlgebra.ofForest (R := R) φ) = forestCoeff a φ := by
  simp [toCharacter, LForestAlgebra.ofForest, forestCoeffMonoidHom]

@[simp]
theorem toCharacter_evalForest (a : LSeries α R) (φ : LRootedForest α) :
    (toCharacter a).evalForest φ = forestCoeff a φ := by
  simp [LForestAlgebra.Character.evalForest]

@[simp]
theorem toCharacter_ofForest_zero (a : LSeries α R) :
    toCharacter a (LForestAlgebra.ofForest (R := R) 0) = 1 := by
  simp

@[simp]
theorem toCharacter_ofForest_singleton (a : LSeries α R) (τ : LRootedTree α) :
    toCharacter a (LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ)) =
      coeff a (.tree τ) := by
  simp

theorem ext_of_toCharacter_eq {a b : LSeries α R}
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
          (fun χ : LForestAlgebra.Character α R =>
            χ (LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ))) h
      simpa using hτ

theorem toCharacter_eq_iff {a b : LSeries α R}
    (ha : HasUnitConstant a) (hb : HasUnitConstant b) :
    toCharacter a = toCharacter b ↔ a = b := by
  constructor
  · exact ext_of_toCharacter_eq ha hb
  · intro h
    rw [h]

/-- Recover the unit-constant labelled B-series determined by a labelled forest character. -/
def ofCharacter (χ : LForestAlgebra.Character α R) : LSeries α R
  | .empty => 1
  | .tree τ => χ.evalForest (LRootedForest.singleton τ)

@[simp]
theorem ofCharacter_empty (χ : LForestAlgebra.Character α R) :
    coeff (ofCharacter χ) LTreeIndex.empty = 1 :=
  rfl

@[simp]
theorem ofCharacter_tree (χ : LForestAlgebra.Character α R) (τ : LRootedTree α) :
    coeff (ofCharacter χ) (.tree τ) = χ.evalForest (LRootedForest.singleton τ) :=
  rfl

theorem ofCharacter_hasUnitConstant (χ : LForestAlgebra.Character α R) :
    HasUnitConstant (ofCharacter χ) :=
  rfl

@[simp]
theorem toCharacter_ofCharacter (χ : LForestAlgebra.Character α R) :
    toCharacter (ofCharacter χ) = χ := by
  apply LForestAlgebra.Character.ext_tree
  intro τ
  change
    toCharacter (ofCharacter χ)
        (LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ)) =
      χ (LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ))
  rw [toCharacter_ofForest_singleton]
  rfl

theorem ofCharacter_toCharacter {a : LSeries α R} (ha : HasUnitConstant a) :
    ofCharacter (toCharacter a) = a := by
  funext τ
  cases τ with
  | empty =>
      change 1 = a LTreeIndex.empty
      exact ha.symm
  | tree τ =>
      change
        toCharacter a (LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ)) =
          a (LTreeIndex.tree τ)
      rw [toCharacter_ofForest_singleton]
      rfl

theorem forestCoeff_ofCharacter (χ : LForestAlgebra.Character α R) (φ : LRootedForest α) :
    forestCoeff (ofCharacter χ) φ = χ.evalForest φ := by
  rw [← toCharacter_ofForest (ofCharacter χ) φ]
  rw [toCharacter_ofCharacter]
  rfl

/-- Unit-constant labelled B-series are equivalent to labelled forest characters. -/
def characterEquiv : {a : LSeries α R // HasUnitConstant a} ≃
    LForestAlgebra.Character α R where
  toFun a := toCharacter a.1
  invFun χ := ⟨ofCharacter χ, ofCharacter_hasUnitConstant χ⟩
  left_inv a := by
    cases a with
    | mk a ha =>
        apply Subtype.ext
        exact ofCharacter_toCharacter ha
  right_inv χ := toCharacter_ofCharacter χ

@[simp]
theorem characterEquiv_apply (a : {a : LSeries α R // HasUnitConstant a}) :
    characterEquiv a = toCharacter a.1 :=
  rfl

@[simp]
theorem characterEquiv_symm_apply (χ : LForestAlgebra.Character α R) :
    ((characterEquiv (α := α) (R := R)).symm χ).1 = ofCharacter χ :=
  rfl

theorem characterEquiv_symm_forestCoeff
    (χ : LForestAlgebra.Character α R) (φ : LRootedForest α) :
    forestCoeff ((characterEquiv (α := α) (R := R)).symm χ).1 φ = χ.evalForest φ := by
  simp [forestCoeff_ofCharacter]

end

end ForestCharacter

/-- The labelled convolution identity coefficients. -/
def unit (α : Type u) (R : Type v) [Zero R] [One R] : LSeries α R
  | .empty => 1
  | .tree _ => 0

@[simp]
theorem coeff_unit_empty [Zero R] [One R] :
    coeff (unit α R) LTreeIndex.empty = 1 :=
  rfl

@[simp]
theorem coeff_unit_tree [Zero R] [One R] (τ : LRootedTree α) :
    coeff (unit α R) (.tree τ) = 0 :=
  rfl

theorem unit_hasUnitConstant [Zero R] [One R] : HasUnitConstant (unit α R) :=
  rfl

theorem forestCoeff_unit [CommSemiring R] (φ : LRootedForest α) :
    forestCoeff (unit α R) φ = LForestAlgebra.counitCoeff (R := R) φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  cases ts with
  | nil =>
      simp [forestCoeff, unit, LForestAlgebra.counitCoeff]
  | cons τ ts =>
      have hne : (((τ :: ts) : List (LRootedTree α)) : LRootedForest α) ≠ 0 :=
        (LRootedForest.order_pos_iff_ne_zero _).1 (LRootedForest.order_coe_cons_pos τ ts)
      simp [forestCoeff, unit, LForestAlgebra.counitCoeff, hne]

@[simp]
theorem toCharacter_unit_ofForest [CommSemiring R] (φ : LRootedForest α) :
    toCharacter (unit α R) (LForestAlgebra.ofForest (R := R) φ) =
      LForestAlgebra.counitCoeff (R := R) φ := by
  simp [forestCoeff_unit]

theorem toCharacter_unit [CommSemiring R] :
    toCharacter (unit α R) = LForestAlgebra.counit α R := by
  apply LForestAlgebra.Character.ext
  intro φ
  simp [LForestAlgebra.Character.evalForest, forestCoeff_unit]

theorem ofCharacter_counit [CommSemiring R] :
    ofCharacter (LForestAlgebra.counit α R) = unit α R := by
  apply ext_of_toCharacter_eq
  · exact ofCharacter_hasUnitConstant _
  · exact unit_hasUnitConstant
  · rw [toCharacter_ofCharacter, toCharacter_unit]

theorem characterEquiv_unit_counit [CommSemiring R] :
    characterEquiv ⟨unit α R, unit_hasUnitConstant⟩ = LForestAlgebra.counit α R := by
  exact toCharacter_unit

theorem characterEquiv_symm_counit [CommSemiring R] :
    ((characterEquiv (α := α) (R := R)).symm (LForestAlgebra.counit α R)).1 =
      unit α R := by
  simpa [characterEquiv_symm_apply] using ofCharacter_counit (α := α) (R := R)

/-- Exact labelled B-series coefficients, ignoring labels. -/
def exact (α : Type u) (R : Type v) [DivisionSemiring R] : LSeries α R :=
  fun τ => (LTreeIndex.treeFactorial τ : R)⁻¹

@[simp]
theorem coeff_exact [DivisionSemiring R] (τ : LTreeIndex α) :
    coeff (exact α R) τ = (LTreeIndex.treeFactorial τ : R)⁻¹ :=
  rfl

/-- Exact labelled B-series coefficients at time/step-size `h`, ignoring labels. -/
def scaledExact (α : Type u) (R : Type v) [DivisionSemiring R] (h : R) :
    LSeries α R :=
  fun τ => h ^ LTreeIndex.order τ * (LTreeIndex.treeFactorial τ : R)⁻¹

@[simp]
theorem coeff_scaledExact [DivisionSemiring R] (h : R) (τ : LTreeIndex α) :
    coeff (scaledExact α R h) τ =
      h ^ LTreeIndex.order τ * (LTreeIndex.treeFactorial τ : R)⁻¹ :=
  rfl

@[simp]
theorem scaledExact_one [DivisionSemiring R] : scaledExact α R (1 : R) = exact α R := by
  funext τ
  simp [scaledExact, exact]

@[simp]
theorem scaledExact_zero [DivisionSemiring R] : scaledExact α R (0 : R) = unit α R := by
  funext τ
  cases τ with
  | empty =>
      simp [scaledExact, unit]
  | tree τ =>
      have hτ : LRootedTree.order τ ≠ 0 := Nat.ne_of_gt (LRootedTree.order_pos τ)
      simp [scaledExact, unit, hτ]

theorem exact_hasUnitConstant [DivisionSemiring R] : HasUnitConstant (exact α R) := by
  simp [HasUnitConstant, constantCoeff, coeff, exact]

theorem scaledExact_hasUnitConstant [DivisionSemiring R] (h : R) :
    HasUnitConstant (scaledExact α R h) := by
  simp [HasUnitConstant, constantCoeff, coeff, scaledExact]

theorem coeff_exact_tree_graft [Field R] (a : α) (φ : LRootedForest α) :
    coeff (exact α R) (.tree (LRootedForest.graft a φ)) =
      ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simp [exact, LRootedForest.treeFactorial_graft]
  ac_rfl

theorem coeff_scaledExact_tree_graft [Field R] (h : R)
    (a : α) (φ : LRootedForest α) :
    coeff (scaledExact α R h) (.tree (LRootedForest.graft a φ)) =
      h ^ (1 + LRootedForest.order φ) *
        ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
          (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simp [scaledExact, LRootedForest.treeFactorial_graft]
  ring

theorem coeff_exact_tree_branches [Field R] (τ : LRootedTree α) :
    coeff (exact α R) (.tree τ) =
      (LRootedTree.order τ : R)⁻¹ *
        (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
  calc
    coeff (exact α R) (.tree τ) =
        coeff (exact α R)
          (.tree (LRootedForest.graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ))) := by
          rw [LRootedForest.graft_branches τ]
    _ = ((1 + LRootedForest.order (LRootedTree.branches τ) : Nat) : R)⁻¹ *
          (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
          exact coeff_exact_tree_graft (R := R) (LRootedTree.rootLabel τ)
            (LRootedTree.branches τ)
    _ = (LRootedTree.order τ : R)⁻¹ *
          (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
          rw [LRootedForest.order_branches τ]

theorem coeff_scaledExact_tree_branches [Field R] (h : R) (τ : LRootedTree α) :
    coeff (scaledExact α R h) (.tree τ) =
      h ^ LRootedTree.order τ *
        (LRootedTree.order τ : R)⁻¹ *
          (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
  calc
    coeff (scaledExact α R h) (.tree τ) =
        coeff (scaledExact α R h)
          (.tree (LRootedForest.graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ))) := by
          rw [LRootedForest.graft_branches τ]
    _ = h ^ (1 + LRootedForest.order (LRootedTree.branches τ)) *
          ((1 + LRootedForest.order (LRootedTree.branches τ) : Nat) : R)⁻¹ *
            (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
          exact coeff_scaledExact_tree_graft (R := R) h (LRootedTree.rootLabel τ)
            (LRootedTree.branches τ)
    _ = h ^ LRootedTree.order τ *
          (LRootedTree.order τ : R)⁻¹ *
            (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
          rw [LRootedForest.order_branches τ]

theorem coeff_exact_tree_butcherProduct [Field R] (φ : LRootedForest α)
    (τ : LRootedTree α) :
    coeff (exact α R) (.tree (LRootedForest.butcherProduct φ τ)) =
      ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  simp [exact, LRootedForest.treeFactorial_butcherProduct]
  ac_rfl

theorem coeff_scaledExact_tree_butcherProduct [Field R] (h : R)
    (φ : LRootedForest α) (τ : LRootedTree α) :
    coeff (scaledExact α R h) (.tree (LRootedForest.butcherProduct φ τ)) =
      h ^ (LRootedForest.order φ + LRootedTree.order τ) *
        ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
          (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  simp [scaledExact, LRootedForest.treeFactorial_butcherProduct]
  ring

theorem forestCoeff_exact [Field R] (φ : LRootedForest α) :
    forestCoeff (exact α R) φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestCoeff, LRootedForest.treeFactorial]
  | cons τ ts ih =>
      have ih' :
          (List.map (fun x => (LRootedTree.treeFactorial x : R)⁻¹) ts).prod =
            ((List.map (Nat.cast ∘ LRootedTree.treeFactorial) ts).prod)⁻¹ := by
        simpa [forestCoeff, LRootedForest.treeFactorial, exact] using ih
      simp [forestCoeff, LRootedForest.treeFactorial, exact]
      rw [ih']
      ring

theorem forestCoeff_scaledExact [Field R] (h : R) (φ : LRootedForest α) :
    forestCoeff (scaledExact α R h) φ =
      h ^ LRootedForest.order φ * (LRootedForest.treeFactorial φ : R)⁻¹ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestCoeff, LRootedForest.order, LRootedForest.treeFactorial]
  | cons τ ts ih =>
      have hprod :
          (List.map
              (fun x =>
                h ^ LRootedTree.order x * (LRootedTree.treeFactorial x : R)⁻¹) ts).prod =
            (List.map (fun x => h ^ LRootedTree.order x) ts).prod *
              (List.map (fun x => (LRootedTree.treeFactorial x : R)⁻¹) ts).prod := by
        induction ts with
        | nil =>
            simp
        | cons ξ ts ih =>
            simp [mul_assoc, mul_left_comm]
      have ih' :
          (List.map (fun x => h ^ LRootedTree.order x) ts).prod *
              (List.map (fun x => (LRootedTree.treeFactorial x : R)⁻¹) ts).prod =
            h ^ (List.map LRootedTree.order ts).sum *
              ((List.map (Nat.cast ∘ LRootedTree.treeFactorial) ts).prod)⁻¹ := by
        rw [← hprod]
        simpa [forestCoeff, LRootedForest.order, LRootedForest.treeFactorial,
          scaledExact] using ih
      simp [forestCoeff, LRootedForest.order, LRootedForest.treeFactorial, scaledExact]
      rw [ih', pow_add]
      ring

@[simp]
theorem forestCoeff_scaledExact_zero [Field R] (φ : LRootedForest α) :
    forestCoeff (scaledExact α R (0 : R)) φ =
      LForestAlgebra.counitCoeff (R := R) φ := by
  rw [scaledExact_zero]
  exact forestCoeff_unit φ

@[simp]
theorem toCharacter_exact_ofForest [Field R] (φ : LRootedForest α) :
    toCharacter (exact α R) (LForestAlgebra.ofForest (R := R) φ) =
      (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simp [forestCoeff_exact]

@[simp]
theorem toCharacter_scaledExact_ofForest [Field R] (h : R) (φ : LRootedForest α) :
    toCharacter (scaledExact α R h) (LForestAlgebra.ofForest (R := R) φ) =
      h ^ LRootedForest.order φ * (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simp [forestCoeff_scaledExact]

@[simp]
theorem toCharacter_scaledExact_zero [Field R] :
    toCharacter (scaledExact α R (0 : R)) = LForestAlgebra.counit α R := by
  rw [scaledExact_zero]
  exact toCharacter_unit

/-- Two labelled B-series agree through order `n`. -/
def AgreeUpToOrder (a b : LSeries α R) (n : Nat) : Prop :=
  ∀ τ, LTreeIndex.order τ ≤ n → coeff a τ = coeff b τ

theorem agreeUpToOrder_refl (a : LSeries α R) (n : Nat) : AgreeUpToOrder a a n := by
  intro τ hτ
  rfl

theorem AgreeUpToOrder.symm {a b : LSeries α R} {n : Nat}
    (h : AgreeUpToOrder a b n) : AgreeUpToOrder b a n := by
  intro τ hτ
  exact (h τ hτ).symm

theorem AgreeUpToOrder.trans {a b c : LSeries α R} {n : Nat}
    (hab : AgreeUpToOrder a b n) (hbc : AgreeUpToOrder b c n) :
    AgreeUpToOrder a c n := by
  intro τ hτ
  exact (hab τ hτ).trans (hbc τ hτ)

theorem AgreeUpToOrder.mono {a b : LSeries α R} {m n : Nat}
    (h : AgreeUpToOrder a b n) (hmn : m ≤ n) : AgreeUpToOrder a b m := by
  intro τ hτ
  exact h τ (hτ.trans hmn)

theorem agreeUpToOrder_succ_iff {a b : LSeries α R} {n : Nat} :
    AgreeUpToOrder a b (n + 1) ↔
      AgreeUpToOrder a b n ∧
        ∀ τ, LTreeIndex.order τ = n + 1 → coeff a τ = coeff b τ := by
  constructor
  · intro h
    exact ⟨h.mono (Nat.le_succ n), fun τ hτ => h τ (by omega)⟩
  · rintro ⟨hprev, htop⟩ τ hτ
    by_cases hle : LTreeIndex.order τ ≤ n
    · exact hprev τ hle
    · exact htop τ (by omega)

theorem AgreeUpToOrder.add [Add R] {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (a + b) (a' + b') n := by
  intro τ hτ
  change a τ + b τ = a' τ + b' τ
  rw [show a τ = a' τ by simpa [LSeries.coeff] using ha τ hτ]
  rw [show b τ = b' τ by simpa [LSeries.coeff] using hb τ hτ]

theorem AgreeUpToOrder.neg [Neg R] {a b : LSeries α R} {n : Nat}
    (h : AgreeUpToOrder a b n) : AgreeUpToOrder (-a) (-b) n := by
  intro τ hτ
  change -a τ = -b τ
  rw [show a τ = b τ by simpa [LSeries.coeff] using h τ hτ]

theorem AgreeUpToOrder.sub [Sub R] {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (a - b) (a' - b') n := by
  intro τ hτ
  change a τ - b τ = a' τ - b' τ
  rw [show a τ = a' τ by simpa [LSeries.coeff] using ha τ hτ]
  rw [show b τ = b' τ by simpa [LSeries.coeff] using hb τ hτ]

theorem AgreeUpToOrder.smul [SMul S R] {a b : LSeries α R} {n : Nat}
    (c : S) (h : AgreeUpToOrder a b n) :
    AgreeUpToOrder (c • a) (c • b) n := by
  intro τ hτ
  change c • a τ = c • b τ
  rw [show a τ = b τ by simpa [LSeries.coeff] using h τ hτ]

theorem agreeUpToOrder_iff_treeCoeff {a b : LSeries α R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ τ : LRootedTree α, LRootedTree.order τ ≤ n →
          coeff a (.tree τ) = coeff b (.tree τ) := by
  constructor
  · intro h
    exact
      ⟨by simpa [constantCoeff] using h LTreeIndex.empty (Nat.zero_le n),
        fun τ hτ => h (.tree τ) hτ⟩
  · rintro ⟨hconst, htree⟩ τ hτ
    cases τ with
    | empty =>
        simpa [constantCoeff] using hconst
    | tree τ =>
        exact htree τ hτ

theorem AgreeUpToOrder.forestCoeff [CommSemiring R] {a b : LSeries α R} {n : Nat}
    (h : AgreeUpToOrder a b n) {φ : LRootedForest α}
    (hφ : LRootedForest.order φ ≤ n) :
    LSeries.forestCoeff a φ = LSeries.forestCoeff b φ := by
  suffices hforest :
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        LSeries.forestCoeff a φ = LSeries.forestCoeff b φ from
    hforest φ hφ
  intro φ
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      intro hts
      simp [LSeries.forestCoeff]
  | cons τ ts ih =>
      intro hts
      have hτ : LTreeIndex.order (.tree τ) ≤ n := by
        have hle :
            LRootedTree.order τ ≤
              LRootedForest.order (((τ :: ts) : List (LRootedTree α)) : LRootedForest α) := by
          simp [LRootedForest.order]
        simpa using hle.trans hts
      have htail :
          LRootedForest.order (ts : LRootedForest α) ≤ n := by
        have hle :
            LRootedForest.order (ts : LRootedForest α) ≤
              LRootedForest.order (((τ :: ts) : List (LRootedTree α)) : LRootedForest α) := by
          simp [LRootedForest.order]
        exact hle.trans hts
      have hhead : LSeries.coeff a (.tree τ) = LSeries.coeff b (.tree τ) :=
        h (.tree τ) hτ
      have hhead' : a (.tree τ) = b (.tree τ) := by
        simpa [LSeries.coeff] using hhead
      have htail_eq :
          (List.map (fun x => a (.tree x)) ts).prod =
            (List.map (fun x => b (.tree x)) ts).prod := by
        simpa [LSeries.forestCoeff] using ih htail
      simp [LSeries.forestCoeff, hhead', htail_eq]

theorem AgreeUpToOrder.toCharacter_evalForest [CommSemiring R] {a b : LSeries α R}
    {n : Nat} (h : AgreeUpToOrder a b n) {φ : LRootedForest α}
    (hφ : LRootedForest.order φ ≤ n) :
    (toCharacter a).evalForest φ = (toCharacter b).evalForest φ := by
  simpa [toCharacter_evalForest] using h.forestCoeff hφ

theorem AgreeUpToOrder.toCharacter_ofForest [CommSemiring R] {a b : LSeries α R}
    {n : Nat} (h : AgreeUpToOrder a b n) {φ : LRootedForest α}
    (hφ : LRootedForest.order φ ≤ n) :
    toCharacter a (LForestAlgebra.ofForest (R := R) φ) =
      toCharacter b (LForestAlgebra.ofForest (R := R) φ) := by
  simpa [toCharacter_ofForest] using h.forestCoeff hφ

theorem agreeUpToOrder_iff_forestCoeff [CommSemiring R]
    {a b : LSeries α R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
          forestCoeff a φ = forestCoeff b φ := by
  constructor
  · intro h
    exact
      ⟨by simpa [constantCoeff] using h LTreeIndex.empty (Nat.zero_le n),
        fun φ hφ => h.forestCoeff hφ⟩
  · rintro ⟨hconst, hforest⟩ τ hτ
    cases τ with
    | empty =>
        simpa [constantCoeff] using hconst
    | tree τ =>
        have hsingleton := hforest (LRootedForest.singleton τ) (by simpa using hτ)
        simpa using hsingleton

theorem agreeUpToOrder_iff_toCharacter_evalForest [CommSemiring R]
    {a b : LSeries α R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
          (toCharacter a).evalForest φ = (toCharacter b).evalForest φ := by
  simpa [toCharacter_evalForest] using
    (agreeUpToOrder_iff_forestCoeff (a := a) (b := b) (n := n))

theorem agreeUpToOrder_iff_toCharacter_ofForest [CommSemiring R]
    {a b : LSeries α R} {n : Nat} :
    AgreeUpToOrder a b n ↔
      constantCoeff a = constantCoeff b ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
          toCharacter a (LForestAlgebra.ofForest (R := R) φ) =
            toCharacter b (LForestAlgebra.ofForest (R := R) φ) := by
  simpa [toCharacter_ofForest] using
    (agreeUpToOrder_iff_forestCoeff (a := a) (b := b) (n := n))

theorem agreeUpToOrder_of_eq {a b : LSeries α R} (h : a = b) (n : Nat) :
    AgreeUpToOrder a b n := by
  subst b
  exact agreeUpToOrder_refl a n

theorem eq_of_agreeUpToOrder_all {a b : LSeries α R}
    (h : ∀ n, AgreeUpToOrder a b n) : a = b := by
  funext τ
  exact h (LTreeIndex.order τ) τ le_rfl

theorem agreeUpToOrder_all_iff_eq {a b : LSeries α R} :
    (∀ n, AgreeUpToOrder a b n) ↔ a = b := by
  constructor
  · exact eq_of_agreeUpToOrder_all
  · intro h n
    exact agreeUpToOrder_of_eq h n

theorem agreeUpToOrder_all_iff_constantCoeff_toCharacter [CommSemiring R]
    {a b : LSeries α R} :
    (∀ n, AgreeUpToOrder a b n) ↔ constantCoeff a = constantCoeff b ∧
      toCharacter a = toCharacter b := by
  constructor
  · intro h
    rw [(agreeUpToOrder_all_iff_eq).1 h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hconst, hchar⟩ n
    rw [agreeUpToOrder_iff_toCharacter_ofForest]
    exact ⟨hconst, fun _ _ => by rw [hchar]⟩

/-- Coefficient-level order conditions for a labelled B-series. -/
def HasOrder [DivisionSemiring R] (a : LSeries α R) (n : Nat) : Prop :=
  AgreeUpToOrder a (exact α R) n

theorem hasOrder_iff [DivisionSemiring R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      ∀ τ, LTreeIndex.order τ ≤ n →
        LSeries.coeff a τ = (LTreeIndex.treeFactorial τ : R)⁻¹ :=
  Iff.rfl

theorem HasOrder.coeff [DivisionSemiring R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {τ : LTreeIndex α} (hτ : LTreeIndex.order τ ≤ n) :
    LSeries.coeff a τ = (LTreeIndex.treeFactorial τ : R)⁻¹ :=
  h τ hτ

theorem HasOrder.treeCoeff [DivisionSemiring R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {τ : LRootedTree α} (hτ : LRootedTree.order τ ≤ n) :
    LSeries.coeff a (LTreeIndex.tree τ) = (LRootedTree.treeFactorial τ : R)⁻¹ :=
  HasOrder.coeff h (τ := LTreeIndex.tree τ) hτ

theorem HasOrder.coeff_tree_graft [Field R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {x : α} {φ : LRootedForest α}
    (hφ : 1 + LRootedForest.order φ ≤ n) :
    LSeries.coeff a (LTreeIndex.tree (LRootedForest.graft x φ)) =
      ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial φ : R)⁻¹ := by
  calc
    LSeries.coeff a (LTreeIndex.tree (LRootedForest.graft x φ)) =
        LSeries.coeff (exact α R) (LTreeIndex.tree (LRootedForest.graft x φ)) := by
          exact h.treeCoeff (by simpa using hφ)
    _ = ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial φ : R)⁻¹ := by
          exact coeff_exact_tree_graft (R := R) x φ

theorem HasOrder.coeff_tree_branches [Field R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {τ : LRootedTree α} (hτ : LRootedTree.order τ ≤ n) :
    LSeries.coeff a (LTreeIndex.tree τ) =
      (LRootedTree.order τ : R)⁻¹ *
        (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
  calc
    LSeries.coeff a (LTreeIndex.tree τ) =
        LSeries.coeff (exact α R) (LTreeIndex.tree τ) := by
          exact h.treeCoeff hτ
    _ = (LRootedTree.order τ : R)⁻¹ *
        (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
          exact coeff_exact_tree_branches (R := R) τ

theorem HasOrder.hasUnitConstant [DivisionSemiring R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) : HasUnitConstant a := by
  simpa [HasUnitConstant, constantCoeff, exact] using
    HasOrder.coeff h (τ := LTreeIndex.empty) (Nat.zero_le n)

theorem hasOrder_iff_treeCoeff [DivisionSemiring R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ τ : LRootedTree α, LRootedTree.order τ ≤ n →
          LSeries.coeff a (LTreeIndex.tree τ) = (LRootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun τ hτ => h.treeCoeff hτ⟩
  · rintro ⟨ha, htree⟩ τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        simpa [exact] using htree τ hτ

theorem HasOrder.mono [DivisionSemiring R] {a : LSeries α R} {m n : Nat}
    (h : HasOrder a n) (hmn : m ≤ n) : HasOrder a m :=
  AgreeUpToOrder.mono h hmn

theorem hasOrder_succ_iff [DivisionSemiring R] {a : LSeries α R} {n : Nat} :
    HasOrder a (n + 1) ↔
      HasOrder a n ∧
        ∀ τ, LTreeIndex.order τ = n + 1 →
          LSeries.coeff a τ = (LTreeIndex.treeFactorial τ : R)⁻¹ := by
  exact agreeUpToOrder_succ_iff

theorem HasOrder.of_agreeUpToOrder [DivisionSemiring R] {a b : LSeries α R} {n : Nat}
    (hab : AgreeUpToOrder a b n) (ha : HasOrder a n) : HasOrder b n :=
  hab.symm.trans ha

theorem hasOrder_congr [DivisionSemiring R] {a b : LSeries α R} {n : Nat}
    (hab : AgreeUpToOrder a b n) : HasOrder a n ↔ HasOrder b n := by
  constructor
  · exact HasOrder.of_agreeUpToOrder hab
  · exact HasOrder.of_agreeUpToOrder hab.symm

theorem hasOrder_all_congr [DivisionSemiring R] {a b : LSeries α R}
    (hab : ∀ n, AgreeUpToOrder a b n) :
    (∀ n, HasOrder a n) ↔ ∀ n, HasOrder b n := by
  constructor
  · intro ha n
    exact (hasOrder_congr (hab n)).1 (ha n)
  · intro hb n
    exact (hasOrder_congr (hab n)).2 (hb n)

theorem HasOrder.agreeUpToOrder [DivisionSemiring R] {a b : LSeries α R} {n : Nat}
    (ha : HasOrder a n) (hb : HasOrder b n) : AgreeUpToOrder a b n :=
  ha.trans hb.symm

theorem hasOrder_zero_iff [DivisionSemiring R] {a : LSeries α R} :
    HasOrder a 0 ↔ HasUnitConstant a := by
  constructor
  · intro h
    exact h.hasUnitConstant
  · intro ha τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have hpos := LRootedTree.order_pos τ
        simp at hτ
        omega

theorem HasOrder.oneNodeCoeff [DivisionSemiring R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) (hn : 1 ≤ n) (x : α) :
    LSeries.coeff a (LTreeIndex.tree (LRootedForest.graft x 0)) = 1 := by
  simpa using
    HasOrder.treeCoeff h (τ := LRootedForest.graft x 0) (by simpa using hn)

theorem hasOrder_one_iff [DivisionSemiring R] {a : LSeries α R} :
    HasOrder a 1 ↔
      HasUnitConstant a ∧
        ∀ x : α, LSeries.coeff a (LTreeIndex.tree (LRootedForest.graft x 0)) = 1 := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun x => h.oneNodeCoeff le_rfl x⟩
  · rintro ⟨ha, hroot⟩ τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have horder : LRootedTree.order τ = 1 := by
          have hpos := LRootedTree.order_pos τ
          simp at hτ
          omega
        rw [(LRootedForest.order_eq_one_iff_eq_graft_root_zero τ).1 horder]
        simpa [exact] using hroot (LRootedTree.rootLabel τ)

theorem exact_hasOrder [DivisionSemiring R] (n : Nat) : HasOrder (exact α R) n :=
  agreeUpToOrder_refl (exact α R) n

theorem eq_exact_of_hasOrder_all [DivisionSemiring R] {a : LSeries α R}
    (h : ∀ n, HasOrder a n) : a = exact α R := by
  funext τ
  exact h (LTreeIndex.order τ) τ le_rfl

theorem hasOrder_all_iff_eq_exact [DivisionSemiring R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔ a = exact α R := by
  constructor
  · exact eq_exact_of_hasOrder_all
  · intro h n
    rw [h]
    exact exact_hasOrder n

theorem hasOrder_all_iff_treeCoeff [DivisionSemiring R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ τ : LRootedTree α,
          LSeries.coeff a (LTreeIndex.tree τ) = (LRootedTree.treeFactorial τ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun τ => (h (LRootedTree.order τ)).treeCoeff le_rfl⟩
  · rintro ⟨ha, htree⟩ n
    rw [hasOrder_iff_treeCoeff]
    exact ⟨ha, fun τ _ => htree τ⟩

theorem hasOrder_iff_forestCoeff [Field R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
          LSeries.forestCoeff a φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun φ hφ => by
      rw [AgreeUpToOrder.forestCoeff h hφ, forestCoeff_exact]⟩
  · rintro ⟨ha, hforest⟩ τ hτ
    cases τ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have hsingleton :
            LSeries.forestCoeff a (LRootedForest.singleton τ) =
              (LRootedForest.treeFactorial (LRootedForest.singleton τ) : R)⁻¹ :=
          hforest (LRootedForest.singleton τ) (by simpa using hτ)
        simpa [exact] using hsingleton

theorem hasOrder_iff_toCharacter_evalForest [Field R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
          (toCharacter a).evalForest φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_evalForest] using (hasOrder_iff_forestCoeff (a := a) (n := n))

theorem hasOrder_iff_toCharacter_ofForest [Field R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
          toCharacter a (LForestAlgebra.ofForest (R := R) φ) =
            (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_ofForest] using (hasOrder_iff_forestCoeff (a := a) (n := n))

theorem HasOrder.forestCoeff [Field R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    LSeries.forestCoeff a φ = (LRootedForest.treeFactorial φ : R)⁻¹ :=
  ((hasOrder_iff_forestCoeff (a := a) (n := n)).1 h).2 φ hφ

theorem HasOrder.toCharacter_evalForest [Field R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    (toCharacter a).evalForest φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_evalForest] using h.forestCoeff hφ

theorem HasOrder.toCharacter_ofForest [Field R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    toCharacter a (LForestAlgebra.ofForest (R := R) φ) =
      (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_ofForest] using h.forestCoeff hφ

theorem hasOrder_iff_coeff_tree_graft [Field R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ (x : α) (φ : LRootedForest α), 1 + LRootedForest.order φ ≤ n →
          LSeries.coeff a (LTreeIndex.tree (LRootedForest.graft x φ)) =
            ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
              (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun x φ hφ => h.coeff_tree_graft hφ⟩
  · rintro ⟨ha, hgraft⟩ ξ hξ
    cases ξ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        calc
          LSeries.coeff a (LTreeIndex.tree τ) =
              LSeries.coeff a
                (LTreeIndex.tree
                  (LRootedForest.graft (LRootedTree.rootLabel τ) (LRootedTree.branches τ))) := by
                rw [LRootedForest.graft_branches τ]
          _ = ((1 + LRootedForest.order (LRootedTree.branches τ) : Nat) : R)⁻¹ *
                (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
                exact hgraft (LRootedTree.rootLabel τ) (LRootedTree.branches τ) (by
                  rw [LRootedForest.order_branches τ]
                  exact hξ)
          _ = (LTreeIndex.treeFactorial (LTreeIndex.tree τ) : R)⁻¹ := by
                simpa [LSeries.coeff, LSeries.exact, LRootedForest.order_branches] using
                  (LSeries.coeff_exact_tree_branches (R := R) τ).symm

theorem hasOrder_iff_coeff_tree_branches [Field R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ τ : LRootedTree α, LRootedTree.order τ ≤ n →
          LSeries.coeff a (LTreeIndex.tree τ) =
            (LRootedTree.order τ : R)⁻¹ *
              (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun τ hτ => h.coeff_tree_branches hτ⟩
  · rintro ⟨ha, hbranches⟩ ξ hξ
    cases ξ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        calc
          LSeries.coeff a (LTreeIndex.tree τ) =
              (LRootedTree.order τ : R)⁻¹ *
                (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ :=
                hbranches τ hξ
          _ = (LTreeIndex.treeFactorial (LTreeIndex.tree τ) : R)⁻¹ := by
                simpa [LSeries.coeff, LSeries.exact] using
                  (LSeries.coeff_exact_tree_branches (R := R) τ).symm

theorem HasOrder.coeff_butcherProduct [Field R] {a : LSeries α R} {n : Nat}
    (h : HasOrder a n) {φ : LRootedForest α} {τ : LRootedTree α}
    (horder : LRootedForest.order φ + LRootedTree.order τ ≤ n) :
    LSeries.coeff a (LTreeIndex.tree (LRootedForest.butcherProduct φ τ)) =
      ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  calc
    LSeries.coeff a (LTreeIndex.tree (LRootedForest.butcherProduct φ τ)) =
        LSeries.coeff (exact α R) (LTreeIndex.tree (LRootedForest.butcherProduct φ τ)) := by
          exact h.treeCoeff (by simpa using horder)
    _ = ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
        (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
          exact coeff_exact_tree_butcherProduct (R := R) φ τ

theorem hasOrder_iff_coeff_butcherProduct [Field R] {a : LSeries α R} {n : Nat} :
    HasOrder a n ↔
      HasUnitConstant a ∧
        ∀ (φ : LRootedForest α) (τ : LRootedTree α),
          LRootedForest.order φ + LRootedTree.order τ ≤ n →
            LSeries.coeff a (LTreeIndex.tree (LRootedForest.butcherProduct φ τ)) =
              ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
                (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨h.hasUnitConstant, fun φ τ horder => HasOrder.coeff_butcherProduct h horder⟩
  · rintro ⟨ha, h⟩
    rw [hasOrder_iff]
    intro ξ hξ
    cases ξ with
    | empty =>
        simpa [HasUnitConstant, constantCoeff, exact] using ha
    | tree τ =>
        have horder :
            LRootedForest.order (LRootedTree.branches τ) +
                LRootedTree.order (LRootedForest.graft (LRootedTree.rootLabel τ) 0) ≤ n := by
          have hbranches :
              LRootedForest.order (LRootedTree.branches τ) +
                  LRootedTree.order (LRootedForest.graft (LRootedTree.rootLabel τ) 0) =
                LRootedTree.order τ := by
            simp
            have h := LRootedForest.order_branches τ
            omega
          rw [hbranches]
          exact hξ
        have hcondition :=
          h (LRootedTree.branches τ)
            (LRootedForest.graft (LRootedTree.rootLabel τ) 0) horder
        calc
          LSeries.coeff a (LTreeIndex.tree τ) =
              LSeries.coeff a
                (LTreeIndex.tree
                  (LRootedForest.butcherProduct (LRootedTree.branches τ)
                    (LRootedForest.graft (LRootedTree.rootLabel τ) 0))) := by
                simp [LRootedForest.butcherProduct]
          _ = ((LRootedForest.order (LRootedTree.branches τ) +
                  LRootedTree.order (LRootedForest.graft (LRootedTree.rootLabel τ) 0) :
                Nat) : R)⁻¹ *
                (LRootedForest.treeFactorial
                  (LRootedTree.branches τ +
                    LRootedTree.branches (LRootedForest.graft (LRootedTree.rootLabel τ) 0)) :
                  R)⁻¹ :=
                hcondition
          _ = (LTreeIndex.treeFactorial (LTreeIndex.tree τ) : R)⁻¹ := by
                have hexact :=
                  (coeff_exact_tree_butcherProduct (R := R)
                    (LRootedTree.branches τ)
                    (LRootedForest.graft (LRootedTree.rootLabel τ) 0)).symm
                simpa [LSeries.coeff, LSeries.exact, LRootedForest.butcherProduct] using hexact

theorem hasOrder_all_iff_forestCoeff [Field R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ φ : LRootedForest α,
          LSeries.forestCoeff a φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun φ => (h (LRootedForest.order φ)).forestCoeff le_rfl⟩
  · rintro ⟨ha, hforest⟩ n
    rw [hasOrder_iff_forestCoeff]
    exact ⟨ha, fun φ _ => hforest φ⟩

theorem hasOrder_all_iff_coeff_tree_graft [Field R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ (x : α) (φ : LRootedForest α),
          LSeries.coeff a (LTreeIndex.tree (LRootedForest.graft x φ)) =
            ((1 + LRootedForest.order φ : Nat) : R)⁻¹ *
              (LRootedForest.treeFactorial φ : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun x φ =>
      (h (1 + LRootedForest.order φ)).coeff_tree_graft le_rfl⟩
  · rintro ⟨ha, hgraft⟩ n
    rw [hasOrder_iff_coeff_tree_graft]
    exact ⟨ha, fun x φ _ => hgraft x φ⟩

theorem hasOrder_all_iff_coeff_tree_branches [Field R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ τ : LRootedTree α,
          LSeries.coeff a (LTreeIndex.tree τ) =
            (LRootedTree.order τ : R)⁻¹ *
              (LRootedForest.treeFactorial (LRootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun τ =>
      (h (LRootedTree.order τ)).coeff_tree_branches le_rfl⟩
  · rintro ⟨ha, hbranches⟩ n
    rw [hasOrder_iff_coeff_tree_branches]
    exact ⟨ha, fun τ _ => hbranches τ⟩

theorem hasOrder_all_iff_toCharacter_evalForest [Field R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ φ : LRootedForest α,
          (toCharacter a).evalForest φ = (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_evalForest] using (hasOrder_all_iff_forestCoeff (a := a))

theorem hasOrder_all_iff_toCharacter_ofForest [Field R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ φ : LRootedForest α,
          toCharacter a (LForestAlgebra.ofForest (R := R) φ) =
            (LRootedForest.treeFactorial φ : R)⁻¹ := by
  simpa [toCharacter_ofForest] using (hasOrder_all_iff_forestCoeff (a := a))

theorem hasOrder_all_iff_toCharacter_eq_exact [Field R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧ toCharacter a = toCharacter (exact α R) := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, by rw [eq_exact_of_hasOrder_all h]⟩
  · rintro ⟨ha, hchar⟩
    rw [hasOrder_all_iff_eq_exact]
    exact ext_of_toCharacter_eq ha exact_hasUnitConstant hchar

theorem characterEquiv_hasOrder_all_iff_exact [Field R]
    (a : {a : LSeries α R // HasUnitConstant a}) :
    (∀ n, HasOrder a.1 n) ↔
      characterEquiv a = characterEquiv ⟨exact α R, exact_hasUnitConstant⟩ := by
  constructor
  · intro h
    apply congrArg characterEquiv
    apply Subtype.ext
    exact (hasOrder_all_iff_eq_exact).1 h
  · intro h
    rw [hasOrder_all_iff_toCharacter_eq_exact]
    exact ⟨a.2, by simpa [characterEquiv_apply] using h⟩

theorem hasOrder_all_iff_coeff_butcherProduct [Field R] {a : LSeries α R} :
    (∀ n, HasOrder a n) ↔
      HasUnitConstant a ∧
        ∀ (φ : LRootedForest α) (τ : LRootedTree α),
          LSeries.coeff a (LTreeIndex.tree (LRootedForest.butcherProduct φ τ)) =
            ((LRootedForest.order φ + LRootedTree.order τ : Nat) : R)⁻¹ *
              (LRootedForest.treeFactorial (φ + LRootedTree.branches τ) : R)⁻¹ := by
  constructor
  · intro h
    exact ⟨(h 0).hasUnitConstant, fun φ τ =>
      (h (LRootedForest.order φ + LRootedTree.order τ)).coeff_butcherProduct le_rfl⟩
  · rintro ⟨ha, h⟩ n
    rw [hasOrder_iff_coeff_butcherProduct]
    exact ⟨ha, fun φ τ _ => h φ τ⟩

/-- Pull a labelled B-series back along a relabelling map. -/
def comapMapLabels (f : α → β) (a : LSeries β R) : LSeries α R :=
  fun τ => coeff a (LTreeIndex.mapLabels f τ)

@[simp]
theorem coeff_comapMapLabels (f : α → β) (a : LSeries β R) (τ : LTreeIndex α) :
    coeff (comapMapLabels f a) τ = coeff a (LTreeIndex.mapLabels f τ) :=
  rfl

theorem forestCoeff_comapMapLabels [CommSemiring R] (f : α → β)
    (a : LSeries β R) (φ : LRootedForest α) :
    forestCoeff (comapMapLabels f a) φ =
      forestCoeff a (LRootedForest.mapLabels f φ) := by
  simp [forestCoeff, comapMapLabels, LRootedForest.mapLabels, Multiset.map_map]

theorem toCharacter_comapMapLabels [CommSemiring R] (f : α → β) (a : LSeries β R) :
    toCharacter (comapMapLabels f a) =
      LForestAlgebra.Character.comapMapLabels f (toCharacter a) := by
  apply LForestAlgebra.Character.ext
  intro φ
  rw [LForestAlgebra.Character.comapMapLabels_evalForest]
  simp [LForestAlgebra.Character.evalForest, forestCoeff_comapMapLabels]

theorem hasUnitConstant_comapMapLabels [One R] (f : α → β) {a : LSeries β R}
    (ha : HasUnitConstant a) : HasUnitConstant (comapMapLabels f a) := by
  simpa [HasUnitConstant, constantCoeff, comapMapLabels] using ha

@[simp]
theorem comapMapLabels_id (a : LSeries α R) :
    comapMapLabels (fun x : α => x) a = a := by
  funext τ
  change a (LTreeIndex.mapLabels id τ) = a τ
  rw [LTreeIndex.mapLabels_id]

theorem comapMapLabels_comp (g : β → γ) (f : α → β) (a : LSeries γ R) :
    comapMapLabels f (comapMapLabels g a) = comapMapLabels (g ∘ f) a := by
  funext τ
  change a (LTreeIndex.mapLabels g (LTreeIndex.mapLabels f τ)) =
    a (LTreeIndex.mapLabels (g ∘ f) τ)
  rw [LTreeIndex.mapLabels_comp]

@[simp]
theorem comapMapLabels_unit [Zero R] [One R] (f : α → β) :
    comapMapLabels f (unit β R) = unit α R := by
  funext τ
  cases τ <;> rfl

@[simp]
theorem comapMapLabels_exact [DivisionSemiring R] (f : α → β) :
    comapMapLabels f (exact β R) = exact α R := by
  funext τ
  cases τ <;> simp [comapMapLabels, exact]

@[simp]
theorem comapMapLabels_scaledExact [DivisionSemiring R] (f : α → β) (h : R) :
    comapMapLabels f (scaledExact β R h) = scaledExact α R h := by
  funext τ
  cases τ <;> simp [comapMapLabels, scaledExact]

theorem agreeUpToOrder_comapMapLabels {a b : LSeries β R} {n : Nat} (f : α → β)
    (h : AgreeUpToOrder a b n) :
    AgreeUpToOrder (comapMapLabels f a) (comapMapLabels f b) n := by
  intro τ hτ
  exact h (LTreeIndex.mapLabels f τ) (by simpa using hτ)

theorem agreeUpToOrder_comapMapLabels_iff_of_surjective
    {a b : LSeries β R} {n : Nat} {f : α → β} (hf : Function.Surjective f) :
    AgreeUpToOrder (comapMapLabels f a) (comapMapLabels f b) n ↔
      AgreeUpToOrder a b n := by
  constructor
  · intro h τ hτ
    classical
    let g : β → α := fun x => Classical.choose (hf x)
    have hfg : ∀ x, f (g x) = x := fun x => Classical.choose_spec (hf x)
    have hτ' : LTreeIndex.order (LTreeIndex.mapLabels g τ) ≤ n := by
      simpa using hτ
    have hcoeff := h (LTreeIndex.mapLabels g τ) hτ'
    simpa [comapMapLabels, LTreeIndex.mapLabels_comp_eq_id f g hfg τ] using hcoeff
  · exact agreeUpToOrder_comapMapLabels f

theorem comapMapLabels_hasOrder [DivisionSemiring R] {a : LSeries β R} {n : Nat}
    (f : α → β) (h : HasOrder a n) : HasOrder (comapMapLabels f a) n := by
  intro τ hτ
  simpa [comapMapLabels, exact] using
    h (LTreeIndex.mapLabels f τ) (by simpa using hτ)

theorem comapMapLabels_hasOrder_iff_of_surjective [DivisionSemiring R]
    {a : LSeries β R} {n : Nat} {f : α → β} (hf : Function.Surjective f) :
    HasOrder (comapMapLabels f a) n ↔ HasOrder a n := by
  constructor
  · intro h τ hτ
    classical
    let g : β → α := fun x => Classical.choose (hf x)
    have hfg : ∀ x, f (g x) = x := fun x => Classical.choose_spec (hf x)
    have hτ' : LTreeIndex.order (LTreeIndex.mapLabels g τ) ≤ n := by
      simpa using hτ
    have hcoeff := h (LTreeIndex.mapLabels g τ) hτ'
    simpa [comapMapLabels, exact, LTreeIndex.mapLabels_comp_eq_id f g hfg τ] using hcoeff
  · exact comapMapLabels_hasOrder f

theorem agreeUpToOrder_all_comapMapLabels {a b : LSeries β R}
    (f : α → β) (h : ∀ n, AgreeUpToOrder a b n) :
    ∀ n, AgreeUpToOrder (comapMapLabels f a) (comapMapLabels f b) n :=
  fun n => agreeUpToOrder_comapMapLabels f (h n)

theorem agreeUpToOrder_all_comapMapLabels_iff_of_surjective
    {a b : LSeries β R} {f : α → β} (hf : Function.Surjective f) :
    (∀ n, AgreeUpToOrder (comapMapLabels f a) (comapMapLabels f b) n) ↔
      ∀ n, AgreeUpToOrder a b n := by
  constructor
  · intro h n
    exact (agreeUpToOrder_comapMapLabels_iff_of_surjective (n := n) hf).1 (h n)
  · intro h n
    exact agreeUpToOrder_comapMapLabels f (h n)

theorem comapMapLabels_hasOrder_all [DivisionSemiring R] {a : LSeries β R}
    (f : α → β) (h : ∀ n, HasOrder a n) :
    ∀ n, HasOrder (comapMapLabels f a) n :=
  fun n => comapMapLabels_hasOrder f (h n)

theorem comapMapLabels_hasOrder_all_iff_of_surjective [DivisionSemiring R]
    {a : LSeries β R} {f : α → β} (hf : Function.Surjective f) :
    (∀ n, HasOrder (comapMapLabels f a) n) ↔ ∀ n, HasOrder a n := by
  constructor
  · intro h n
    exact (comapMapLabels_hasOrder_iff_of_surjective (n := n) hf).1 (h n)
  · intro h n
    exact comapMapLabels_hasOrder f (h n)

/-- Restrict a labelled B-series to trees where every vertex has the same label. -/
def comapConstLabel (x : α) (a : LSeries α R) : Series R :=
  fun τ => coeff a (LTreeIndex.constLabel x τ)

@[simp]
theorem coeff_comapConstLabel (x : α) (a : LSeries α R) (τ : TreeIndex) :
    Series.coeff (comapConstLabel x a) τ = coeff a (LTreeIndex.constLabel x τ) :=
  rfl

theorem forestCoeff_comapConstLabel [CommSemiring R] (x : α)
    (a : LSeries α R) (φ : RootedForest) :
    Series.forestCoeff (comapConstLabel x a) φ =
      forestCoeff a (LRootedForest.constLabel x φ) := by
  simp [Series.forestCoeff, forestCoeff, comapConstLabel, LRootedForest.constLabel,
    Multiset.map_map]

theorem toCharacter_comapConstLabel [CommSemiring R] (x : α) (a : LSeries α R) :
    Series.toCharacter (comapConstLabel x a) =
      LForestAlgebra.Character.comapConstLabel x (toCharacter a) := by
  apply ForestAlgebra.Character.ext
  intro φ
  rw [LForestAlgebra.Character.comapConstLabel_evalForest]
  simp [ForestAlgebra.Character.evalForest, LForestAlgebra.Character.evalForest,
    forestCoeff_comapConstLabel]

theorem hasUnitConstant_comapConstLabel [One R] (x : α) {a : LSeries α R}
    (ha : HasUnitConstant a) : Series.HasUnitConstant (comapConstLabel x a) := by
  simpa [Series.HasUnitConstant, Series.constantCoeff, HasUnitConstant, constantCoeff,
    comapConstLabel] using ha

@[simp]
theorem comapConstLabel_unit [Zero R] [One R] (x : α) :
    comapConstLabel x (unit α R) = Series.unit R := by
  funext τ
  cases τ <;> rfl

@[simp]
theorem comapConstLabel_exact [DivisionSemiring R] (x : α) :
    comapConstLabel x (exact α R) = Series.exact R := by
  funext τ
  cases τ <;> simp [comapConstLabel, exact, Series.exact]

@[simp]
theorem comapConstLabel_scaledExact [DivisionSemiring R] (x : α) (h : R) :
    comapConstLabel x (scaledExact α R h) = Series.scaledExact h := by
  funext τ
  cases τ <;> simp [comapConstLabel, scaledExact, Series.scaledExact]

theorem agreeUpToOrder_comapConstLabel {a b : LSeries α R} {n : Nat}
    (x : α) (h : AgreeUpToOrder a b n) :
    Series.AgreeUpToOrder (comapConstLabel x a) (comapConstLabel x b) n := by
  intro τ hτ
  exact h (LTreeIndex.constLabel x τ) (by simpa using hτ)

theorem comapConstLabel_hasOrder [DivisionSemiring R] {a : LSeries α R} {n : Nat}
    (x : α) (h : HasOrder a n) : Series.HasOrder (comapConstLabel x a) n := by
  intro τ hτ
  simpa [comapConstLabel, exact, Series.exact] using
    h (LTreeIndex.constLabel x τ) (by simpa using hτ)

theorem agreeUpToOrder_all_comapConstLabel {a b : LSeries α R}
    (x : α) (h : ∀ n, AgreeUpToOrder a b n) :
    ∀ n, Series.AgreeUpToOrder (comapConstLabel x a) (comapConstLabel x b) n :=
  fun n => agreeUpToOrder_comapConstLabel x (h n)

theorem comapConstLabel_hasOrder_all [DivisionSemiring R] {a : LSeries α R}
    (x : α) (h : ∀ n, HasOrder a n) :
    ∀ n, Series.HasOrder (comapConstLabel x a) n :=
  fun n => comapConstLabel_hasOrder x (h n)

/-- Pull an unlabelled B-series back to labelled trees by forgetting labels. -/
def comapEraseLabels (a : Series R) : LSeries α R :=
  fun τ => Series.coeff a (LTreeIndex.erase τ)

@[simp]
theorem coeff_comapEraseLabels (a : Series R) (τ : LTreeIndex α) :
    coeff (comapEraseLabels a) τ = Series.coeff a (LTreeIndex.erase τ) :=
  rfl

theorem forestCoeff_comapEraseLabels [CommSemiring R] (a : Series R)
    (φ : LRootedForest α) :
    forestCoeff (comapEraseLabels a) φ =
      Series.forestCoeff a (LRootedForest.erase φ) := by
  simp [forestCoeff, comapEraseLabels, LRootedForest.erase, Series.forestCoeff,
    Multiset.map_map]

theorem toCharacter_comapEraseLabels [CommSemiring R] (a : Series R) :
    toCharacter (comapEraseLabels (α := α) a) =
      LForestAlgebra.Character.comapEraseLabels (α := α) (Series.toCharacter a) := by
  apply LForestAlgebra.Character.ext
  intro φ
  rw [LForestAlgebra.Character.comapEraseLabels_evalForest]
  simp [LForestAlgebra.Character.evalForest, forestCoeff_comapEraseLabels]

theorem hasUnitConstant_comapEraseLabels [One R] {a : Series R}
    (ha : Series.HasUnitConstant a) : HasUnitConstant (comapEraseLabels (α := α) a) := by
  simpa [HasUnitConstant, constantCoeff, Series.HasUnitConstant, Series.constantCoeff,
    comapEraseLabels] using ha

theorem ofCharacter_comapMapLabels [CommSemiring R] (f : α → β)
    (χ : LForestAlgebra.Character β R) :
    ofCharacter (LForestAlgebra.Character.comapMapLabels f χ) =
      comapMapLabels f (ofCharacter χ) := by
  funext τ
  cases τ with
  | empty => rfl
  | tree τ =>
      change
        (LForestAlgebra.Character.comapMapLabels f χ).evalForest
            (LRootedForest.singleton τ) =
          χ.evalForest (LRootedForest.singleton (LRootedTree.map f τ))
      rw [LForestAlgebra.Character.comapMapLabels_evalForest,
        LRootedForest.mapLabels_singleton]

theorem ofCharacter_comapEraseLabels [CommSemiring R] (χ : ForestAlgebra.Character R) :
    ofCharacter (LForestAlgebra.Character.comapEraseLabels (α := α) χ) =
      comapEraseLabels (α := α) (Series.ofCharacter χ) := by
  funext τ
  cases τ with
  | empty => rfl
  | tree τ =>
      change
        (LForestAlgebra.Character.comapEraseLabels χ).evalForest
            (LRootedForest.singleton τ) =
          χ.evalForest (RootedForest.singleton (LRootedTree.erase τ))
      rw [LForestAlgebra.Character.comapEraseLabels_evalForest,
        LRootedForest.erase_singleton]
      rfl

theorem ofCharacter_comapConstLabel [CommSemiring R] (x : α)
    (χ : LForestAlgebra.Character α R) :
    Series.ofCharacter (LForestAlgebra.Character.comapConstLabel x χ) =
      comapConstLabel x (ofCharacter χ) := by
  funext τ
  cases τ with
  | empty => rfl
  | tree τ =>
      change
        (LForestAlgebra.Character.comapConstLabel x χ).evalForest
            (RootedForest.singleton τ) =
          χ.evalForest (LRootedForest.singleton (LRootedTree.constLabel x τ))
      rw [LForestAlgebra.Character.comapConstLabel_evalForest,
        LRootedForest.constLabel_singleton]

theorem characterEquiv_comapMapLabels [CommSemiring R] (f : α → β)
    (a : {a : LSeries β R // HasUnitConstant a}) :
    characterEquiv ⟨comapMapLabels f a.1, hasUnitConstant_comapMapLabels f a.2⟩ =
      LForestAlgebra.Character.comapMapLabels f (characterEquiv a) := by
  simp [characterEquiv_apply, toCharacter_comapMapLabels]

theorem characterEquiv_comapConstLabel [CommSemiring R] (x : α)
    (a : {a : LSeries α R // HasUnitConstant a}) :
    Series.characterEquiv ⟨comapConstLabel x a.1, hasUnitConstant_comapConstLabel x a.2⟩ =
      LForestAlgebra.Character.comapConstLabel x (characterEquiv a) := by
  simp [Series.characterEquiv_apply, characterEquiv_apply, toCharacter_comapConstLabel]

theorem characterEquiv_comapEraseLabels [CommSemiring R]
    (a : {a : Series R // Series.HasUnitConstant a}) :
    characterEquiv
        ⟨comapEraseLabels (α := α) a.1, hasUnitConstant_comapEraseLabels (α := α) a.2⟩ =
      LForestAlgebra.Character.comapEraseLabels (α := α) (Series.characterEquiv a) := by
  simp [characterEquiv_apply, Series.characterEquiv_apply, toCharacter_comapEraseLabels]

theorem characterEquiv_symm_comapMapLabels [CommSemiring R] (f : α → β)
    (χ : LForestAlgebra.Character β R) :
    ((characterEquiv (α := α) (R := R)).symm
        (LForestAlgebra.Character.comapMapLabels f χ)).1 =
      comapMapLabels f ((characterEquiv (α := β) (R := R)).symm χ).1 := by
  simpa [characterEquiv_symm_apply] using ofCharacter_comapMapLabels f χ

theorem characterEquiv_symm_comapConstLabel [CommSemiring R] (x : α)
    (χ : LForestAlgebra.Character α R) :
    ((Series.characterEquiv (R := R)).symm
        (LForestAlgebra.Character.comapConstLabel x χ)).1 =
      comapConstLabel x ((characterEquiv (α := α) (R := R)).symm χ).1 := by
  simpa [characterEquiv_symm_apply, Series.characterEquiv_symm_apply] using
    ofCharacter_comapConstLabel x χ

theorem characterEquiv_symm_comapEraseLabels [CommSemiring R]
    (χ : ForestAlgebra.Character R) :
    ((characterEquiv (α := α) (R := R)).symm
        (LForestAlgebra.Character.comapEraseLabels (α := α) χ)).1 =
      comapEraseLabels (α := α) ((Series.characterEquiv (R := R)).symm χ).1 := by
  simpa [characterEquiv_symm_apply, Series.characterEquiv_symm_apply] using
    ofCharacter_comapEraseLabels (α := α) χ

@[simp]
theorem comapEraseLabels_unit [Zero R] [One R] :
    comapEraseLabels (α := α) (Series.unit R) = unit α R := by
  funext τ
  cases τ <;> rfl

@[simp]
theorem comapEraseLabels_exact [DivisionSemiring R] :
    comapEraseLabels (α := α) (Series.exact R) = exact α R := by
  funext τ
  cases τ <;> simp [comapEraseLabels, exact, Series.exact]

@[simp]
theorem comapEraseLabels_scaledExact [DivisionSemiring R] (h : R) :
    comapEraseLabels (α := α) (Series.scaledExact h) = scaledExact α R h := by
  funext τ
  cases τ <;> simp [comapEraseLabels, scaledExact, Series.scaledExact]

theorem comapEraseLabels_comapMapLabels (f : α → β) (a : Series R) :
    comapMapLabels f (comapEraseLabels (α := β) a) =
      comapEraseLabels (α := α) a := by
  funext τ
  simp [comapMapLabels, comapEraseLabels]

theorem comapConstLabel_comapEraseLabels (x : α) (a : Series R) :
    comapConstLabel x (comapEraseLabels (α := α) a) = a := by
  funext τ
  simp [comapConstLabel, comapEraseLabels]

theorem comapConstLabel_comapMapLabels (f : α → β) (x : α) (a : LSeries β R) :
    comapConstLabel x (comapMapLabels f a) = comapConstLabel (f x) a := by
  funext τ
  simp [comapConstLabel, comapMapLabels]

theorem agreeUpToOrder_comapEraseLabels {a b : Series R} {n : Nat}
    (h : Series.AgreeUpToOrder a b n) :
    AgreeUpToOrder (comapEraseLabels (α := α) a) (comapEraseLabels (α := α) b) n := by
  intro τ hτ
  exact h (LTreeIndex.erase τ) (by simpa using hτ)

theorem agreeUpToOrder_of_comapEraseLabels {a b : Series R} {n : Nat}
    (x : α)
    (h : AgreeUpToOrder (comapEraseLabels (α := α) a) (comapEraseLabels (α := α) b) n) :
    Series.AgreeUpToOrder a b n := by
  intro τ hτ
  have hlabel := h (LTreeIndex.constLabel x τ) (by simpa using hτ)
  simpa [comapEraseLabels] using hlabel

theorem agreeUpToOrder_comapEraseLabels_iff [Nonempty α] {a b : Series R} {n : Nat} :
    AgreeUpToOrder (comapEraseLabels (α := α) a) (comapEraseLabels (α := α) b) n ↔
      Series.AgreeUpToOrder a b n := by
  constructor
  · intro h
    exact agreeUpToOrder_of_comapEraseLabels (Classical.choice (inferInstance : Nonempty α)) h
  · exact agreeUpToOrder_comapEraseLabels

theorem comapEraseLabels_hasOrder [DivisionSemiring R] {a : Series R} {n : Nat}
    (h : Series.HasOrder a n) : HasOrder (comapEraseLabels (α := α) a) n := by
  intro τ hτ
  simpa [comapEraseLabels, exact, Series.exact] using
    h (LTreeIndex.erase τ) (by simpa using hτ)

theorem hasOrder_of_comapEraseLabels [DivisionSemiring R] {a : Series R} {n : Nat}
    (x : α) (h : HasOrder (comapEraseLabels (α := α) a) n) : Series.HasOrder a n := by
  intro τ hτ
  have hlabel := h (LTreeIndex.constLabel x τ) (by simpa using hτ)
  simpa [comapEraseLabels, exact, Series.exact] using hlabel

theorem comapEraseLabels_hasOrder_iff [DivisionSemiring R] [Nonempty α]
    {a : Series R} {n : Nat} :
    HasOrder (comapEraseLabels (α := α) a) n ↔ Series.HasOrder a n := by
  constructor
  · intro h
    exact hasOrder_of_comapEraseLabels (Classical.choice (inferInstance : Nonempty α)) h
  · exact comapEraseLabels_hasOrder

theorem agreeUpToOrder_all_comapEraseLabels {a b : Series R}
    (h : ∀ n, Series.AgreeUpToOrder a b n) :
    ∀ n, AgreeUpToOrder (comapEraseLabels (α := α) a) (comapEraseLabels (α := α) b) n :=
  fun n => agreeUpToOrder_comapEraseLabels (h n)

theorem agreeUpToOrder_all_comapEraseLabels_iff [Nonempty α] {a b : Series R} :
    (∀ n, AgreeUpToOrder (comapEraseLabels (α := α) a) (comapEraseLabels (α := α) b) n) ↔
      ∀ n, Series.AgreeUpToOrder a b n := by
  constructor
  · intro h n
    exact (agreeUpToOrder_comapEraseLabels_iff (α := α) (n := n)).1 (h n)
  · intro h n
    exact agreeUpToOrder_comapEraseLabels (h n)

theorem comapEraseLabels_hasOrder_all [DivisionSemiring R] {a : Series R}
    (h : ∀ n, Series.HasOrder a n) :
    ∀ n, HasOrder (comapEraseLabels (α := α) a) n :=
  fun n => comapEraseLabels_hasOrder (h n)

theorem comapEraseLabels_hasOrder_all_iff [DivisionSemiring R] [Nonempty α]
    {a : Series R} :
    (∀ n, HasOrder (comapEraseLabels (α := α) a) n) ↔ ∀ n, Series.HasOrder a n := by
  constructor
  · intro h n
    exact (comapEraseLabels_hasOrder_iff (α := α) (n := n)).1 (h n)
  · intro h n
    exact comapEraseLabels_hasOrder (h n)

/-- A labelled B-series whose coefficients only depend on the unlabelled tree. -/
def LabelInvariant (a : LSeries α R) : Prop :=
  ∀ τ σ, LTreeIndex.erase τ = LTreeIndex.erase σ → coeff a τ = coeff a σ

theorem LabelInvariant.coeff_eq {a : LSeries α R} (h : LabelInvariant a)
    {τ σ : LTreeIndex α} (hτσ : LTreeIndex.erase τ = LTreeIndex.erase σ) :
    coeff a τ = coeff a σ :=
  h τ σ hτσ

theorem labelInvariant_comapEraseLabels (a : Series R) :
    LabelInvariant (comapEraseLabels (α := α) a) := by
  intro τ σ hτσ
  simpa [comapEraseLabels] using congrArg (fun ξ => Series.coeff a ξ) hτσ

theorem labelInvariant_unit [Zero R] [One R] :
    LabelInvariant (unit α R) := by
  intro τ σ hτσ
  cases τ <;> cases σ <;> simp [unit] at hτσ ⊢

theorem labelInvariant_exact [DivisionSemiring R] :
    LabelInvariant (exact α R) := by
  intro τ σ hτσ
  have hfac : LTreeIndex.treeFactorial τ = LTreeIndex.treeFactorial σ := by
    have h := congrArg TreeIndex.treeFactorial hτσ
    simpa using h
  simpa [exact] using congrArg (fun n : Nat => ((n : R)⁻¹)) hfac

theorem labelInvariant_scaledExact [DivisionSemiring R] (h : R) :
    LabelInvariant (scaledExact α R h) := by
  intro τ σ hτσ
  have horder : LTreeIndex.order τ = LTreeIndex.order σ := by
    have h' := congrArg TreeIndex.order hτσ
    simpa using h'
  have hfac : LTreeIndex.treeFactorial τ = LTreeIndex.treeFactorial σ := by
    have h' := congrArg TreeIndex.treeFactorial hτσ
    simpa using h'
  simp [scaledExact, horder, hfac]

theorem labelInvariant_zero [Zero R] :
    LabelInvariant (0 : LSeries α R) := by
  intro τ σ hτσ
  rfl

theorem LabelInvariant.add [Add R] {a b : LSeries α R}
    (ha : LabelInvariant a) (hb : LabelInvariant b) : LabelInvariant (a + b) := by
  intro τ σ hτσ
  change a τ + b τ = a σ + b σ
  rw [show a τ = a σ by simpa [coeff] using ha.coeff_eq hτσ]
  rw [show b τ = b σ by simpa [coeff] using hb.coeff_eq hτσ]

theorem LabelInvariant.neg [Neg R] {a : LSeries α R}
    (ha : LabelInvariant a) : LabelInvariant (-a) := by
  intro τ σ hτσ
  change -a τ = -a σ
  rw [show a τ = a σ by simpa [coeff] using ha.coeff_eq hτσ]

theorem LabelInvariant.sub [Sub R] {a b : LSeries α R}
    (ha : LabelInvariant a) (hb : LabelInvariant b) : LabelInvariant (a - b) := by
  intro τ σ hτσ
  change a τ - b τ = a σ - b σ
  rw [show a τ = a σ by simpa [coeff] using ha.coeff_eq hτσ]
  rw [show b τ = b σ by simpa [coeff] using hb.coeff_eq hτσ]

theorem LabelInvariant.smul [SMul S R] {a : LSeries α R}
    (c : S) (ha : LabelInvariant a) : LabelInvariant (c • a) := by
  intro τ σ hτσ
  change c • a τ = c • a σ
  rw [show a τ = a σ by simpa [coeff] using ha.coeff_eq hτσ]

theorem LabelInvariant.comapMapLabels {a : LSeries β R} (h : LabelInvariant a)
    (f : α → β) : LabelInvariant (comapMapLabels f a) := by
  intro τ σ hτσ
  exact h (LTreeIndex.mapLabels f τ) (LTreeIndex.mapLabels f σ) (by simpa using hτσ)

theorem LabelInvariant.comapConstLabel_eq {a : LSeries α R} (h : LabelInvariant a)
    (x y : α) : comapConstLabel x a = comapConstLabel y a := by
  funext τ
  exact h (LTreeIndex.constLabel x τ) (LTreeIndex.constLabel y τ) (by simp)

theorem LabelInvariant.comapEraseLabels_comapConstLabel {a : LSeries α R}
    (h : LabelInvariant a) (x : α) :
    comapEraseLabels (α := α) (comapConstLabel x a) = a := by
  funext τ
  change coeff a (LTreeIndex.constLabel x (LTreeIndex.erase τ)) = a τ
  simpa [coeff] using
    h (LTreeIndex.constLabel x (LTreeIndex.erase τ)) τ (by simp)

/-- Unlabelled series are equivalent to labelled series whose coefficients ignore labels. -/
noncomputable def labelInvariantEquiv [Nonempty α] :
    Series R ≃ {a : LSeries α R // LabelInvariant a} where
  toFun a := ⟨comapEraseLabels (α := α) a, labelInvariant_comapEraseLabels a⟩
  invFun a := comapConstLabel (Classical.choice (inferInstance : Nonempty α)) a.1
  left_inv a := by
    exact comapConstLabel_comapEraseLabels (Classical.choice (inferInstance : Nonempty α)) a
  right_inv a := by
    cases a with
    | mk a ha =>
        apply Subtype.ext
        exact ha.comapEraseLabels_comapConstLabel
          (Classical.choice (inferInstance : Nonempty α))

@[simp]
theorem labelInvariantEquiv_apply [Nonempty α] (a : Series R) :
    (labelInvariantEquiv (α := α) a).1 = comapEraseLabels (α := α) a :=
  rfl

@[simp]
theorem labelInvariantEquiv_symm_apply [Nonempty α]
    (a : {a : LSeries α R // LabelInvariant a}) :
    (labelInvariantEquiv (α := α) (R := R)).symm a =
      comapConstLabel (Classical.choice (inferInstance : Nonempty α)) a.1 :=
  rfl

theorem labelInvariantEquiv_unit [Zero R] [One R] [Nonempty α] :
    labelInvariantEquiv (α := α) (R := R) (Series.unit R) =
      ⟨unit α R, labelInvariant_unit⟩ := by
  apply Subtype.ext
  exact comapEraseLabels_unit (α := α) (R := R)

theorem labelInvariantEquiv_symm_unit [Zero R] [One R] [Nonempty α] :
    (labelInvariantEquiv (α := α) (R := R)).symm
        ⟨unit α R, labelInvariant_unit⟩ =
      Series.unit R := by
  exact comapConstLabel_unit (Classical.choice (inferInstance : Nonempty α))

theorem labelInvariant_iff_exists_comapEraseLabels [Nonempty α] (a : LSeries α R) :
    LabelInvariant a ↔ ∃ b : Series R, comapEraseLabels (α := α) b = a := by
  constructor
  · intro h
    let x := Classical.choice (inferInstance : Nonempty α)
    exact ⟨comapConstLabel x a, h.comapEraseLabels_comapConstLabel x⟩
  · rintro ⟨b, rfl⟩
    exact labelInvariant_comapEraseLabels (α := α) b

theorem labelInvariantEquiv_hasUnitConstant [One R] [Nonempty α] {a : Series R} :
    HasUnitConstant (labelInvariantEquiv (α := α) a).1 ↔ Series.HasUnitConstant a := by
  simp [labelInvariantEquiv_apply, HasUnitConstant, Series.HasUnitConstant, constantCoeff,
    Series.constantCoeff, comapEraseLabels]

theorem labelInvariantEquiv_symm_hasUnitConstant [One R] [Nonempty α]
    {a : {a : LSeries α R // LabelInvariant a}} :
    Series.HasUnitConstant ((labelInvariantEquiv (α := α) (R := R)).symm a) ↔
      HasUnitConstant a.1 := by
  simp [labelInvariantEquiv_symm_apply, Series.HasUnitConstant, HasUnitConstant,
    Series.constantCoeff, constantCoeff, comapConstLabel]

/-- Unit-constant unlabelled series are equivalent to unit-constant label-invariant series. -/
noncomputable def labelInvariantUnitEquiv [One R] [Nonempty α] :
    {a : Series R // Series.HasUnitConstant a} ≃
      {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a} where
  toFun a :=
    ⟨comapEraseLabels (α := α) a.1,
      ⟨hasUnitConstant_comapEraseLabels (α := α) a.2,
        labelInvariant_comapEraseLabels (α := α) a.1⟩⟩
  invFun a :=
    ⟨comapConstLabel (Classical.choice (inferInstance : Nonempty α)) a.1,
      hasUnitConstant_comapConstLabel
        (Classical.choice (inferInstance : Nonempty α)) a.2.1⟩
  left_inv a := by
    apply Subtype.ext
    exact comapConstLabel_comapEraseLabels
      (Classical.choice (inferInstance : Nonempty α)) a.1
  right_inv a := by
    apply Subtype.ext
    exact a.2.2.comapEraseLabels_comapConstLabel
      (Classical.choice (inferInstance : Nonempty α))

@[simp]
theorem labelInvariantUnitEquiv_apply [One R] [Nonempty α]
    (a : {a : Series R // Series.HasUnitConstant a}) :
    (labelInvariantUnitEquiv (α := α) a).1 = comapEraseLabels (α := α) a.1 :=
  rfl

@[simp]
theorem labelInvariantUnitEquiv_symm_apply [One R] [Nonempty α]
    (a : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}) :
    ((labelInvariantUnitEquiv (α := α) (R := R)).symm a).1 =
      comapConstLabel (Classical.choice (inferInstance : Nonempty α)) a.1 :=
  rfl

theorem labelInvariantUnitEquiv_unit [Zero R] [One R] [Nonempty α] :
    labelInvariantUnitEquiv (α := α) (R := R)
        ⟨Series.unit R, Series.unit_hasUnitConstant⟩ =
      ⟨unit α R, unit_hasUnitConstant, labelInvariant_unit⟩ := by
  apply Subtype.ext
  exact comapEraseLabels_unit (α := α) (R := R)

theorem labelInvariantUnitEquiv_symm_unit [Zero R] [One R] [Nonempty α] :
    ((labelInvariantUnitEquiv (α := α) (R := R)).symm
        ⟨unit α R, unit_hasUnitConstant, labelInvariant_unit⟩).1 =
      Series.unit R := by
  exact comapConstLabel_unit (Classical.choice (inferInstance : Nonempty α))

theorem LabelInvariant.toCharacter [CommSemiring R] [Nonempty α] {a : LSeries α R}
    (h : LabelInvariant a) :
    LForestAlgebra.Character.LabelInvariant (toCharacter a) := by
  rcases (labelInvariant_iff_exists_comapEraseLabels (α := α) a).1 h with ⟨b, hb⟩
  rw [← hb, toCharacter_comapEraseLabels]
  exact LForestAlgebra.Character.labelInvariant_comapEraseLabels
    (α := α) (Series.toCharacter b)

theorem labelInvariant_of_toCharacter [CommSemiring R] {a : LSeries α R}
    (h : LForestAlgebra.Character.LabelInvariant (toCharacter a)) : LabelInvariant a := by
  intro τ σ hτσ
  cases τ with
  | empty =>
      cases σ with
      | empty => rfl
      | tree σ => cases hτσ
  | tree τ =>
      cases σ with
      | empty => cases hτσ
      | tree σ =>
          have herase : LRootedTree.erase τ = LRootedTree.erase σ := by
            simpa using hτσ
          have hforest :
              (toCharacter a).evalForest (LRootedForest.singleton τ) =
                (toCharacter a).evalForest (LRootedForest.singleton σ) := by
            exact h (LRootedForest.singleton τ) (LRootedForest.singleton σ) (by
              simp [LRootedForest.erase_singleton, herase])
          simpa [toCharacter_evalForest, forestCoeff_singleton] using hforest

theorem labelInvariant_iff_toCharacter_labelInvariant [CommSemiring R] [Nonempty α]
    {a : LSeries α R} :
    LabelInvariant a ↔ LForestAlgebra.Character.LabelInvariant (toCharacter a) := by
  constructor
  · exact LabelInvariant.toCharacter
  · exact labelInvariant_of_toCharacter

theorem characterEquiv_labelInvariant_iff [CommSemiring R] [Nonempty α]
    (a : {a : LSeries α R // HasUnitConstant a}) :
    LForestAlgebra.Character.LabelInvariant (characterEquiv a) ↔ LabelInvariant a.1 := by
  rw [labelInvariant_iff_toCharacter_labelInvariant]
  simp [characterEquiv_apply]

/-- Unit-constant label-invariant series are equivalent to label-invariant characters. -/
noncomputable def labelInvariantCharacterEquiv [CommSemiring R] [Nonempty α] :
    {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a} ≃
      {χ : LForestAlgebra.Character α R // LForestAlgebra.Character.LabelInvariant χ} where
  toFun a :=
    ⟨characterEquiv ⟨a.1, a.2.1⟩,
      (characterEquiv_labelInvariant_iff ⟨a.1, a.2.1⟩).2 a.2.2⟩
  invFun χ :=
    let a := (characterEquiv (α := α) (R := R)).symm χ.1
    ⟨a.1, ⟨a.2, by
      have ha_eq : characterEquiv a = χ.1 := by
        exact (characterEquiv (α := α) (R := R)).right_inv χ.1
      have hχ : LForestAlgebra.Character.LabelInvariant (characterEquiv a) := by
        rw [ha_eq]
        exact χ.2
      exact (characterEquiv_labelInvariant_iff a).1 hχ⟩⟩
  left_inv a := by
    apply Subtype.ext
    simpa [characterEquiv_apply, characterEquiv_symm_apply] using
      ofCharacter_toCharacter a.2.1
  right_inv χ := by
    apply Subtype.ext
    simp

@[simp]
theorem labelInvariantCharacterEquiv_apply [CommSemiring R] [Nonempty α]
    (a : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}) :
    (labelInvariantCharacterEquiv (α := α) (R := R) a).1 =
      characterEquiv ⟨a.1, a.2.1⟩ :=
  rfl

@[simp]
theorem labelInvariantCharacterEquiv_symm_apply [CommSemiring R] [Nonempty α]
    (χ : {χ : LForestAlgebra.Character α R // LForestAlgebra.Character.LabelInvariant χ}) :
    ((labelInvariantCharacterEquiv (α := α) (R := R)).symm χ).1 =
      ((characterEquiv (α := α) (R := R)).symm χ.1).1 :=
  rfl

theorem labelInvariantCharacterEquiv_labelInvariantUnitEquiv [CommSemiring R] [Nonempty α]
    (a : {a : Series R // Series.HasUnitConstant a}) :
    labelInvariantCharacterEquiv (α := α) (R := R)
        (labelInvariantUnitEquiv (α := α) (R := R) a) =
      LForestAlgebra.Character.labelInvariantEquiv (α := α) (R := R)
        (Series.characterEquiv a) := by
  apply Subtype.ext
  simpa [labelInvariantUnitEquiv_apply] using characterEquiv_comapEraseLabels (α := α) a

theorem labelInvariantCharacterEquiv_unit [CommSemiring R] [Nonempty α] :
    labelInvariantCharacterEquiv (α := α) (R := R)
        ⟨unit α R, unit_hasUnitConstant, labelInvariant_unit⟩ =
      LForestAlgebra.Character.labelInvariantEquiv (α := α) (R := R)
        (Series.characterEquiv ⟨Series.unit R, Series.unit_hasUnitConstant⟩) := by
  rw [← labelInvariantUnitEquiv_unit (α := α) (R := R)]
  exact labelInvariantCharacterEquiv_labelInvariantUnitEquiv
    (α := α) (R := R) ⟨Series.unit R, Series.unit_hasUnitConstant⟩

theorem labelInvariantUnitEquiv_exact [DivisionSemiring R] [Nonempty α] :
    labelInvariantUnitEquiv (α := α) (R := R)
        ⟨Series.exact R, Series.exact_hasUnitConstant⟩ =
      ⟨exact α R, exact_hasUnitConstant, labelInvariant_exact⟩ := by
  apply Subtype.ext
  exact comapEraseLabels_exact (α := α) (R := R)

theorem labelInvariantUnitEquiv_scaledExact [DivisionSemiring R] [Nonempty α] (h : R) :
    labelInvariantUnitEquiv (α := α) (R := R)
        ⟨Series.scaledExact h, Series.scaledExact_hasUnitConstant h⟩ =
      ⟨scaledExact α R h, scaledExact_hasUnitConstant h, labelInvariant_scaledExact h⟩ := by
  apply Subtype.ext
  exact comapEraseLabels_scaledExact (α := α) h

theorem labelInvariantUnitEquiv_symm_exact [DivisionSemiring R] [Nonempty α] :
    ((labelInvariantUnitEquiv (α := α) (R := R)).symm
        ⟨exact α R, exact_hasUnitConstant, labelInvariant_exact⟩).1 =
      Series.exact R := by
  exact comapConstLabel_exact (Classical.choice (inferInstance : Nonempty α))

theorem labelInvariantUnitEquiv_symm_scaledExact [DivisionSemiring R] [Nonempty α]
    (h : R) :
    ((labelInvariantUnitEquiv (α := α) (R := R)).symm
        ⟨scaledExact α R h, scaledExact_hasUnitConstant h,
          labelInvariant_scaledExact h⟩).1 =
      Series.scaledExact h := by
  exact comapConstLabel_scaledExact (Classical.choice (inferInstance : Nonempty α)) h

theorem labelInvariantUnitEquiv_hasOrder [DivisionSemiring R] [Nonempty α]
    {a : {a : Series R // Series.HasUnitConstant a}} {n : Nat} :
    HasOrder (labelInvariantUnitEquiv (α := α) (R := R) a).1 n ↔
      Series.HasOrder a.1 n := by
  simpa [labelInvariantUnitEquiv_apply] using
    (comapEraseLabels_hasOrder_iff (α := α) (a := a.1) (n := n))

theorem labelInvariantUnitEquiv_hasOrder_all [DivisionSemiring R] [Nonempty α]
    {a : {a : Series R // Series.HasUnitConstant a}} :
    (∀ n, HasOrder (labelInvariantUnitEquiv (α := α) (R := R) a).1 n) ↔
      ∀ n, Series.HasOrder a.1 n := by
  simpa [labelInvariantUnitEquiv_apply] using
    (comapEraseLabels_hasOrder_all_iff (α := α) (a := a.1))

theorem labelInvariantCharacterEquiv_exact [Field R] [Nonempty α] :
    labelInvariantCharacterEquiv (α := α) (R := R)
        ⟨exact α R, exact_hasUnitConstant, labelInvariant_exact⟩ =
      LForestAlgebra.Character.labelInvariantEquiv (α := α) (R := R)
        (Series.characterEquiv ⟨Series.exact R, Series.exact_hasUnitConstant⟩) := by
  rw [← labelInvariantUnitEquiv_exact (α := α) (R := R)]
  exact labelInvariantCharacterEquiv_labelInvariantUnitEquiv
    (α := α) (R := R) ⟨Series.exact R, Series.exact_hasUnitConstant⟩

theorem labelInvariantCharacterEquiv_scaledExact [Field R] [Nonempty α] (h : R) :
    labelInvariantCharacterEquiv (α := α) (R := R)
        ⟨scaledExact α R h, scaledExact_hasUnitConstant h,
          labelInvariant_scaledExact h⟩ =
      LForestAlgebra.Character.labelInvariantEquiv (α := α) (R := R)
        (Series.characterEquiv
          ⟨Series.scaledExact h, Series.scaledExact_hasUnitConstant h⟩) := by
  rw [← labelInvariantUnitEquiv_scaledExact (α := α) (R := R) h]
  exact labelInvariantCharacterEquiv_labelInvariantUnitEquiv
    (α := α) (R := R)
    ⟨Series.scaledExact h, Series.scaledExact_hasUnitConstant h⟩

theorem labelInvariantCharacterEquiv_hasOrder_all_iff_exact [Field R] [Nonempty α]
    (a : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}) :
    (∀ n, HasOrder a.1 n) ↔
      labelInvariantCharacterEquiv (α := α) (R := R) a =
        labelInvariantCharacterEquiv (α := α) (R := R)
          ⟨exact α R, exact_hasUnitConstant, labelInvariant_exact⟩ := by
  constructor
  · intro h
    apply congrArg (labelInvariantCharacterEquiv (α := α) (R := R))
    apply Subtype.ext
    exact (hasOrder_all_iff_eq_exact).1 h
  · intro h
    have hchar :
        characterEquiv ⟨a.1, a.2.1⟩ =
          characterEquiv ⟨exact α R, exact_hasUnitConstant⟩ := by
      simpa [labelInvariantCharacterEquiv_apply] using congrArg Subtype.val h
    exact (characterEquiv_hasOrder_all_iff_exact ⟨a.1, a.2.1⟩).2 hchar

theorem LabelInvariant.agreeUpToOrder_iff_comapConstLabel
    {a b : LSeries α R} {n : Nat} (ha : LabelInvariant a)
    (hb : LabelInvariant b) (x : α) :
    AgreeUpToOrder a b n ↔
      Series.AgreeUpToOrder (comapConstLabel x a) (comapConstLabel x b) n := by
  constructor
  · exact agreeUpToOrder_comapConstLabel x
  · intro h τ hτ
    have hconst := h (LTreeIndex.erase τ) (by simpa using hτ)
    calc
      coeff a τ = coeff a (LTreeIndex.constLabel x (LTreeIndex.erase τ)) := by
        exact (ha.coeff_eq (by simp)).symm
      _ = coeff b (LTreeIndex.constLabel x (LTreeIndex.erase τ)) := by
        simpa [comapConstLabel] using hconst
      _ = coeff b τ := by
        exact hb.coeff_eq (by simp)

theorem LabelInvariant.hasOrder_iff_comapConstLabel [DivisionSemiring R]
    {a : LSeries α R} {n : Nat} (ha : LabelInvariant a) (x : α) :
    HasOrder a n ↔ Series.HasOrder (comapConstLabel x a) n := by
  constructor
  · exact comapConstLabel_hasOrder x
  · intro h τ hτ
    have hconst := h (LTreeIndex.erase τ) (by simpa using hτ)
    calc
      coeff a τ = coeff a (LTreeIndex.constLabel x (LTreeIndex.erase τ)) := by
        exact (ha.coeff_eq (by simp)).symm
      _ = (TreeIndex.treeFactorial (LTreeIndex.erase τ) : R)⁻¹ := by
        simpa [comapConstLabel, Series.exact] using hconst
      _ = (LTreeIndex.treeFactorial τ : R)⁻¹ := by
        simp

theorem LabelInvariant.agreeUpToOrder_all_iff_comapConstLabel
    {a b : LSeries α R} (ha : LabelInvariant a)
    (hb : LabelInvariant b) (x : α) :
    (∀ n, AgreeUpToOrder a b n) ↔
      ∀ n, Series.AgreeUpToOrder (comapConstLabel x a) (comapConstLabel x b) n := by
  constructor
  · intro h n
    exact agreeUpToOrder_comapConstLabel x (h n)
  · intro h n
    exact (ha.agreeUpToOrder_iff_comapConstLabel hb x).2 (h n)

theorem LabelInvariant.hasOrder_all_iff_comapConstLabel [DivisionSemiring R]
    {a : LSeries α R} (ha : LabelInvariant a) (x : α) :
    (∀ n, HasOrder a n) ↔ ∀ n, Series.HasOrder (comapConstLabel x a) n := by
  constructor
  · intro h n
    exact comapConstLabel_hasOrder x (h n)
  · intro h n
    exact (ha.hasOrder_iff_comapConstLabel x).2 (h n)

theorem labelInvariantUnitEquiv_agreeUpToOrder [One R] [Nonempty α]
    {a b : {a : Series R // Series.HasUnitConstant a}} {n : Nat} :
    AgreeUpToOrder (labelInvariantUnitEquiv (α := α) (R := R) a).1
        (labelInvariantUnitEquiv (α := α) (R := R) b).1 n ↔
      Series.AgreeUpToOrder a.1 b.1 n := by
  simpa [labelInvariantUnitEquiv_apply] using
    (agreeUpToOrder_comapEraseLabels_iff (α := α) (a := a.1) (b := b.1) (n := n))

theorem labelInvariantUnitEquiv_symm_agreeUpToOrder [One R] [Nonempty α]
    {a b : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}} {n : Nat} :
    Series.AgreeUpToOrder ((labelInvariantUnitEquiv (α := α) (R := R)).symm a).1
        ((labelInvariantUnitEquiv (α := α) (R := R)).symm b).1 n ↔
      AgreeUpToOrder a.1 b.1 n := by
  rw [labelInvariantUnitEquiv_symm_apply, labelInvariantUnitEquiv_symm_apply]
  exact (a.2.2.agreeUpToOrder_iff_comapConstLabel b.2.2
    (Classical.choice (inferInstance : Nonempty α))).symm

theorem labelInvariantUnitEquiv_symm_hasOrder [DivisionSemiring R] [Nonempty α]
    {a : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}} {n : Nat} :
    Series.HasOrder ((labelInvariantUnitEquiv (α := α) (R := R)).symm a).1 n ↔
      HasOrder a.1 n := by
  rw [labelInvariantUnitEquiv_symm_apply]
  exact (a.2.2.hasOrder_iff_comapConstLabel
    (Classical.choice (inferInstance : Nonempty α))).symm

theorem labelInvariantUnitEquiv_agreeUpToOrder_all [One R] [Nonempty α]
    {a b : {a : Series R // Series.HasUnitConstant a}} :
    (∀ n, AgreeUpToOrder (labelInvariantUnitEquiv (α := α) (R := R) a).1
        (labelInvariantUnitEquiv (α := α) (R := R) b).1 n) ↔
      ∀ n, Series.AgreeUpToOrder a.1 b.1 n := by
  constructor
  · intro h n
    exact (labelInvariantUnitEquiv_agreeUpToOrder
      (α := α) (a := a) (b := b) (n := n)).1 (h n)
  · intro h n
    exact (labelInvariantUnitEquiv_agreeUpToOrder
      (α := α) (a := a) (b := b) (n := n)).2 (h n)

theorem labelInvariantUnitEquiv_symm_agreeUpToOrder_all [One R] [Nonempty α]
    {a b : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}} :
    (∀ n, Series.AgreeUpToOrder
        ((labelInvariantUnitEquiv (α := α) (R := R)).symm a).1
        ((labelInvariantUnitEquiv (α := α) (R := R)).symm b).1 n) ↔
      ∀ n, AgreeUpToOrder a.1 b.1 n := by
  constructor
  · intro h n
    exact (labelInvariantUnitEquiv_symm_agreeUpToOrder
      (α := α) (a := a) (b := b) (n := n)).1 (h n)
  · intro h n
    exact (labelInvariantUnitEquiv_symm_agreeUpToOrder
      (α := α) (a := a) (b := b) (n := n)).2 (h n)

theorem labelInvariantUnitEquiv_symm_hasOrder_all [DivisionSemiring R] [Nonempty α]
    {a : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}} :
    (∀ n, Series.HasOrder ((labelInvariantUnitEquiv (α := α) (R := R)).symm a).1 n) ↔
      ∀ n, HasOrder a.1 n := by
  constructor
  · intro h n
    exact (labelInvariantUnitEquiv_symm_hasOrder (α := α) (a := a) (n := n)).1 (h n)
  · intro h n
    exact (labelInvariantUnitEquiv_symm_hasOrder (α := α) (a := a) (n := n)).2 (h n)

theorem labelInvariantEquiv_agreeUpToOrder [Nonempty α]
    {a b : Series R} {n : Nat} :
    AgreeUpToOrder (labelInvariantEquiv (α := α) a).1
        (labelInvariantEquiv (α := α) b).1 n ↔
      Series.AgreeUpToOrder a b n := by
  simpa using
    (agreeUpToOrder_comapEraseLabels_iff (α := α) (a := a) (b := b) (n := n))

theorem labelInvariantEquiv_symm_agreeUpToOrder [Nonempty α]
    {a b : {a : LSeries α R // LabelInvariant a}} {n : Nat} :
    Series.AgreeUpToOrder ((labelInvariantEquiv (α := α) (R := R)).symm a)
        ((labelInvariantEquiv (α := α) (R := R)).symm b) n ↔
      AgreeUpToOrder a.1 b.1 n := by
  rw [labelInvariantEquiv_symm_apply, labelInvariantEquiv_symm_apply]
  exact (a.2.agreeUpToOrder_iff_comapConstLabel b.2
    (Classical.choice (inferInstance : Nonempty α))).symm

theorem labelInvariantEquiv_hasOrder [DivisionSemiring R] [Nonempty α]
    {a : Series R} {n : Nat} :
    HasOrder (labelInvariantEquiv (α := α) a).1 n ↔ Series.HasOrder a n := by
  simpa using
    (comapEraseLabels_hasOrder_iff (α := α) (a := a) (n := n))

theorem labelInvariantEquiv_symm_hasOrder [DivisionSemiring R] [Nonempty α]
    {a : {a : LSeries α R // LabelInvariant a}} {n : Nat} :
    Series.HasOrder ((labelInvariantEquiv (α := α) (R := R)).symm a) n ↔
      HasOrder a.1 n := by
  rw [labelInvariantEquiv_symm_apply]
  exact (a.2.hasOrder_iff_comapConstLabel
    (Classical.choice (inferInstance : Nonempty α))).symm

theorem labelInvariantEquiv_agreeUpToOrder_all [Nonempty α]
    {a b : Series R} :
    (∀ n, AgreeUpToOrder (labelInvariantEquiv (α := α) a).1
        (labelInvariantEquiv (α := α) b).1 n) ↔
      ∀ n, Series.AgreeUpToOrder a b n := by
  constructor
  · intro h n
    exact (labelInvariantEquiv_agreeUpToOrder (α := α) (a := a) (b := b) (n := n)).1
      (h n)
  · intro h n
    exact (labelInvariantEquiv_agreeUpToOrder (α := α) (a := a) (b := b) (n := n)).2
      (h n)

theorem labelInvariantEquiv_symm_agreeUpToOrder_all [Nonempty α]
    {a b : {a : LSeries α R // LabelInvariant a}} :
    (∀ n, Series.AgreeUpToOrder ((labelInvariantEquiv (α := α) (R := R)).symm a)
        ((labelInvariantEquiv (α := α) (R := R)).symm b) n) ↔
      ∀ n, AgreeUpToOrder a.1 b.1 n := by
  constructor
  · intro h n
    exact (labelInvariantEquiv_symm_agreeUpToOrder
      (α := α) (a := a) (b := b) (n := n)).1 (h n)
  · intro h n
    exact (labelInvariantEquiv_symm_agreeUpToOrder
      (α := α) (a := a) (b := b) (n := n)).2 (h n)

theorem labelInvariantEquiv_hasOrder_all [DivisionSemiring R] [Nonempty α]
    {a : Series R} :
    (∀ n, HasOrder (labelInvariantEquiv (α := α) a).1 n) ↔
      ∀ n, Series.HasOrder a n := by
  constructor
  · intro h n
    exact (labelInvariantEquiv_hasOrder (α := α) (a := a) (n := n)).1 (h n)
  · intro h n
    exact (labelInvariantEquiv_hasOrder (α := α) (a := a) (n := n)).2 (h n)

theorem labelInvariantEquiv_symm_hasOrder_all [DivisionSemiring R] [Nonempty α]
    {a : {a : LSeries α R // LabelInvariant a}} :
    (∀ n, Series.HasOrder ((labelInvariantEquiv (α := α) (R := R)).symm a) n) ↔
      ∀ n, HasOrder a.1 n := by
  constructor
  · intro h n
    exact (labelInvariantEquiv_symm_hasOrder (α := α) (a := a) (n := n)).1 (h n)
  · intro h n
    exact (labelInvariantEquiv_symm_hasOrder (α := α) (a := a) (n := n)).2 (h n)

end LSeries

end BSeries
