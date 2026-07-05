/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.LabelledCharacterConvolution
import BSeries.Series.Convolution
import BSeries.Series.Labelled

/-!
# Convolution of Labelled B-Series

The convolution of labelled B-series coefficient families, expressed
through the labelled character convolution, with order-truncation
congruence lemmas.
-/

namespace BSeries

open HopfAlgebras

universe u v w

namespace PLTree

open HopfAlgebras.PLTree

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

theorem evalCoproductTerm_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : LSeries.AgreeUpToOrder a a' n) (hb : LSeries.AgreeUpToOrder b b' n)
    (term : LRootedForest α × LRootedForest α)
    (hterm : LRootedForest.order term.1 + LRootedForest.order term.2 ≤ n) :
    evalCoproductTerm (LSeries.toCharacter a) (LSeries.toCharacter b) term =
      evalCoproductTerm (LSeries.toCharacter a') (LSeries.toCharacter b') term := by
  have hleft : LRootedForest.order term.1 ≤ n := by omega
  have hright : LRootedForest.order term.2 ≤ n := by omega
  simp [
    evalCoproductTerm,
    LForestAlgebra.Character.evalForest,
    LSeries.AgreeUpToOrder.forestCoeff ha hleft,
    LSeries.AgreeUpToOrder.forestCoeff hb hright
  ]

theorem evalCoproductTerms_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : LSeries.AgreeUpToOrder a a' n) (hb : LSeries.AgreeUpToOrder b b' n)
    {terms : List (LRootedForest α × LRootedForest α)}
    (hterms : ∀ term ∈ terms,
      LRootedForest.order term.1 + LRootedForest.order term.2 ≤ n) :
    evalCoproductTerms (LSeries.toCharacter a) (LSeries.toCharacter b) terms =
      evalCoproductTerms (LSeries.toCharacter a') (LSeries.toCharacter b') terms := by
  induction terms with
  | nil =>
      rw [evalCoproductTerms_nil, evalCoproductTerms_nil]
  | cons term terms ih =>
      have hterm : LRootedForest.order term.1 + LRootedForest.order term.2 ≤ n :=
        hterms term (by simp)
      have htail :
          ∀ term ∈ terms, LRootedForest.order term.1 + LRootedForest.order term.2 ≤ n := by
        intro term hmem
        exact hterms term (by simp [hmem])
      rw [
        evalCoproductTerms_cons,
        evalCoproductTerms_cons,
        evalCoproductTerm_congr_of_agree ha hb term hterm,
        ih htail
      ]

theorem convolutionCoeff_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : LSeries.AgreeUpToOrder a a' n) (hb : LSeries.AgreeUpToOrder b b' n)
    {t : PLTree α} (ht : PLTree.order t ≤ n) :
    convolutionCoeff (LSeries.toCharacter a) (LSeries.toCharacter b) t =
      convolutionCoeff (LSeries.toCharacter a') (LSeries.toCharacter b') t := by
  unfold convolutionCoeff
  exact evalCoproductTerms_congr_of_agree ha hb (fun term hterm => by
    rw [coproductTerms_order hterm]
    exact ht)

theorem convolutionForestCoeff_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : LSeries.AgreeUpToOrder a a' n) (hb : LSeries.AgreeUpToOrder b b' n)
    {ts : List (PLTree α)} (hts : PLTree.orderList ts ≤ n) :
    convolutionForestCoeff (LSeries.toCharacter a) (LSeries.toCharacter b) ts =
      convolutionForestCoeff (LSeries.toCharacter a') (LSeries.toCharacter b') ts := by
  unfold convolutionForestCoeff
  exact evalCoproductTerms_congr_of_agree ha hb (fun term hterm => by
    rw [coproductTermsList_order hterm]
    exact hts)


end

end PLTree

namespace LRootedForest

open HopfAlgebras.LRootedForest

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

private theorem order_out (τ : LRootedTree α) :
    PLTree.order (Quotient.out τ) = LRootedTree.order τ := by
  rw [← LRootedTree.order_ofPLTree (Quotient.out τ)]
  rw [show LRootedTree.ofPLTree (Quotient.out τ) = τ from Quotient.out_eq τ]

private theorem orderList_out :
    ∀ ts : List (LRootedTree α),
      PLTree.orderList (ts.map Quotient.out) = LRootedForest.order (ts : LRootedForest α)
  | [] => rfl
  | τ :: ts => by
      simp [LRootedForest.order, order_out τ, orderList_out ts]


theorem convolutionCoeff_toCharacter_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : LSeries.AgreeUpToOrder a a' n) (hb : LSeries.AgreeUpToOrder b b' n)
    {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    convolutionCoeff (LSeries.toCharacter a) (LSeries.toCharacter b) φ =
      convolutionCoeff (LSeries.toCharacter a') (LSeries.toCharacter b') φ := by
  suffices hforest :
      ∀ φ : LRootedForest α, LRootedForest.order φ ≤ n →
        convolutionCoeff (LSeries.toCharacter a) (LSeries.toCharacter b) φ =
          convolutionCoeff (LSeries.toCharacter a') (LSeries.toCharacter b') φ from
    hforest φ hφ
  intro φ
  refine Quotient.inductionOn φ ?_
  intro ts hts
  rw [convolutionCoeff, convolutionCoeff]
  change
    LForestTensorAlgebra.evalByCharacters (LSeries.toCharacter a) (LSeries.toCharacter b)
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out)) =
      LForestTensorAlgebra.evalByCharacters (LSeries.toCharacter a') (LSeries.toCharacter b')
        (PLTree.labelledCoproductList (R := R) (ts.map Quotient.out))
  rw [LForestTensorAlgebra.evalByCharacters_labelledCoproductList,
    LForestTensorAlgebra.evalByCharacters_labelledCoproductList]
  exact PLTree.convolutionForestCoeff_congr_of_agree ha hb (by
    rw [orderList_out]
    exact hts)


end

end LRootedForest

namespace LSeries

noncomputable section

variable {α : Type u} {R : Type v} [CommSemiring R]

/-- Planar labelled convolution coefficient obtained from the cut coproduct. -/
def planarConvolutionCoeff (a b : LSeries α R) (t : PLTree α) : R :=
  PLTree.convolutionCoeff (toCharacter a) (toCharacter b) t

theorem planarConvolutionCoeff_eq_of_cuts_listRelPerm
    (a b : LSeries α R) {t u : PLTree α}
    (h : PTree.ListRelPerm PLTree.Cut.Perm (PLTree.cuts t) (PLTree.cuts u)) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a b u :=
  PLTree.convolutionCoeff_eq_of_cuts_listRelPerm (toCharacter a) (toCharacter b) h

theorem planarConvolutionCoeff_eq_of_rootCuts_listRelPerm
    (a b : LSeries α R) {t u : PLTree α} (htu : PLTree.Perm t u)
    (hroot : PTree.ListRelPerm PLTree.RootCut.Perm (PLTree.rootCuts t) (PLTree.rootCuts u)) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a b u :=
  PLTree.convolutionCoeff_eq_of_rootCuts_listRelPerm (toCharacter a) (toCharacter b)
    htu hroot

theorem planarConvolutionCoeff_perm (a b : LSeries α R)
    {t u : PLTree α} (h : PLTree.Perm t u) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a b u :=
  PLTree.convolutionCoeff_perm (toCharacter a) (toCharacter b) h

/-- Multiplicative extension of planar labelled convolution coefficients. -/
def planarConvolutionForestCoeff (a b : LSeries α R) (ts : List (PLTree α)) : R :=
  PLTree.convolutionForestCoeff (toCharacter a) (toCharacter b) ts

/-- Pulling unlabelled series back by erasing labels commutes with planar convolution. -/
theorem planarConvolutionCoeff_comapEraseLabels
    (a b : Series R) (t : PLTree α) :
    planarConvolutionCoeff (comapEraseLabels (α := α) a)
        (comapEraseLabels (α := α) b) t =
      Series.planarConvolutionCoeff a b (PLTree.erase t) := by
  rw [planarConvolutionCoeff, Series.planarConvolutionCoeff,
    toCharacter_comapEraseLabels, toCharacter_comapEraseLabels]
  exact PLTree.convolutionCoeff_comapEraseLabels (Series.toCharacter a) (Series.toCharacter b) t

/-- Pulling unlabelled series back by erasing labels commutes with planar forest convolution. -/
theorem planarConvolutionForestCoeff_comapEraseLabels
    (a b : Series R) (ts : List (PLTree α)) :
    planarConvolutionForestCoeff (comapEraseLabels (α := α) a)
        (comapEraseLabels (α := α) b) ts =
      Series.planarConvolutionForestCoeff a b (ts.map PLTree.erase) := by
  rw [planarConvolutionForestCoeff, Series.planarConvolutionForestCoeff,
    toCharacter_comapEraseLabels, toCharacter_comapEraseLabels]
  exact PLTree.convolutionForestCoeff_comapEraseLabels
    (Series.toCharacter a) (Series.toCharacter b) ts

theorem planarConvolutionCoeff_comapConstLabel
    (x : α) (a b : LSeries α R) (t : PTree) :
    Series.planarConvolutionCoeff (comapConstLabel x a)
        (comapConstLabel x b) t =
      planarConvolutionCoeff a b (PLTree.constLabel x t) := by
  rw [Series.planarConvolutionCoeff, planarConvolutionCoeff,
    toCharacter_comapConstLabel, toCharacter_comapConstLabel]
  exact PLTree.convolutionCoeff_comapConstLabel
    x (toCharacter a) (toCharacter b) t

theorem planarConvolutionForestCoeff_comapConstLabel
    (x : α) (a b : LSeries α R) (ts : List PTree) :
    Series.planarConvolutionForestCoeff (comapConstLabel x a)
        (comapConstLabel x b) ts =
      planarConvolutionForestCoeff a b (ts.map (PLTree.constLabel x)) := by
  rw [Series.planarConvolutionForestCoeff, planarConvolutionForestCoeff,
    toCharacter_comapConstLabel, toCharacter_comapConstLabel]
  exact PLTree.convolutionForestCoeff_comapConstLabel
    x (toCharacter a) (toCharacter b) ts

/-- Planar convolution of label-invariant series depends only on the erased tree. -/
theorem LabelInvariant.planarConvolutionCoeff_eq [Nonempty α]
    {a b : LSeries α R} (ha : LabelInvariant a) (hb : LabelInvariant b)
    {t u : PLTree α} (htu : PLTree.erase t = PLTree.erase u) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a b u := by
  let x := Classical.choice (inferInstance : Nonempty α)
  have ha' := ha.comapEraseLabels_comapConstLabel x
  have hb' := hb.comapEraseLabels_comapConstLabel x
  rw [← ha', ← hb']
  rw [planarConvolutionCoeff_comapEraseLabels, planarConvolutionCoeff_comapEraseLabels, htu]

/-- Planar forest convolution of label-invariant series depends only on erased forests. -/
theorem LabelInvariant.planarConvolutionForestCoeff_eq [Nonempty α]
    {a b : LSeries α R} (ha : LabelInvariant a) (hb : LabelInvariant b)
    {ts us : List (PLTree α)} (hts : ts.map PLTree.erase = us.map PLTree.erase) :
    planarConvolutionForestCoeff a b ts = planarConvolutionForestCoeff a b us := by
  let x := Classical.choice (inferInstance : Nonempty α)
  have ha' := ha.comapEraseLabels_comapConstLabel x
  have hb' := hb.comapEraseLabels_comapConstLabel x
  rw [← ha', ← hb']
  rw [planarConvolutionForestCoeff_comapEraseLabels,
    planarConvolutionForestCoeff_comapEraseLabels, hts]

/-- Convolution coefficient on a non-planar labelled rooted forest. -/
def forestConvolutionCoeff (a b : LSeries α R) (φ : LRootedForest α) : R :=
  LRootedForest.convolutionCoeff (toCharacter a) (toCharacter b) φ

@[simp]
theorem forestConvolutionCoeff_zero (a b : LSeries α R) :
    forestConvolutionCoeff a b 0 = 1 := by
  simp [forestConvolutionCoeff]

@[simp]
theorem forestConvolutionCoeff_empty (a b : LSeries α R) :
    forestConvolutionCoeff a b LRootedForest.empty = 1 := by
  simp [forestConvolutionCoeff]

@[simp]
theorem forestConvolutionCoeff_singleton (a b : LSeries α R) (τ : LRootedTree α) :
    forestConvolutionCoeff a b (LRootedForest.singleton τ) =
      planarConvolutionCoeff a b (Quotient.out τ) := by
  simp [forestConvolutionCoeff, planarConvolutionCoeff]

theorem forestConvolutionCoeff_singleton_ofPLTree
    (a b : LSeries α R) (t : PLTree α) :
    forestConvolutionCoeff a b (LRootedForest.singleton (LRootedTree.ofPLTree t)) =
      planarConvolutionCoeff a b t := by
  rw [forestConvolutionCoeff_singleton]
  exact planarConvolutionCoeff_perm a b (LRootedTree.out_perm_ofPLTree t)

@[simp]
theorem forestConvolutionCoeff_add (a b : LSeries α R) (φ ψ : LRootedForest α) :
    forestConvolutionCoeff a b (φ + ψ) =
      forestConvolutionCoeff a b φ * forestConvolutionCoeff a b ψ := by
  simp [forestConvolutionCoeff]

theorem forestConvolutionCoeff_comapEraseLabels
    (a b : Series R) (φ : LRootedForest α) :
    forestConvolutionCoeff (comapEraseLabels (α := α) a)
        (comapEraseLabels (α := α) b) φ =
      Series.forestConvolutionCoeff a b (LRootedForest.erase φ) := by
  rw [forestConvolutionCoeff, Series.forestConvolutionCoeff,
    toCharacter_comapEraseLabels, toCharacter_comapEraseLabels]
  exact LRootedForest.convolutionCoeff_comapEraseLabels
    (Series.toCharacter a) (Series.toCharacter b) φ

theorem forestConvolutionCoeff_comapMapLabels {β : Type w}
    (f : α → β) (a b : LSeries β R) (φ : LRootedForest α) :
    forestConvolutionCoeff (comapMapLabels f a) (comapMapLabels f b) φ =
      LSeries.forestConvolutionCoeff a b (LRootedForest.mapLabels f φ) := by
  rw [forestConvolutionCoeff, forestConvolutionCoeff, toCharacter_comapMapLabels,
    toCharacter_comapMapLabels]
  exact LRootedForest.convolutionCoeff_comapMapLabels
    f (LSeries.toCharacter a) (LSeries.toCharacter b) φ

theorem forestConvolutionCoeff_comapConstLabel
    (x : α) (a b : LSeries α R) (φ : RootedForest) :
    Series.forestConvolutionCoeff (comapConstLabel x a)
        (comapConstLabel x b) φ =
      forestConvolutionCoeff a b (LRootedForest.constLabel x φ) := by
  rw [Series.forestConvolutionCoeff, forestConvolutionCoeff,
    toCharacter_comapConstLabel, toCharacter_comapConstLabel]
  exact RootedForest.convolutionCoeff_comapConstLabel
    x (toCharacter a) (toCharacter b) φ

theorem planarConvolutionCoeff_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {t : PLTree α} (ht : PLTree.order t ≤ n) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a' b' t :=
  PLTree.convolutionCoeff_congr_of_agree ha hb ht

theorem planarConvolutionForestCoeff_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {ts : List (PLTree α)} (hts : PLTree.orderList ts ≤ n) :
    planarConvolutionForestCoeff a b ts = planarConvolutionForestCoeff a' b' ts :=
  PLTree.convolutionForestCoeff_congr_of_agree ha hb hts

theorem forestConvolutionCoeff_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    forestConvolutionCoeff a b φ = forestConvolutionCoeff a' b' φ :=
  LRootedForest.convolutionCoeff_toCharacter_congr_of_agree ha hb hφ

theorem forestConvolutionCoeff_unit_right (a : LSeries α R) (φ : LRootedForest α) :
    forestConvolutionCoeff a (unit α R) φ = forestCoeff a φ := by
  rw [forestConvolutionCoeff, LSeries.toCharacter_unit,
    LRootedForest.convolutionCoeff_unit_right, LSeries.toCharacter_evalForest]

theorem forestConvolutionCoeff_unit_left (a : LSeries α R) (φ : LRootedForest α) :
    forestConvolutionCoeff (unit α R) a φ = forestCoeff a φ := by
  rw [forestConvolutionCoeff, LSeries.toCharacter_unit,
    LRootedForest.convolutionCoeff_unit_left, LSeries.toCharacter_evalForest]

/-- Convolution product of two labelled B-series coefficient families. -/
def convolution (a b : LSeries α R) : LSeries α R
  | .empty => 1
  | .tree τ => forestConvolutionCoeff a b (LRootedForest.singleton τ)

@[simp]
theorem convolution_empty (a b : LSeries α R) :
    coeff (convolution a b) LTreeIndex.empty = 1 :=
  rfl

@[simp]
theorem convolution_tree (a b : LSeries α R) (τ : LRootedTree α) :
    coeff (convolution a b) (.tree τ) =
      forestConvolutionCoeff a b (LRootedForest.singleton τ) :=
  rfl

theorem convolution_tree_eq_treeConvolutionCoeff
    (a b : LSeries α R) (τ : LRootedTree α) :
    coeff (convolution a b) (.tree τ) =
      LRootedTree.convolutionCoeff (toCharacter a) (toCharacter b) τ := by
  rw [convolution_tree]
  exact (LRootedTree.convolutionCoeff_eq_singleton (toCharacter a) (toCharacter b) τ).symm

theorem convolution_tree_comapEraseLabels
    (a b : Series R) (τ : LRootedTree α) :
    coeff (convolution (comapEraseLabels (α := α) a)
        (comapEraseLabels (α := α) b)) (.tree τ) =
      Series.coeff (Series.convolution a b) (.tree (LRootedTree.erase τ)) := by
  rw [convolution_tree, forestConvolutionCoeff_comapEraseLabels,
    LRootedForest.erase_singleton, Series.convolution_tree]

theorem convolution_comapEraseLabels (a b : Series R) :
    convolution (comapEraseLabels (α := α) a)
        (comapEraseLabels (α := α) b) =
      comapEraseLabels (α := α) (Series.convolution a b) := by
  funext ξ
  cases ξ with
  | empty =>
      rfl
  | tree τ =>
      exact convolution_tree_comapEraseLabels a b τ

theorem convolution_tree_comapMapLabels {β : Type w}
    (f : α → β) (a b : LSeries β R) (τ : LRootedTree α) :
    coeff (convolution (comapMapLabels f a) (comapMapLabels f b)) (.tree τ) =
      LSeries.coeff (convolution a b) (.tree (LRootedTree.map f τ)) := by
  rw [convolution_tree, forestConvolutionCoeff_comapMapLabels,
    LRootedForest.mapLabels_singleton, convolution_tree]

theorem convolution_comapMapLabels {β : Type w}
    (f : α → β) (a b : LSeries β R) :
    convolution (comapMapLabels f a) (comapMapLabels f b) =
      comapMapLabels f (convolution a b) := by
  funext ξ
  cases ξ with
  | empty =>
      rfl
  | tree τ =>
      exact convolution_tree_comapMapLabels f a b τ

theorem convolution_tree_comapConstLabel
    (x : α) (a b : LSeries α R) (τ : RootedTree) :
    Series.coeff (Series.convolution (comapConstLabel x a)
        (comapConstLabel x b)) (.tree τ) =
      coeff (convolution a b) (.tree (LRootedTree.constLabel x τ)) := by
  rw [Series.convolution_tree, forestConvolutionCoeff_comapConstLabel,
    LRootedForest.constLabel_singleton, convolution_tree]

theorem convolution_comapConstLabel
    (x : α) (a b : LSeries α R) :
    Series.convolution (comapConstLabel x a) (comapConstLabel x b) =
      comapConstLabel x (convolution a b) := by
  funext ξ
  cases ξ with
  | empty =>
      rfl
  | tree τ =>
      exact convolution_tree_comapConstLabel x a b τ

theorem LabelInvariant.convolution [Nonempty α]
    {a b : LSeries α R} (ha : LabelInvariant a) (hb : LabelInvariant b) :
    LabelInvariant (convolution a b) := by
  rcases (labelInvariant_iff_exists_comapEraseLabels (α := α) a).1 ha with ⟨a₀, ha₀⟩
  rcases (labelInvariant_iff_exists_comapEraseLabels (α := α) b).1 hb with ⟨b₀, hb₀⟩
  rw [← ha₀, ← hb₀, convolution_comapEraseLabels]
  exact labelInvariant_comapEraseLabels (α := α) (Series.convolution a₀ b₀)

theorem labelInvariantEquiv_convolution [Nonempty α] (a b : Series R) :
    labelInvariantEquiv (α := α) (R := R) (Series.convolution a b) =
      ⟨convolution
          (labelInvariantEquiv (α := α) (R := R) a).1
          (labelInvariantEquiv (α := α) (R := R) b).1,
        (labelInvariantEquiv (α := α) (R := R) a).2.convolution
          (labelInvariantEquiv (α := α) (R := R) b).2⟩ := by
  apply Subtype.ext
  exact (convolution_comapEraseLabels (α := α) a b).symm

theorem labelInvariantUnitEquiv_convolution [Nonempty α]
    (a b : {a : Series R // Series.HasUnitConstant a}) :
    labelInvariantUnitEquiv (α := α) (R := R)
        ⟨Series.convolution a.1 b.1, Series.convolution_hasUnitConstant a.1 b.1⟩ =
      ⟨convolution
          (labelInvariantUnitEquiv (α := α) (R := R) a).1
          (labelInvariantUnitEquiv (α := α) (R := R) b).1,
        by rfl,
        (labelInvariantUnitEquiv (α := α) (R := R) a).2.2.convolution
          (labelInvariantUnitEquiv (α := α) (R := R) b).2.2⟩ := by
  apply Subtype.ext
  exact (convolution_comapEraseLabels (α := α) a.1 b.1).symm

theorem labelInvariantEquiv_symm_convolution [Nonempty α]
    (a b : {a : LSeries α R // LabelInvariant a}) :
    (labelInvariantEquiv (α := α) (R := R)).symm
        ⟨LSeries.convolution a.1 b.1, a.2.convolution b.2⟩ =
      Series.convolution
        ((labelInvariantEquiv (α := α) (R := R)).symm a)
        ((labelInvariantEquiv (α := α) (R := R)).symm b) := by
  change
    comapConstLabel (Classical.choice (inferInstance : Nonempty α))
        (LSeries.convolution a.1 b.1) =
      Series.convolution
        (comapConstLabel (Classical.choice (inferInstance : Nonempty α)) a.1)
        (comapConstLabel (Classical.choice (inferInstance : Nonempty α)) b.1)
  exact (LSeries.convolution_comapConstLabel
    (Classical.choice (inferInstance : Nonempty α)) a.1 b.1).symm

theorem labelInvariantUnitEquiv_symm_convolution [Nonempty α]
    (a b : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}) :
    (labelInvariantUnitEquiv (α := α) (R := R)).symm
        ⟨LSeries.convolution a.1 b.1, by rfl, a.2.2.convolution b.2.2⟩ =
      ⟨Series.convolution
          ((labelInvariantUnitEquiv (α := α) (R := R)).symm a).1
          ((labelInvariantUnitEquiv (α := α) (R := R)).symm b).1,
        Series.convolution_hasUnitConstant
          ((labelInvariantUnitEquiv (α := α) (R := R)).symm a).1
          ((labelInvariantUnitEquiv (α := α) (R := R)).symm b).1⟩ := by
  apply Subtype.ext
  change
    comapConstLabel (Classical.choice (inferInstance : Nonempty α))
        (LSeries.convolution a.1 b.1) =
      Series.convolution
        (comapConstLabel (Classical.choice (inferInstance : Nonempty α)) a.1)
        (comapConstLabel (Classical.choice (inferInstance : Nonempty α)) b.1)
  exact (LSeries.convolution_comapConstLabel
    (Classical.choice (inferInstance : Nonempty α)) a.1 b.1).symm

theorem convolution_tree_ofPLTree (a b : LSeries α R) (t : PLTree α) :
    coeff (convolution a b) (.tree (LRootedTree.ofPLTree t)) =
      planarConvolutionCoeff a b t := by
  rw [convolution_tree]
  exact forestConvolutionCoeff_singleton_ofPLTree a b t

theorem convolution_hasUnitConstant (a b : LSeries α R) :
    HasUnitConstant (convolution a b) :=
  rfl

theorem forestCoeff_convolution (a b : LSeries α R) (φ : LRootedForest α) :
    forestCoeff (convolution a b) φ = forestConvolutionCoeff a b φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestCoeff]
  | cons τ ts ih =>
      change
        forestCoeff (convolution a b) (LRootedForest.singleton τ + (ts : LRootedForest α)) =
          forestConvolutionCoeff a b (LRootedForest.singleton τ + (ts : LRootedForest α))
      have ih' :
          forestCoeff (convolution a b) (ts : LRootedForest α) =
            forestConvolutionCoeff a b (ts : LRootedForest α) := by
        simpa using ih
      rw [forestCoeff_add, forestConvolutionCoeff_add, ih']
      rw [forestCoeff_singleton, convolution_tree]

theorem forestCoeff_convolution_singleton_tree
    (a b : LSeries α R) (τ : LRootedTree α) :
    forestCoeff (convolution a b) (LRootedForest.singleton τ) =
      LRootedTree.convolutionCoeff (toCharacter a) (toCharacter b) τ := by
  rw [forestCoeff_convolution]
  exact (LRootedTree.convolutionCoeff_eq_singleton (toCharacter a) (toCharacter b) τ).symm

theorem forestCoeff_convolution_singleton_ofPLTree (a b : LSeries α R) (t : PLTree α) :
    forestCoeff (convolution a b) (LRootedForest.singleton (LRootedTree.ofPLTree t)) =
      planarConvolutionCoeff a b t := by
  rw [forestCoeff_convolution]
  exact forestConvolutionCoeff_singleton_ofPLTree a b t

theorem forestCoeff_convolution_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {φ : LRootedForest α} (hφ : LRootedForest.order φ ≤ n) :
    forestCoeff (convolution a b) φ = forestCoeff (convolution a' b') φ := by
  rw [forestCoeff_convolution, forestCoeff_convolution]
  exact forestConvolutionCoeff_congr_of_agree ha hb hφ

theorem forestCoeff_convolution_congr_left_of_agree {a a' b : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    {φ : LRootedForest α} → LRootedForest.order φ ≤ n →
      forestCoeff (convolution a b) φ = forestCoeff (convolution a' b) φ :=
  forestCoeff_convolution_congr_of_agree ha (agreeUpToOrder_refl b n)

theorem forestCoeff_convolution_congr_right_of_agree {a b b' : LSeries α R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    {φ : LRootedForest α} → LRootedForest.order φ ≤ n →
      forestCoeff (convolution a b) φ = forestCoeff (convolution a b') φ :=
  forestCoeff_convolution_congr_of_agree (agreeUpToOrder_refl a n) hb

@[simp]
theorem forestCoeff_convolution_unit_right (a : LSeries α R) (φ : LRootedForest α) :
    forestCoeff (convolution a (unit α R)) φ = forestCoeff a φ := by
  rw [forestCoeff_convolution]
  exact forestConvolutionCoeff_unit_right a φ

@[simp]
theorem forestCoeff_convolution_unit_left (a : LSeries α R) (φ : LRootedForest α) :
    forestCoeff (convolution (unit α R) a) φ = forestCoeff a φ := by
  rw [forestCoeff_convolution]
  exact forestConvolutionCoeff_unit_left a φ

@[simp]
theorem toCharacter_convolution_ofForest (a b : LSeries α R) (φ : LRootedForest α) :
    toCharacter (convolution a b) (LForestAlgebra.ofForest (R := R) φ) =
      forestConvolutionCoeff a b φ := by
  simp [forestCoeff_convolution]

theorem toCharacter_convolution_ofForest_singleton_tree
    (a b : LSeries α R) (τ : LRootedTree α) :
    toCharacter (convolution a b)
        (LForestAlgebra.ofForest (R := R) (LRootedForest.singleton τ)) =
      LRootedTree.convolutionCoeff (toCharacter a) (toCharacter b) τ := by
  rw [toCharacter_convolution_ofForest]
  exact (LRootedTree.convolutionCoeff_eq_singleton (toCharacter a) (toCharacter b) τ).symm

theorem toCharacter_convolution_ofForest_singleton_ofPLTree
    (a b : LSeries α R) (t : PLTree α) :
    toCharacter (convolution a b)
        (LForestAlgebra.ofForest (R := R)
          (LRootedForest.singleton (LRootedTree.ofPLTree t))) =
      planarConvolutionCoeff a b t := by
  rw [toCharacter_convolution_ofForest]
  exact forestConvolutionCoeff_singleton_ofPLTree a b t

@[simp]
theorem toCharacter_convolution (a b : LSeries α R) :
    toCharacter (convolution a b) =
      LForestAlgebra.Character.convolution (toCharacter a) (toCharacter b) := by
  ext τ
  change
    (toCharacter (convolution a b)).evalForest (LRootedForest.singleton τ) =
      (LForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)).evalForest
        (LRootedForest.singleton τ)
  rw [toCharacter_evalForest, forestCoeff_convolution,
    LForestAlgebra.Character.convolution_evalForest]
  rfl

@[simp]
theorem toCharacter_convolution_unit_right (a : LSeries α R) :
    toCharacter (convolution a (unit α R)) = toCharacter a := by
  rw [toCharacter_convolution, LSeries.toCharacter_unit]
  exact LForestAlgebra.Character.convolution_unit_right (toCharacter a)

@[simp]
theorem toCharacter_convolution_unit_left (a : LSeries α R) :
    toCharacter (convolution (unit α R) a) = toCharacter a := by
  rw [toCharacter_convolution, LSeries.toCharacter_unit]
  exact LForestAlgebra.Character.convolution_unit_left (toCharacter a)

@[simp]
theorem ofCharacter_character_unit :
    ofCharacter (LForestAlgebra.Character.unit α R) = unit α R := by
  show ofCharacter (LForestAlgebra.counit α R) = unit α R
  rw [← LSeries.toCharacter_unit]
  exact ofCharacter_toCharacter unit_hasUnitConstant

theorem ofCharacter_convolution (χ ψ : LForestAlgebra.Character α R) :
    ofCharacter (LForestAlgebra.Character.convolution χ ψ) =
      convolution (ofCharacter χ) (ofCharacter ψ) := by
  apply ext_of_toCharacter_eq
  · exact ofCharacter_hasUnitConstant _
  · exact convolution_hasUnitConstant _ _
  · rw [toCharacter_ofCharacter, toCharacter_convolution, toCharacter_ofCharacter,
      toCharacter_ofCharacter]

theorem ofCharacter_convolution_toCharacter (a b : LSeries α R) :
    ofCharacter (LForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) =
      convolution a b := by
  apply ext_of_toCharacter_eq
  · exact ofCharacter_hasUnitConstant _
  · exact convolution_hasUnitConstant _ _
  · rw [toCharacter_ofCharacter, toCharacter_convolution]

@[simp]
theorem characterEquiv_unit :
    characterEquiv ⟨unit α R, unit_hasUnitConstant⟩ =
      LForestAlgebra.Character.unit α R := by
  show toCharacter (unit α R) = LForestAlgebra.Character.unit α R
  exact LSeries.toCharacter_unit

theorem characterEquiv_convolution
    (a b : {a : LSeries α R // HasUnitConstant a}) :
    characterEquiv ⟨convolution a.1 b.1, convolution_hasUnitConstant a.1 b.1⟩ =
      LForestAlgebra.Character.convolution (characterEquiv a) (characterEquiv b) := by
  simp [toCharacter_convolution]

theorem labelInvariantCharacterEquiv_convolution [Nonempty α]
    (a b : {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a}) :
    labelInvariantCharacterEquiv (α := α) (R := R)
        ⟨convolution a.1 b.1,
          convolution_hasUnitConstant a.1 b.1,
          a.2.2.convolution b.2.2⟩ =
      ⟨LForestAlgebra.Character.convolution
          (labelInvariantCharacterEquiv (α := α) (R := R) a).1
          (labelInvariantCharacterEquiv (α := α) (R := R) b).1,
        (labelInvariantCharacterEquiv (α := α) (R := R) a).2.convolution
          (labelInvariantCharacterEquiv (α := α) (R := R) b).2⟩ := by
  apply Subtype.ext
  exact characterEquiv_convolution ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩

theorem characterEquiv_symm_convolution (χ ψ : LForestAlgebra.Character α R) :
    ((characterEquiv (α := α) (R := R)).symm
        (LForestAlgebra.Character.convolution χ ψ)).1 =
      convolution ((characterEquiv (α := α) (R := R)).symm χ).1
        ((characterEquiv (α := α) (R := R)).symm ψ).1 := by
  simp [ofCharacter_convolution]

theorem eq_convolution_of_toCharacter_eq {a b c : LSeries α R} (hc : HasUnitConstant c)
    (h : toCharacter c =
      LForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) :
    c = convolution a b :=
  ext_of_toCharacter_eq hc (convolution_hasUnitConstant a b)
    (h.trans (toCharacter_convolution a b).symm)

theorem convolution_assoc_of_character_assoc {a b c : LSeries α R}
    (hassoc :
      LForestAlgebra.Character.convolution
          (LForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) (toCharacter c) =
        LForestAlgebra.Character.convolution (toCharacter a)
          (LForestAlgebra.Character.convolution (toCharacter b) (toCharacter c))) :
    convolution (convolution a b) c = convolution a (convolution b c) := by
  apply ext_of_toCharacter_eq
  · exact convolution_hasUnitConstant _ _
  · exact convolution_hasUnitConstant _ _
  · rw [toCharacter_convolution, toCharacter_convolution, toCharacter_convolution,
      toCharacter_convolution]
    exact hassoc

theorem convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : LForestAlgebra α R,
      LForestAlgebra.coproductLeft α R x = LForestAlgebra.coproductRight α R x)
    (a b c : LSeries α R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (LForestAlgebra.Character.convolution_assoc_of_coproduct_eq
      (α := α) (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc :
      LForestAlgebra.coproductLeft α R = LForestAlgebra.coproductRight α R)
    (a b c : LSeries α R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (LForestAlgebra.Character.convolution_assoc_of_coproductLeft_eq_coproductRight
      (α := α) (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc_of_nestedCoproductTerms
    (hcoassoc : ∀ t : PLTree α,
      LForestTripleTensorAlgebra.sumTerms (R := R) (PLTree.nestedCoproductLeftTerms t) =
        LForestTripleTensorAlgebra.sumTerms (R := R) (PLTree.nestedCoproductRightTerms t))
    (a b c : LSeries α R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (LForestAlgebra.Character.convolution_assoc_of_nestedCoproductTerms
      (α := α) (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc_of_nestedCoproductTerms_perm
    (hcoassoc : ∀ t : PLTree α,
      (PLTree.nestedCoproductLeftTerms t).Perm (PLTree.nestedCoproductRightTerms t))
    (a b c : LSeries α R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (LForestAlgebra.Character.convolution_assoc_of_nestedCoproductTerms_perm
      (α := α) (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc (a b c : LSeries α R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_coproductLeft_eq_coproductRight
    (LForestAlgebra.coproductLeft_eq_coproductRight (α := α) (R := R)) a b c

theorem agreeUpToOrder_convolution_assoc_of_character_assoc {a b c : LSeries α R}
    (hassoc :
      LForestAlgebra.Character.convolution
          (LForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) (toCharacter c) =
        LForestAlgebra.Character.convolution (toCharacter a)
          (LForestAlgebra.Character.convolution (toCharacter b) (toCharacter c)))
    (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc_of_character_assoc hassoc) n

theorem agreeUpToOrder_convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : LForestAlgebra α R,
      LForestAlgebra.coproductLeft α R x = LForestAlgebra.coproductRight α R x)
    (a b c : LSeries α R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc_of_coproduct_eq hcoassoc a b c) n

theorem agreeUpToOrder_convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc :
      LForestAlgebra.coproductLeft α R = LForestAlgebra.coproductRight α R)
    (a b c : LSeries α R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq
    (convolution_assoc_of_coproductLeft_eq_coproductRight hcoassoc a b c) n

theorem agreeUpToOrder_convolution_assoc_of_nestedCoproductTerms_perm
    (hcoassoc : ∀ t : PLTree α,
      (PLTree.nestedCoproductLeftTerms t).Perm (PLTree.nestedCoproductRightTerms t))
    (a b c : LSeries α R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc_of_nestedCoproductTerms_perm hcoassoc a b c) n

theorem agreeUpToOrder_convolution_assoc
    (a b c : LSeries α R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc a b c) n

theorem convolution_tree_congr_of_agree {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {τ : LRootedTree α} (hτ : LRootedTree.order τ ≤ n) :
    coeff (convolution a b) (.tree τ) = coeff (convolution a' b') (.tree τ) := by
  change
      forestConvolutionCoeff a b (LRootedForest.singleton τ) =
      forestConvolutionCoeff a' b' (LRootedForest.singleton τ)
  exact forestConvolutionCoeff_congr_of_agree ha hb (by simpa using hτ)

theorem convolution_tree_congr_left_of_agree {a a' b : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    {τ : LRootedTree α} → LRootedTree.order τ ≤ n →
      coeff (convolution a b) (.tree τ) = coeff (convolution a' b) (.tree τ) :=
  convolution_tree_congr_of_agree ha (agreeUpToOrder_refl b n)

theorem convolution_tree_congr_right_of_agree {a b b' : LSeries α R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    {τ : LRootedTree α} → LRootedTree.order τ ≤ n →
      coeff (convolution a b) (.tree τ) = coeff (convolution a b') (.tree τ) :=
  convolution_tree_congr_of_agree (agreeUpToOrder_refl a n) hb

theorem agreeUpToOrder_convolution {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (convolution a b) (convolution a' b') n := by
  intro ξ hξ
  cases ξ with
  | empty =>
      rw [convolution_empty, convolution_empty]
  | tree τ =>
      exact convolution_tree_congr_of_agree ha hb hξ

theorem agreeUpToOrder_convolution_left {a a' b : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    AgreeUpToOrder (convolution a b) (convolution a' b) n :=
  agreeUpToOrder_convolution ha (agreeUpToOrder_refl b n)

theorem agreeUpToOrder_convolution_right {a b b' : LSeries α R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (convolution a b) (convolution a b') n :=
  agreeUpToOrder_convolution (agreeUpToOrder_refl a n) hb

theorem convolution_eq_of_agreeUpToOrder_all {a a' b b' : LSeries α R}
    (ha : ∀ n, AgreeUpToOrder a a' n) (hb : ∀ n, AgreeUpToOrder b b' n) :
    convolution a b = convolution a' b' := by
  funext ξ
  cases ξ with
  | empty =>
      rfl
  | tree τ =>
      simpa [LSeries.coeff] using
        convolution_tree_congr_of_agree
          (ha (LRootedTree.order τ)) (hb (LRootedTree.order τ)) (τ := τ) le_rfl

theorem convolution_left_eq_of_agreeUpToOrder_all {a a' b : LSeries α R}
    (ha : ∀ n, AgreeUpToOrder a a' n) :
    convolution a b = convolution a' b :=
  convolution_eq_of_agreeUpToOrder_all ha (fun n => agreeUpToOrder_refl b n)

theorem convolution_right_eq_of_agreeUpToOrder_all {a b b' : LSeries α R}
    (hb : ∀ n, AgreeUpToOrder b b' n) :
    convolution a b = convolution a b' :=
  convolution_eq_of_agreeUpToOrder_all (fun n => agreeUpToOrder_refl a n) hb

theorem agreeUpToOrder_all_convolution {a a' b b' : LSeries α R}
    (ha : ∀ n, AgreeUpToOrder a a' n) (hb : ∀ n, AgreeUpToOrder b b' n) :
    ∀ n, AgreeUpToOrder (convolution a b) (convolution a' b') n := by
  rw [agreeUpToOrder_all_iff_eq]
  exact convolution_eq_of_agreeUpToOrder_all ha hb

theorem agreeUpToOrder_all_convolution_left {a a' b : LSeries α R}
    (ha : ∀ n, AgreeUpToOrder a a' n) :
    ∀ n, AgreeUpToOrder (convolution a b) (convolution a' b) n :=
  agreeUpToOrder_all_convolution ha (fun n => agreeUpToOrder_refl b n)

theorem agreeUpToOrder_all_convolution_right {a b b' : LSeries α R}
    (hb : ∀ n, AgreeUpToOrder b b' n) :
    ∀ n, AgreeUpToOrder (convolution a b) (convolution a b') n :=
  agreeUpToOrder_all_convolution (fun n => agreeUpToOrder_refl a n) hb

theorem convolution_unit_right {a : LSeries α R} (ha : HasUnitConstant a) :
    convolution a (unit α R) = a := by
  funext τ
  cases τ with
  | empty =>
      exact ha.symm
  | tree τ =>
      change forestConvolutionCoeff a (unit α R) (LRootedForest.singleton τ) = a (.tree τ)
      simpa [LSeries.coeff] using
        forestConvolutionCoeff_unit_right a (LRootedForest.singleton τ)

theorem convolution_unit_left {a : LSeries α R} (ha : HasUnitConstant a) :
    convolution (unit α R) a = a := by
  funext τ
  cases τ with
  | empty =>
      exact ha.symm
  | tree τ =>
      change forestConvolutionCoeff (unit α R) a (LRootedForest.singleton τ) = a (.tree τ)
      simpa [LSeries.coeff] using
        forestConvolutionCoeff_unit_left a (LRootedForest.singleton τ)

noncomputable instance instUnitConstantMonoid :
    Monoid {a : LSeries α R // HasUnitConstant a} where
  one := ⟨unit α R, unit_hasUnitConstant⟩
  mul a b := ⟨convolution a.1 b.1, convolution_hasUnitConstant a.1 b.1⟩
  mul_assoc a b c := by
    apply Subtype.ext
    exact convolution_assoc a.1 b.1 c.1
  one_mul a := by
    apply Subtype.ext
    exact convolution_unit_left a.2
  mul_one a := by
    apply Subtype.ext
    exact convolution_unit_right a.2

noncomputable def characterMulEquiv :
    {a : LSeries α R // HasUnitConstant a} ≃* LForestAlgebra.Character α R where
  toEquiv := characterEquiv
  map_mul' a b := by
    change characterEquiv ⟨convolution a.1 b.1, convolution_hasUnitConstant a.1 b.1⟩ =
      LForestAlgebra.Character.convolution (characterEquiv a) (characterEquiv b)
    exact characterEquiv_convolution a b

noncomputable instance instLabelInvariantUnitConstantMonoid [Nonempty α] :
    Monoid {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a} where
  one := ⟨unit α R, unit_hasUnitConstant, labelInvariant_unit⟩
  mul a b :=
    ⟨convolution a.1 b.1, convolution_hasUnitConstant a.1 b.1, a.2.2.convolution b.2.2⟩
  mul_assoc a b c := by
    apply Subtype.ext
    exact convolution_assoc a.1 b.1 c.1
  one_mul a := by
    apply Subtype.ext
    exact convolution_unit_left a.2.1
  mul_one a := by
    apply Subtype.ext
    exact convolution_unit_right a.2.1

noncomputable def labelInvariantUnitMulEquiv [Nonempty α] :
    {a : Series R // Series.HasUnitConstant a} ≃*
      {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a} where
  toEquiv := labelInvariantUnitEquiv
  map_mul' a b := by
    change labelInvariantUnitEquiv (α := α) (R := R)
        ⟨Series.convolution a.1 b.1, Series.convolution_hasUnitConstant a.1 b.1⟩ =
      ⟨convolution (labelInvariantUnitEquiv (α := α) (R := R) a).1
          (labelInvariantUnitEquiv (α := α) (R := R) b).1,
        convolution_hasUnitConstant _ _,
        (labelInvariantUnitEquiv (α := α) (R := R) a).2.2.convolution
          (labelInvariantUnitEquiv (α := α) (R := R) b).2.2⟩
    exact labelInvariantUnitEquiv_convolution a b

noncomputable def labelInvariantCharacterMulEquiv [Nonempty α] :
    {a : LSeries α R // HasUnitConstant a ∧ LabelInvariant a} ≃*
      {χ : LForestAlgebra.Character α R // LForestAlgebra.Character.LabelInvariant χ} where
  toEquiv := labelInvariantCharacterEquiv
  map_mul' a b := by
    change labelInvariantCharacterEquiv (α := α) (R := R)
        ⟨convolution a.1 b.1, convolution_hasUnitConstant a.1 b.1, a.2.2.convolution b.2.2⟩ =
      ⟨LForestAlgebra.Character.convolution
          (labelInvariantCharacterEquiv (α := α) (R := R) a).1
          (labelInvariantCharacterEquiv (α := α) (R := R) b).1,
        (labelInvariantCharacterEquiv (α := α) (R := R) a).2.convolution
          (labelInvariantCharacterEquiv (α := α) (R := R) b).2⟩
    exact labelInvariantCharacterEquiv_convolution a b

@[simp]
theorem planarConvolutionForestCoeff_nil (a b : LSeries α R) :
    planarConvolutionForestCoeff a b [] = 1 := by
  simp [planarConvolutionForestCoeff]

@[simp]
theorem planarConvolutionForestCoeff_cons (a b : LSeries α R)
    (t : PLTree α) (ts : List (PLTree α)) :
    planarConvolutionForestCoeff a b (t :: ts) =
      planarConvolutionCoeff a b t * planarConvolutionForestCoeff a b ts := by
  simp [planarConvolutionForestCoeff, planarConvolutionCoeff]

theorem planarConvolutionForestCoeff_perm (a b : LSeries α R)
    {ts us : List (PLTree α)} (h : ts.Perm us) :
    planarConvolutionForestCoeff a b ts = planarConvolutionForestCoeff a b us :=
  PLTree.convolutionForestCoeff_perm (toCharacter a) (toCharacter b) h

theorem planarConvolutionForestCoeff_forall₂_perm (a b : LSeries α R) :
    ∀ {ts us : List (PLTree α)}, List.Forall₂ PLTree.Perm ts us →
      planarConvolutionForestCoeff a b ts = planarConvolutionForestCoeff a b us :=
  PLTree.convolutionForestCoeff_forall₂_perm (toCharacter a) (toCharacter b)

end

section Field

variable {α : Type u} {R : Type v} [Field R]

theorem convolution_hasOrder_zero (a b : LSeries α R) :
    HasOrder (convolution a b) 0 := by
  rw [hasOrder_zero_iff]
  exact convolution_hasUnitConstant a b

theorem convolution_hasOrder_all_congr {a a' b b' : LSeries α R}
    (ha : ∀ n, AgreeUpToOrder a a' n) (hb : ∀ n, AgreeUpToOrder b b' n) :
    (∀ n, HasOrder (convolution a b) n) ↔
      ∀ n, HasOrder (convolution a' b') n :=
  hasOrder_all_congr (agreeUpToOrder_all_convolution ha hb)

theorem convolution_hasOrder_congr {a a' b b' : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    HasOrder (convolution a b) n ↔ HasOrder (convolution a' b') n :=
  hasOrder_congr (agreeUpToOrder_convolution ha hb)

theorem convolution_hasOrder_all_congr_left {a a' b : LSeries α R}
    (ha : ∀ n, AgreeUpToOrder a a' n) :
    (∀ n, HasOrder (convolution a b) n) ↔
      ∀ n, HasOrder (convolution a' b) n :=
  convolution_hasOrder_all_congr ha (fun n => agreeUpToOrder_refl b n)

theorem convolution_hasOrder_congr_left {a a' b : LSeries α R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    HasOrder (convolution a b) n ↔ HasOrder (convolution a' b) n :=
  convolution_hasOrder_congr ha (agreeUpToOrder_refl b n)

theorem convolution_hasOrder_all_congr_right {a b b' : LSeries α R}
    (hb : ∀ n, AgreeUpToOrder b b' n) :
    (∀ n, HasOrder (convolution a b) n) ↔
      ∀ n, HasOrder (convolution a b') n :=
  convolution_hasOrder_all_congr (fun n => agreeUpToOrder_refl a n) hb

theorem convolution_hasOrder_congr_right {a b b' : LSeries α R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    HasOrder (convolution a b) n ↔ HasOrder (convolution a b') n :=
  convolution_hasOrder_congr (agreeUpToOrder_refl a n) hb

theorem convolution_unit_right_of_hasOrder {a : LSeries α R} {n : Nat}
    (ha : HasOrder a n) : convolution a (unit α R) = a :=
  convolution_unit_right ha.hasUnitConstant

theorem convolution_unit_left_of_hasOrder {a : LSeries α R} {n : Nat}
    (ha : HasOrder a n) : convolution (unit α R) a = a :=
  convolution_unit_left ha.hasUnitConstant

end Field

end LSeries

end BSeries
