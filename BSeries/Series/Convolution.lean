/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import HopfAlgebras.Hopf.CharacterConvolution
import BSeries.Series.Basic

/-!
# Convolution of B-Series

The Butcher-group convolution of B-series coefficient families, expressed
through the character convolution of `Hopf/CharacterConvolution.lean`, with
the congruence lemmas for order-truncated agreement.
-/

namespace BSeries

open HopfAlgebras

universe u

namespace PTree

open HopfAlgebras.PTree

noncomputable section

variable {R : Type u} [CommSemiring R]

theorem evalCoproductTerm_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : Series.AgreeUpToOrder a a' n) (hb : Series.AgreeUpToOrder b b' n)
    (term : RootedForest × RootedForest)
    (hterm : RootedForest.order term.1 + RootedForest.order term.2 ≤ n) :
    evalCoproductTerm (Series.toCharacter a) (Series.toCharacter b) term =
      evalCoproductTerm (Series.toCharacter a') (Series.toCharacter b') term := by
  have hleft : RootedForest.order term.1 ≤ n := by omega
  have hright : RootedForest.order term.2 ≤ n := by omega
  simp [
    evalCoproductTerm,
    ForestAlgebra.Character.evalForest,
    Series.AgreeUpToOrder.forestCoeff ha hleft,
    Series.AgreeUpToOrder.forestCoeff hb hright
  ]

theorem evalCoproductTerms_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : Series.AgreeUpToOrder a a' n) (hb : Series.AgreeUpToOrder b b' n)
    {terms : List (RootedForest × RootedForest)}
    (hterms : ∀ term ∈ terms,
      RootedForest.order term.1 + RootedForest.order term.2 ≤ n) :
    evalCoproductTerms (Series.toCharacter a) (Series.toCharacter b) terms =
      evalCoproductTerms (Series.toCharacter a') (Series.toCharacter b') terms := by
  induction terms with
  | nil =>
      rw [evalCoproductTerms_nil, evalCoproductTerms_nil]
  | cons term terms ih =>
      have hterm : RootedForest.order term.1 + RootedForest.order term.2 ≤ n :=
        hterms term (by simp)
      have htail :
          ∀ term ∈ terms, RootedForest.order term.1 + RootedForest.order term.2 ≤ n := by
        intro term hmem
        exact hterms term (by simp [hmem])
      rw [
        evalCoproductTerms_cons,
        evalCoproductTerms_cons,
        evalCoproductTerm_congr_of_agree ha hb term hterm,
        ih htail
      ]

theorem convolutionCoeff_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : Series.AgreeUpToOrder a a' n) (hb : Series.AgreeUpToOrder b b' n)
    {t : PTree} (ht : PTree.order t ≤ n) :
    convolutionCoeff (Series.toCharacter a) (Series.toCharacter b) t =
      convolutionCoeff (Series.toCharacter a') (Series.toCharacter b') t := by
  unfold convolutionCoeff
  exact evalCoproductTerms_congr_of_agree ha hb (fun term hterm => by
    rw [coproductTerms_order hterm]
    exact ht)

theorem convolutionForestCoeff_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : Series.AgreeUpToOrder a a' n) (hb : Series.AgreeUpToOrder b b' n)
    {ts : List PTree} (hts : PTree.orderList ts ≤ n) :
    convolutionForestCoeff (Series.toCharacter a) (Series.toCharacter b) ts =
      convolutionForestCoeff (Series.toCharacter a') (Series.toCharacter b') ts := by
  unfold convolutionForestCoeff
  exact evalCoproductTerms_congr_of_agree ha hb (fun term hterm => by
    rw [coproductTermsList_order hterm]
    exact hts)


end

end PTree

namespace RootedForest

open HopfAlgebras.RootedForest

noncomputable section

variable {R : Type u} [CommSemiring R]

private theorem order_out (τ : RootedTree) :
    PTree.order (Quotient.out τ) = RootedTree.order τ := by
  rw [← RootedTree.order_ofPTree (Quotient.out τ)]
  rw [show RootedTree.ofPTree (Quotient.out τ) = τ from Quotient.out_eq τ]

private theorem orderList_out :
    ∀ ts : List RootedTree,
      PTree.orderList (ts.map Quotient.out) = RootedForest.order (ts : RootedForest)
  | [] => rfl
  | τ :: ts => by
      simp [RootedForest.order, order_out τ, orderList_out ts]

theorem convolutionCoeff_toCharacter_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : Series.AgreeUpToOrder a a' n) (hb : Series.AgreeUpToOrder b b' n)
    {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    convolutionCoeff (Series.toCharacter a) (Series.toCharacter b) φ =
      convolutionCoeff (Series.toCharacter a') (Series.toCharacter b') φ := by
  suffices hforest :
      ∀ φ : RootedForest, RootedForest.order φ ≤ n →
        convolutionCoeff (Series.toCharacter a) (Series.toCharacter b) φ =
          convolutionCoeff (Series.toCharacter a') (Series.toCharacter b') φ from
    hforest φ hφ
  intro φ
  refine Quotient.inductionOn φ ?_
  intro ts hts
  rw [convolutionCoeff, convolutionCoeff]
  change
    ForestTensorAlgebra.evalByCharacters (Series.toCharacter a) (Series.toCharacter b)
        (PTree.coproductList (R := R) (ts.map Quotient.out)) =
      ForestTensorAlgebra.evalByCharacters (Series.toCharacter a') (Series.toCharacter b')
        (PTree.coproductList (R := R) (ts.map Quotient.out))
  rw [ForestTensorAlgebra.evalByCharacters_coproductList,
    ForestTensorAlgebra.evalByCharacters_coproductList]
  exact PTree.convolutionForestCoeff_congr_of_agree ha hb (by
    rw [orderList_out]
    exact hts)


end

end RootedForest

namespace Series

noncomputable section

variable {R : Type u} [CommSemiring R]

/-- Planar convolution coefficient obtained from the cut coproduct. -/
def planarConvolutionCoeff (a b : Series R) (t : PTree) : R :=
  PTree.convolutionCoeff (toCharacter a) (toCharacter b) t

/-- Multiplicative extension of planar convolution coefficients to planar forests. -/
def planarConvolutionForestCoeff (a b : Series R) (ts : List PTree) : R :=
  PTree.convolutionForestCoeff (toCharacter a) (toCharacter b) ts

theorem planarConvolutionCoeff_eq_of_cuts_listRelPerm
    (a b : Series R) {t u : PTree}
    (h : PTree.ListRelPerm PTree.Cut.Perm (PTree.cuts t) (PTree.cuts u)) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a b u :=
  PTree.convolutionCoeff_eq_of_cuts_listRelPerm (toCharacter a) (toCharacter b) h

theorem planarConvolutionCoeff_eq_of_rootCuts_listRelPerm
    (a b : Series R) {t u : PTree} (htu : PTree.Perm t u)
    (hroot : PTree.ListRelPerm PTree.RootCut.Perm (PTree.rootCuts t) (PTree.rootCuts u)) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a b u :=
  PTree.convolutionCoeff_eq_of_rootCuts_listRelPerm (toCharacter a) (toCharacter b) htu hroot

theorem planarConvolutionCoeff_perm (a b : Series R)
    {t u : PTree} (h : PTree.Perm t u) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a b u :=
  PTree.convolutionCoeff_perm (toCharacter a) (toCharacter b) h

/-- Convolution coefficient on a non-planar rooted forest. -/
def forestConvolutionCoeff (a b : Series R) (φ : RootedForest) : R :=
  RootedForest.convolutionCoeff (toCharacter a) (toCharacter b) φ

@[simp]
theorem forestConvolutionCoeff_zero (a b : Series R) :
    forestConvolutionCoeff a b 0 = 1 := by
  simp [forestConvolutionCoeff]

@[simp]
theorem forestConvolutionCoeff_empty (a b : Series R) :
    forestConvolutionCoeff a b RootedForest.empty = 1 := by
  simp [forestConvolutionCoeff]

@[simp]
theorem forestConvolutionCoeff_singleton (a b : Series R) (τ : RootedTree) :
    forestConvolutionCoeff a b (RootedForest.singleton τ) =
      planarConvolutionCoeff a b (Quotient.out τ) := by
  simp [forestConvolutionCoeff, planarConvolutionCoeff]

theorem forestConvolutionCoeff_singleton_ofPTree
    (a b : Series R) (t : PTree) :
    forestConvolutionCoeff a b (RootedForest.singleton (RootedTree.ofPTree t)) =
      planarConvolutionCoeff a b t := by
  rw [forestConvolutionCoeff_singleton]
  exact planarConvolutionCoeff_perm a b (RootedTree.out_perm_ofPTree t)

@[simp]
theorem forestConvolutionCoeff_add (a b : Series R) (φ ψ : RootedForest) :
    forestConvolutionCoeff a b (φ + ψ) =
      forestConvolutionCoeff a b φ * forestConvolutionCoeff a b ψ := by
  simp [forestConvolutionCoeff]

theorem planarConvolutionCoeff_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {t : PTree} (ht : PTree.order t ≤ n) :
    planarConvolutionCoeff a b t = planarConvolutionCoeff a' b' t :=
  PTree.convolutionCoeff_congr_of_agree ha hb ht

theorem planarConvolutionForestCoeff_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {ts : List PTree} (hts : PTree.orderList ts ≤ n) :
    planarConvolutionForestCoeff a b ts = planarConvolutionForestCoeff a' b' ts :=
  PTree.convolutionForestCoeff_congr_of_agree ha hb hts

theorem forestConvolutionCoeff_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    forestConvolutionCoeff a b φ = forestConvolutionCoeff a' b' φ :=
  RootedForest.convolutionCoeff_toCharacter_congr_of_agree ha hb hφ

theorem forestConvolutionCoeff_unit_right (a : Series R) (φ : RootedForest) :
    forestConvolutionCoeff a (unit R) φ = forestCoeff a φ := by
  rw [forestConvolutionCoeff, Series.toCharacter_unit,
    RootedForest.convolutionCoeff_unit_right, Series.toCharacter_evalForest]

theorem forestConvolutionCoeff_unit_left (a : Series R) (φ : RootedForest) :
    forestConvolutionCoeff (unit R) a φ = forestCoeff a φ := by
  rw [forestConvolutionCoeff, Series.toCharacter_unit,
    RootedForest.convolutionCoeff_unit_left, Series.toCharacter_evalForest]

/-- Convolution product of two B-series coefficient families. -/
def convolution (a b : Series R) : Series R
  | .empty => 1
  | .tree τ => forestConvolutionCoeff a b (RootedForest.singleton τ)

@[simp]
theorem convolution_empty (a b : Series R) :
    coeff (convolution a b) TreeIndex.empty = 1 :=
  rfl

@[simp]
theorem convolution_tree (a b : Series R) (τ : RootedTree) :
    coeff (convolution a b) (.tree τ) =
      forestConvolutionCoeff a b (RootedForest.singleton τ) :=
  rfl

theorem convolution_tree_eq_treeConvolutionCoeff
    (a b : Series R) (τ : RootedTree) :
    coeff (convolution a b) (.tree τ) =
      RootedTree.convolutionCoeff (toCharacter a) (toCharacter b) τ := by
  rw [convolution_tree]
  exact (RootedTree.convolutionCoeff_eq_singleton (toCharacter a) (toCharacter b) τ).symm

theorem convolution_tree_ofPTree (a b : Series R) (t : PTree) :
    coeff (convolution a b) (.tree (RootedTree.ofPTree t)) =
      planarConvolutionCoeff a b t := by
  rw [convolution_tree]
  exact forestConvolutionCoeff_singleton_ofPTree a b t

theorem convolution_hasUnitConstant (a b : Series R) :
    HasUnitConstant (convolution a b) :=
  rfl

theorem forestCoeff_convolution (a b : Series R) (φ : RootedForest) :
    forestCoeff (convolution a b) φ = forestConvolutionCoeff a b φ := by
  refine Quotient.inductionOn φ ?_
  intro ts
  induction ts with
  | nil =>
      simp [forestCoeff]
  | cons τ ts ih =>
      change
        forestCoeff (convolution a b) (RootedForest.singleton τ + (ts : RootedForest)) =
          forestConvolutionCoeff a b (RootedForest.singleton τ + (ts : RootedForest))
      have ih' :
          forestCoeff (convolution a b) (ts : RootedForest) =
            forestConvolutionCoeff a b (ts : RootedForest) := by
        simpa using ih
      rw [forestCoeff_add, forestConvolutionCoeff_add, ih']
      rw [forestCoeff_singleton, convolution_tree]

theorem forestCoeff_convolution_singleton_tree
    (a b : Series R) (τ : RootedTree) :
    forestCoeff (convolution a b) (RootedForest.singleton τ) =
      RootedTree.convolutionCoeff (toCharacter a) (toCharacter b) τ := by
  rw [forestCoeff_convolution]
  exact (RootedTree.convolutionCoeff_eq_singleton (toCharacter a) (toCharacter b) τ).symm

theorem forestCoeff_convolution_singleton_ofPTree (a b : Series R) (t : PTree) :
    forestCoeff (convolution a b) (RootedForest.singleton (RootedTree.ofPTree t)) =
      planarConvolutionCoeff a b t := by
  rw [forestCoeff_convolution]
  exact forestConvolutionCoeff_singleton_ofPTree a b t

theorem forestCoeff_convolution_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {φ : RootedForest} (hφ : RootedForest.order φ ≤ n) :
    forestCoeff (convolution a b) φ = forestCoeff (convolution a' b') φ := by
  rw [forestCoeff_convolution, forestCoeff_convolution]
  exact forestConvolutionCoeff_congr_of_agree ha hb hφ

theorem forestCoeff_convolution_congr_left_of_agree {a a' b : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    {φ : RootedForest} → RootedForest.order φ ≤ n →
      forestCoeff (convolution a b) φ = forestCoeff (convolution a' b) φ :=
  forestCoeff_convolution_congr_of_agree ha (agreeUpToOrder_refl b n)

theorem forestCoeff_convolution_congr_right_of_agree {a b b' : Series R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    {φ : RootedForest} → RootedForest.order φ ≤ n →
      forestCoeff (convolution a b) φ = forestCoeff (convolution a b') φ :=
  forestCoeff_convolution_congr_of_agree (agreeUpToOrder_refl a n) hb

@[simp]
theorem forestCoeff_convolution_unit_right (a : Series R) (φ : RootedForest) :
    forestCoeff (convolution a (unit R)) φ = forestCoeff a φ := by
  rw [forestCoeff_convolution]
  exact forestConvolutionCoeff_unit_right a φ

@[simp]
theorem forestCoeff_convolution_unit_left (a : Series R) (φ : RootedForest) :
    forestCoeff (convolution (unit R) a) φ = forestCoeff a φ := by
  rw [forestCoeff_convolution]
  exact forestConvolutionCoeff_unit_left a φ

@[simp]
theorem toCharacter_convolution_ofForest (a b : Series R) (φ : RootedForest) :
    toCharacter (convolution a b) (ForestAlgebra.ofForest (R := R) φ) =
      forestConvolutionCoeff a b φ := by
  simp [forestCoeff_convolution]

theorem toCharacter_convolution_ofForest_singleton_tree
    (a b : Series R) (τ : RootedTree) :
    toCharacter (convolution a b)
        (ForestAlgebra.ofForest (R := R) (RootedForest.singleton τ)) =
      RootedTree.convolutionCoeff (toCharacter a) (toCharacter b) τ := by
  rw [toCharacter_convolution_ofForest]
  exact (RootedTree.convolutionCoeff_eq_singleton (toCharacter a) (toCharacter b) τ).symm

theorem toCharacter_convolution_ofForest_singleton_ofPTree
    (a b : Series R) (t : PTree) :
    toCharacter (convolution a b)
        (ForestAlgebra.ofForest (R := R)
          (RootedForest.singleton (RootedTree.ofPTree t))) =
      planarConvolutionCoeff a b t := by
  rw [toCharacter_convolution_ofForest]
  exact forestConvolutionCoeff_singleton_ofPTree a b t

@[simp]
theorem toCharacter_convolution (a b : Series R) :
    toCharacter (convolution a b) =
      ForestAlgebra.Character.convolution (toCharacter a) (toCharacter b) := by
  ext τ
  change
    (toCharacter (convolution a b)).evalForest (RootedForest.singleton τ) =
      (ForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)).evalForest
        (RootedForest.singleton τ)
  rw [toCharacter_evalForest, forestCoeff_convolution,
    ForestAlgebra.Character.convolution_evalForest]
  rfl

@[simp]
theorem toCharacter_convolution_unit_right (a : Series R) :
    toCharacter (convolution a (unit R)) = toCharacter a := by
  rw [toCharacter_convolution, Series.toCharacter_unit]
  exact ForestAlgebra.Character.convolution_unit_right (toCharacter a)

@[simp]
theorem toCharacter_convolution_unit_left (a : Series R) :
    toCharacter (convolution (unit R) a) = toCharacter a := by
  rw [toCharacter_convolution, Series.toCharacter_unit]
  exact ForestAlgebra.Character.convolution_unit_left (toCharacter a)

@[simp]
theorem ofCharacter_character_unit :
    ofCharacter (ForestAlgebra.Character.unit R) = unit R := by
  show ofCharacter (ForestAlgebra.counit R) = unit R
  rw [← Series.toCharacter_unit]
  exact ofCharacter_toCharacter unit_hasUnitConstant

theorem ofCharacter_convolution (χ ψ : ForestAlgebra.Character R) :
    ofCharacter (ForestAlgebra.Character.convolution χ ψ) =
      convolution (ofCharacter χ) (ofCharacter ψ) := by
  apply ext_of_toCharacter_eq
  · exact ofCharacter_hasUnitConstant _
  · exact convolution_hasUnitConstant _ _
  · rw [toCharacter_ofCharacter, toCharacter_convolution, toCharacter_ofCharacter,
      toCharacter_ofCharacter]

theorem ofCharacter_convolution_toCharacter (a b : Series R) :
    ofCharacter (ForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) =
      convolution a b := by
  apply ext_of_toCharacter_eq
  · exact ofCharacter_hasUnitConstant _
  · exact convolution_hasUnitConstant _ _
  · rw [toCharacter_ofCharacter, toCharacter_convolution]

@[simp]
theorem characterEquiv_unit :
    characterEquiv ⟨unit R, unit_hasUnitConstant⟩ = ForestAlgebra.Character.unit R := by
  show toCharacter (unit R) = ForestAlgebra.Character.unit R
  exact Series.toCharacter_unit

theorem characterEquiv_convolution
    (a b : {a : Series R // HasUnitConstant a}) :
    characterEquiv ⟨convolution a.1 b.1, convolution_hasUnitConstant a.1 b.1⟩ =
      ForestAlgebra.Character.convolution (characterEquiv a) (characterEquiv b) := by
  simp [toCharacter_convolution]

theorem characterEquiv_symm_convolution (χ ψ : ForestAlgebra.Character R) :
    ((characterEquiv (R := R)).symm (ForestAlgebra.Character.convolution χ ψ)).1 =
      convolution ((characterEquiv (R := R)).symm χ).1
        ((characterEquiv (R := R)).symm ψ).1 := by
  simp [ofCharacter_convolution]

theorem eq_convolution_of_toCharacter_eq {a b c : Series R} (hc : HasUnitConstant c)
    (h : toCharacter c =
      ForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) :
    c = convolution a b :=
  ext_of_toCharacter_eq hc (convolution_hasUnitConstant a b)
    (h.trans (toCharacter_convolution a b).symm)

theorem convolution_assoc_of_character_assoc {a b c : Series R}
    (hassoc :
      ForestAlgebra.Character.convolution
          (ForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) (toCharacter c) =
        ForestAlgebra.Character.convolution (toCharacter a)
          (ForestAlgebra.Character.convolution (toCharacter b) (toCharacter c))) :
    convolution (convolution a b) c = convolution a (convolution b c) := by
  apply ext_of_toCharacter_eq
  · exact convolution_hasUnitConstant _ _
  · exact convolution_hasUnitConstant _ _
  · rw [toCharacter_convolution, toCharacter_convolution, toCharacter_convolution,
      toCharacter_convolution]
    exact hassoc

theorem convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : ForestAlgebra R,
      ForestAlgebra.coproductLeft R x = ForestAlgebra.coproductRight R x)
    (a b c : Series R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (ForestAlgebra.Character.convolution_assoc_of_coproduct_eq
      (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc : ForestAlgebra.coproductLeft R = ForestAlgebra.coproductRight R)
    (a b c : Series R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (ForestAlgebra.Character.convolution_assoc_of_coproductLeft_eq_coproductRight
      (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc_of_nestedCoproductTerms
    (hcoassoc : ∀ t : PTree,
      ForestTripleTensorAlgebra.sumTerms (R := R) (PTree.nestedCoproductLeftTerms t) =
        ForestTripleTensorAlgebra.sumTerms (R := R) (PTree.nestedCoproductRightTerms t))
    (a b c : Series R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (ForestAlgebra.Character.convolution_assoc_of_nestedCoproductTerms
      (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc_of_nestedCoproductTerms_perm
    (hcoassoc : ∀ t : PTree,
      (PTree.nestedCoproductLeftTerms t).Perm (PTree.nestedCoproductRightTerms t))
    (a b c : Series R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_character_assoc
    (ForestAlgebra.Character.convolution_assoc_of_nestedCoproductTerms_perm
      (R := R) hcoassoc (toCharacter a) (toCharacter b) (toCharacter c))

theorem convolution_assoc (a b c : Series R) :
    convolution (convolution a b) c = convolution a (convolution b c) :=
  convolution_assoc_of_coproductLeft_eq_coproductRight
    (ForestAlgebra.coproductLeft_eq_coproductRight (R := R)) a b c

theorem agreeUpToOrder_convolution_assoc_of_character_assoc {a b c : Series R}
    (hassoc :
      ForestAlgebra.Character.convolution
          (ForestAlgebra.Character.convolution (toCharacter a) (toCharacter b)) (toCharacter c) =
        ForestAlgebra.Character.convolution (toCharacter a)
          (ForestAlgebra.Character.convolution (toCharacter b) (toCharacter c)))
    (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc_of_character_assoc hassoc) n

theorem agreeUpToOrder_convolution_assoc_of_coproduct_eq
    (hcoassoc : ∀ x : ForestAlgebra R,
      ForestAlgebra.coproductLeft R x = ForestAlgebra.coproductRight R x)
    (a b c : Series R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc_of_coproduct_eq hcoassoc a b c) n

theorem agreeUpToOrder_convolution_assoc_of_coproductLeft_eq_coproductRight
    (hcoassoc : ForestAlgebra.coproductLeft R = ForestAlgebra.coproductRight R)
    (a b c : Series R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq
    (convolution_assoc_of_coproductLeft_eq_coproductRight hcoassoc a b c) n

theorem agreeUpToOrder_convolution_assoc_of_nestedCoproductTerms_perm
    (hcoassoc : ∀ t : PTree,
      (PTree.nestedCoproductLeftTerms t).Perm (PTree.nestedCoproductRightTerms t))
    (a b c : Series R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc_of_nestedCoproductTerms_perm hcoassoc a b c) n

theorem agreeUpToOrder_convolution_assoc
    (a b c : Series R) (n : Nat) :
    AgreeUpToOrder (convolution (convolution a b) c) (convolution a (convolution b c)) n :=
  agreeUpToOrder_of_eq (convolution_assoc a b c) n

theorem convolution_tree_congr_of_agree {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n)
    {τ : RootedTree} (hτ : RootedTree.order τ ≤ n) :
    coeff (convolution a b) (.tree τ) = coeff (convolution a' b') (.tree τ) := by
  change
      forestConvolutionCoeff a b (RootedForest.singleton τ) =
      forestConvolutionCoeff a' b' (RootedForest.singleton τ)
  exact forestConvolutionCoeff_congr_of_agree ha hb (by simpa using hτ)

theorem convolution_tree_congr_left_of_agree {a a' b : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    {τ : RootedTree} → RootedTree.order τ ≤ n →
      coeff (convolution a b) (.tree τ) = coeff (convolution a' b) (.tree τ) :=
  convolution_tree_congr_of_agree ha (agreeUpToOrder_refl b n)

theorem convolution_tree_congr_right_of_agree {a b b' : Series R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    {τ : RootedTree} → RootedTree.order τ ≤ n →
      coeff (convolution a b) (.tree τ) = coeff (convolution a b') (.tree τ) :=
  convolution_tree_congr_of_agree (agreeUpToOrder_refl a n) hb

theorem agreeUpToOrder_convolution {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (convolution a b) (convolution a' b') n := by
  intro ξ hξ
  cases ξ with
  | empty =>
      rw [convolution_empty, convolution_empty]
  | tree τ =>
      exact convolution_tree_congr_of_agree ha hb hξ

theorem agreeUpToOrder_convolution_left {a a' b : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    AgreeUpToOrder (convolution a b) (convolution a' b) n :=
  agreeUpToOrder_convolution ha (agreeUpToOrder_refl b n)

theorem agreeUpToOrder_convolution_right {a b b' : Series R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    AgreeUpToOrder (convolution a b) (convolution a b') n :=
  agreeUpToOrder_convolution (agreeUpToOrder_refl a n) hb

theorem convolution_eq_of_agreeUpToOrder_all {a a' b b' : Series R}
    (ha : ∀ n, AgreeUpToOrder a a' n) (hb : ∀ n, AgreeUpToOrder b b' n) :
    convolution a b = convolution a' b' := by
  funext ξ
  cases ξ with
  | empty =>
      rfl
  | tree τ =>
      simpa [Series.coeff] using
        convolution_tree_congr_of_agree
          (ha (RootedTree.order τ)) (hb (RootedTree.order τ)) (τ := τ) le_rfl

theorem convolution_left_eq_of_agreeUpToOrder_all {a a' b : Series R}
    (ha : ∀ n, AgreeUpToOrder a a' n) :
    convolution a b = convolution a' b :=
  convolution_eq_of_agreeUpToOrder_all ha (fun n => agreeUpToOrder_refl b n)

theorem convolution_right_eq_of_agreeUpToOrder_all {a b b' : Series R}
    (hb : ∀ n, AgreeUpToOrder b b' n) :
    convolution a b = convolution a b' :=
  convolution_eq_of_agreeUpToOrder_all (fun n => agreeUpToOrder_refl a n) hb

theorem agreeUpToOrder_all_convolution {a a' b b' : Series R}
    (ha : ∀ n, AgreeUpToOrder a a' n) (hb : ∀ n, AgreeUpToOrder b b' n) :
    ∀ n, AgreeUpToOrder (convolution a b) (convolution a' b') n := by
  rw [agreeUpToOrder_all_iff_eq]
  exact convolution_eq_of_agreeUpToOrder_all ha hb

theorem agreeUpToOrder_all_convolution_left {a a' b : Series R}
    (ha : ∀ n, AgreeUpToOrder a a' n) :
    ∀ n, AgreeUpToOrder (convolution a b) (convolution a' b) n :=
  agreeUpToOrder_all_convolution ha (fun n => agreeUpToOrder_refl b n)

theorem agreeUpToOrder_all_convolution_right {a b b' : Series R}
    (hb : ∀ n, AgreeUpToOrder b b' n) :
    ∀ n, AgreeUpToOrder (convolution a b) (convolution a b') n :=
  agreeUpToOrder_all_convolution (fun n => agreeUpToOrder_refl a n) hb

theorem convolution_unit_right {a : Series R} (ha : HasUnitConstant a) :
    convolution a (unit R) = a := by
  funext τ
  cases τ with
  | empty =>
      exact ha.symm
  | tree τ =>
      change forestConvolutionCoeff a (unit R) (RootedForest.singleton τ) = a (.tree τ)
      simpa [Series.coeff] using
        forestConvolutionCoeff_unit_right a (RootedForest.singleton τ)

theorem convolution_unit_left {a : Series R} (ha : HasUnitConstant a) :
    convolution (unit R) a = a := by
  funext τ
  cases τ with
  | empty =>
      exact ha.symm
  | tree τ =>
      change forestConvolutionCoeff (unit R) a (RootedForest.singleton τ) = a (.tree τ)
      simpa [Series.coeff] using
        forestConvolutionCoeff_unit_left a (RootedForest.singleton τ)

noncomputable instance instUnitConstantMonoid :
    Monoid {a : Series R // HasUnitConstant a} where
  one := ⟨unit R, unit_hasUnitConstant⟩
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
    {a : Series R // HasUnitConstant a} ≃* ForestAlgebra.Character R where
  toEquiv := characterEquiv
  map_mul' a b := by
    change characterEquiv ⟨convolution a.1 b.1, convolution_hasUnitConstant a.1 b.1⟩ =
      ForestAlgebra.Character.convolution (characterEquiv a) (characterEquiv b)
    exact characterEquiv_convolution a b

@[simp]
theorem planarConvolutionForestCoeff_nil (a b : Series R) :
    planarConvolutionForestCoeff a b [] = 1 := by
  simp [planarConvolutionForestCoeff]

@[simp]
theorem planarConvolutionForestCoeff_cons (a b : Series R)
    (t : PTree) (ts : List PTree) :
    planarConvolutionForestCoeff a b (t :: ts) =
      planarConvolutionCoeff a b t * planarConvolutionForestCoeff a b ts := by
  simp [planarConvolutionForestCoeff, planarConvolutionCoeff]

theorem planarConvolutionForestCoeff_perm (a b : Series R)
    {ts us : List PTree} (h : ts.Perm us) :
    planarConvolutionForestCoeff a b ts = planarConvolutionForestCoeff a b us :=
  PTree.convolutionForestCoeff_perm (toCharacter a) (toCharacter b) h

theorem planarConvolutionForestCoeff_forall₂_perm (a b : Series R) :
    ∀ {ts us : List PTree}, List.Forall₂ PTree.Perm ts us →
      planarConvolutionForestCoeff a b ts = planarConvolutionForestCoeff a b us :=
  PTree.convolutionForestCoeff_forall₂_perm (toCharacter a) (toCharacter b)

end

section Field

variable {R : Type u} [Field R]

theorem convolution_hasOrder_zero (a b : Series R) :
    HasOrder (convolution a b) 0 := by
  rw [hasOrder_zero_iff]
  exact convolution_hasUnitConstant a b

theorem convolution_hasOrder_all_congr {a a' b b' : Series R}
    (ha : ∀ n, AgreeUpToOrder a a' n) (hb : ∀ n, AgreeUpToOrder b b' n) :
    (∀ n, HasOrder (convolution a b) n) ↔
      ∀ n, HasOrder (convolution a' b') n :=
  hasOrder_all_congr (agreeUpToOrder_all_convolution ha hb)

theorem convolution_hasOrder_congr {a a' b b' : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) (hb : AgreeUpToOrder b b' n) :
    HasOrder (convolution a b) n ↔ HasOrder (convolution a' b') n :=
  hasOrder_congr (agreeUpToOrder_convolution ha hb)

theorem convolution_hasOrder_all_congr_left {a a' b : Series R}
    (ha : ∀ n, AgreeUpToOrder a a' n) :
    (∀ n, HasOrder (convolution a b) n) ↔
      ∀ n, HasOrder (convolution a' b) n :=
  convolution_hasOrder_all_congr ha (fun n => agreeUpToOrder_refl b n)

theorem convolution_hasOrder_congr_left {a a' b : Series R} {n : Nat}
    (ha : AgreeUpToOrder a a' n) :
    HasOrder (convolution a b) n ↔ HasOrder (convolution a' b) n :=
  convolution_hasOrder_congr ha (agreeUpToOrder_refl b n)

theorem convolution_hasOrder_all_congr_right {a b b' : Series R}
    (hb : ∀ n, AgreeUpToOrder b b' n) :
    (∀ n, HasOrder (convolution a b) n) ↔
      ∀ n, HasOrder (convolution a b') n :=
  convolution_hasOrder_all_congr (fun n => agreeUpToOrder_refl a n) hb

theorem convolution_hasOrder_congr_right {a b b' : Series R} {n : Nat}
    (hb : AgreeUpToOrder b b' n) :
    HasOrder (convolution a b) n ↔ HasOrder (convolution a b') n :=
  convolution_hasOrder_congr (agreeUpToOrder_refl a n) hb

theorem convolution_unit_right_of_hasOrder {a : Series R} {n : Nat}
    (ha : HasOrder a n) : convolution a (unit R) = a :=
  convolution_unit_right ha.hasUnitConstant

theorem convolution_unit_left_of_hasOrder {a : Series R} {n : Nat}
    (ha : HasOrder a n) : convolution (unit R) a = a :=
  convolution_unit_left ha.hasUnitConstant

end Field

end Series

end BSeries
