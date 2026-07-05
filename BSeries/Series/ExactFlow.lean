/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Cuts.FlowIdentity
import BSeries.Series.SquareRoot

/-!
# The Flow Property of the Exact B-Series

The exact-flow B-series compose as a one-parameter group:
`B_h ∘ B_{h'} = B_{h+h'}`, i.e.

  `convolution (scaledExact h) (scaledExact h') = scaledExact (h + h')`,

by the flow identity for cuts. Consequently the exact solution's character is
an odd character: **the exact solution is a symmetric method**
(`isOdd_toCharacter_exact`), the fact underlying the order theory of
symmetric components (arXiv:2507.21006, Section 7; Butcher; HLW III.1).
-/

namespace BSeries

open HopfAlgebras

universe u

namespace Series

noncomputable section

variable {R : Type u}

private theorem flow_identity_tree [Field R] [CharZero R] (h h' : R)
    (t : PTree) :
    ((PTree.coproductTerms t).map fun term =>
      h ^ RootedForest.order term.1 *
        ((RootedForest.treeFactorial term.1 : R))⁻¹ *
        (h' ^ RootedForest.order term.2 *
          ((RootedForest.treeFactorial term.2 : R))⁻¹)).sum =
    (h + h') ^ PTree.order t * ((PTree.treeFactorial t : R))⁻¹ := by
  have hlist := PTree.flow_identity R h h' [t]
  have hmap : ((PTree.coproductTermsList [t]).map fun term =>
      h ^ RootedForest.order term.1 *
        ((RootedForest.treeFactorial term.1 : R))⁻¹ *
        (h' ^ RootedForest.order term.2 *
          ((RootedForest.treeFactorial term.2 : R))⁻¹)).sum =
      ((PTree.coproductTerms t).map fun term =>
        h ^ RootedForest.order term.1 *
          ((RootedForest.treeFactorial term.1 : R))⁻¹ *
          (h' ^ RootedForest.order term.2 *
            ((RootedForest.treeFactorial term.2 : R))⁻¹)).sum := by
    rw [show PTree.coproductTermsList [t] =
      PTree.multiplyCoproductTerms (PTree.coproductTerms t)
        [((0 : RootedForest), (0 : RootedForest))] from rfl]
    unfold PTree.multiplyCoproductTerms
    induction PTree.coproductTerms t with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.flatMap_cons, List.map_cons, List.map_nil,
          List.map_append, List.sum_append, List.sum_cons, List.sum_nil,
          add_zero] at ih ⊢
        rw [ih]
  rw [hmap] at hlist
  rw [hlist]
  have horder : PTree.orderList [t] = PTree.order t := by
    rw [PTree.orderList_cons, PTree.orderList_nil]
    omega
  have hfact : PTree.treeFactorialList [t] = PTree.treeFactorial t := by
    show PTree.treeFactorial t * PTree.treeFactorialList [] =
      PTree.treeFactorial t
    show PTree.treeFactorial t * 1 = PTree.treeFactorial t
    rw [mul_one]
  rw [horder, hfact]

/-- The flow property of the exact B-series: exact flows compose as a
one-parameter group, `B_h ∘ B_{h'} = B_{h+h'}` (Butcher; HLW III.1). -/
theorem convolution_scaledExact [Field R] [CharZero R] (h h' : R) :
    convolution (scaledExact h) (scaledExact h') = scaledExact (h + h') := by
  funext τ
  cases τ with
  | empty =>
      show (1 : R) = scaledExact (h + h') TreeIndex.empty
      rw [show scaledExact (h + h') TreeIndex.empty =
        (h + h') ^ TreeIndex.order TreeIndex.empty *
          ((TreeIndex.treeFactorial TreeIndex.empty : R))⁻¹ from rfl]
      simp [TreeIndex.order, TreeIndex.treeFactorial]
  | tree τ' =>
      rw [← RootedTree.ofPTree_out τ']
      have hconv := convolution_tree_ofPTree (scaledExact h)
        (scaledExact h') (Quotient.out τ')
      calc convolution (scaledExact h) (scaledExact h')
            (.tree (RootedTree.ofPTree (Quotient.out τ')))
          = planarConvolutionCoeff (scaledExact h) (scaledExact h')
              (Quotient.out τ') := hconv
        _ = ((PTree.coproductTerms (Quotient.out τ')).map fun term =>
              h ^ RootedForest.order term.1 *
                ((RootedForest.treeFactorial term.1 : R))⁻¹ *
                (h' ^ RootedForest.order term.2 *
                  ((RootedForest.treeFactorial term.2 : R))⁻¹)).sum := by
            rw [planarConvolutionCoeff, PTree.convolutionCoeff,
              PTree.evalCoproductTerms]
            refine congrArg List.sum (List.map_congr_left fun term _ => ?_)
            simp only [PTree.evalCoproductTerm]
            rw [toCharacter_evalForest, toCharacter_evalForest,
              forestCoeff_scaledExact, forestCoeff_scaledExact]
        _ = (h + h') ^ PTree.order (Quotient.out τ') *
              ((PTree.treeFactorial (Quotient.out τ') : R))⁻¹ :=
            flow_identity_tree h h' _
        _ = scaledExact (h + h')
              (.tree (RootedTree.ofPTree (Quotient.out τ'))) := rfl

/-- The exact flow composed with its time-reversal is the identity. -/
theorem convolution_exact_neg [Field R] [CharZero R] :
    convolution (exact R) (scaledExact (-1 : R)) = unit R := by
  have h := convolution_scaledExact (1 : R) (-1)
  rwa [scaledExact_one, add_neg_cancel, scaledExact_zero] at h

theorem convolution_neg_exact [Field R] [CharZero R] :
    convolution (scaledExact (-1 : R)) (exact R) = unit R := by
  have h := convolution_scaledExact (-1 : R) 1
  rwa [scaledExact_one, neg_add_cancel, scaledExact_zero] at h

/-- The canonical involution of the exact character is the time-reversed
exact flow. -/
theorem involution_toCharacter_exact [Field R] [CharZero R] :
    ForestAlgebra.Character.involution (toCharacter (exact R)) =
      toCharacter (scaledExact (-1 : R)) := by
  apply ForestAlgebra.Character.ext
  intro φ
  rw [ForestAlgebra.Character.involution_evalForest, toCharacter_evalForest,
    toCharacter_evalForest, forestCoeff_scaledExact]
  rw [show forestCoeff (exact R) φ =
    (1 : R) ^ RootedForest.order φ *
      ((RootedForest.treeFactorial φ : R))⁻¹ from by
    rw [← scaledExact_one, forestCoeff_scaledExact]]
  rw [one_pow, one_mul]

/--
The exact solution of an ODE is a symmetric method: its B-series character is
an odd character (arXiv:2507.21006, Section 7, `a = a*`).
-/
theorem isOdd_toCharacter_exact [Field R] [CharZero R] :
    ForestAlgebra.Character.IsOdd (toCharacter (exact R)) := by
  have hinv : ForestAlgebra.Character.involution (toCharacter (exact R)) =
      ForestAlgebra.Character.inverseCharacter (toCharacter (exact R)) := by
    refine ForestAlgebra.Character.convolution_inverse_unique ?_
      (ForestAlgebra.Character.convolution_inverseCharacter_right _)
    rw [involution_toCharacter_exact, ← toCharacter_convolution,
      convolution_neg_exact, toCharacter_unit]
    exact ForestAlgebra.Character.unit_eq_counit.symm
  unfold ForestAlgebra.Character.IsOdd
  rw [hinv]
  rfl

/-- Characters agree on any element supported in orders where they agree on
forests. -/
private theorem character_apply_eq_of_agree [Field R]
    {χ ξ : ForestAlgebra.Character R} {n : ℕ}
    (hagree : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ.evalForest φ = ξ.evalForest φ) {x : ForestAlgebra R}
    (hsupp : ∀ ψ ∈ x.support, RootedForest.order ψ ≤ n) :
    χ x = ξ x := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      show χ (0 : ForestAlgebra R) = ξ (0 : ForestAlgebra R)
      rw [map_zero, map_zero]
  | single_add ψ b f hψf hb ih =>
      have hsupport : (Finsupp.single ψ b + f).support =
          {ψ} ∪ f.support := by
        rw [Finsupp.support_add_eq (by
          rw [Finsupp.support_single ψ hb]
          simpa using hψf), Finsupp.support_single ψ hb]
      have hψn : RootedForest.order ψ ≤ n := by
        refine hsupp ψ ?_
        rw [hsupport]
        exact Finset.mem_union_left _ (Finset.mem_singleton_self ψ)
      have hfn : ∀ ψ' ∈ f.support, RootedForest.order ψ' ≤ n := by
        intro ψ' hψ'
        refine hsupp ψ' ?_
        rw [hsupport]
        exact Finset.mem_union_right _ hψ'
      have hsingle : (AddMonoidAlgebra.single ψ b : ForestAlgebra R) =
          b • ForestAlgebra.ofForest ψ := by
        rw [ForestAlgebra.ofForest, AddMonoidAlgebra.smul_single', mul_one]
      show χ ((AddMonoidAlgebra.single ψ b : ForestAlgebra R) +
          (id f : ForestAlgebra R)) =
        ξ ((AddMonoidAlgebra.single ψ b : ForestAlgebra R) +
          (id f : ForestAlgebra R))
      rw [map_add, map_add, hsingle, map_smul, map_smul]
      simp only [id_eq]
      rw [ih hfn]
      exact congrArg (· + ξ f)
        (congrArg (HSMul.hSMul b) (hagree ψ hψn))

/--
The adjoint preserves the order of a B-series method: if a character agrees
with the exact solution up to order `n`, so does its adjoint
(arXiv:2507.21006, Proposition 7.1(1), one direction).
-/
theorem adjointCharacter_agree_exact [Field R] [CharZero R]
    {χ : ForestAlgebra.Character R} {n : ℕ}
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ.evalForest φ = (toCharacter (exact R)).evalForest φ) :
    ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      (ForestAlgebra.Character.adjointCharacter χ).evalForest φ =
        (toCharacter (exact R)).evalForest φ := by
  intro φ hφ
  rw [ForestAlgebra.Character.adjointCharacter_evalForest]
  have hs : ∀ ψ ∈ (RootedForest.antipode (R := R) φ).support,
      RootedForest.order ψ ≤ n := fun ψ hψ => by
    rw [RootedForest.order_eq_of_mem_support_antipode hψ]
    exact hφ
  rw [character_apply_eq_of_agree h hs]
  have hodd := (ForestAlgebra.Character.isOdd_iff_adjointCharacter_eq
    (toCharacter (exact R))).1 isOdd_toCharacter_exact
  calc ((-1 : R) ^ RootedForest.order φ) *
        (toCharacter (exact R)) (RootedForest.antipode (R := R) φ)
      = (ForestAlgebra.Character.adjointCharacter
          (toCharacter (exact R))).evalForest φ :=
        (ForestAlgebra.Character.adjointCharacter_evalForest _ φ).symm
    _ = (toCharacter (exact R)).evalForest φ := by rw [hodd]

/--
A method and its adjoint have the same order: `ord(ψ) = ord(ψ*)`
(arXiv:2507.21006, Proposition 7.1(1)).
-/
theorem adjointCharacter_agree_exact_iff [Field R] [CharZero R]
    (χ : ForestAlgebra.Character R) (n : ℕ) :
    (∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ.evalForest φ = (toCharacter (exact R)).evalForest φ) ↔
    (∀ φ : RootedForest, RootedForest.order φ ≤ n →
      (ForestAlgebra.Character.adjointCharacter χ).evalForest φ =
        (toCharacter (exact R)).evalForest φ) := by
  constructor
  · exact adjointCharacter_agree_exact
  · intro h
    have h2 := adjointCharacter_agree_exact h
    rwa [ForestAlgebra.Character.adjointCharacter_adjointCharacter] at h2

/-- Order-agreement transports through the adjoint. -/
theorem adjointCharacter_evalForest_congr [Field R]
    {χ ξ : ForestAlgebra.Character R} {n : ℕ}
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ.evalForest φ = ξ.evalForest φ) :
    ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      (ForestAlgebra.Character.adjointCharacter χ).evalForest φ =
        (ForestAlgebra.Character.adjointCharacter ξ).evalForest φ := by
  intro φ hφ
  rw [ForestAlgebra.Character.adjointCharacter_evalForest,
    ForestAlgebra.Character.adjointCharacter_evalForest]
  have hs : ∀ ψ ∈ (RootedForest.antipode (R := R) φ).support,
      RootedForest.order ψ ≤ n := fun ψ hψ => by
    rw [RootedForest.order_eq_of_mem_support_antipode hψ]
    exact hφ
  rw [character_apply_eq_of_agree h hs]

/-- Order-agreement between two characters transports through the
adjoint. -/
theorem adjointCharacter_evalForest_congr_pair [Field R]
    {χ ξ : ForestAlgebra.Character R} {n : ℕ}
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ.evalForest φ = ξ.evalForest φ) :
    ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      (ForestAlgebra.Character.adjointCharacter χ).evalForest φ =
        (ForestAlgebra.Character.adjointCharacter ξ).evalForest φ := by
  intro φ hφ
  rw [ForestAlgebra.Character.adjointCharacter_evalForest,
    ForestAlgebra.Character.adjointCharacter_evalForest]
  congr 1
  exact character_apply_eq_of_agree h (fun ρ hρ => by
    rw [RootedForest.order_eq_of_mem_support_antipode hρ]
    exact hφ)

/-- Order-agreement transports through character convolution. -/
theorem convolution_evalForest_congr [Field R]
    {χ₁ χ₂ ξ₁ ξ₂ : ForestAlgebra.Character R} {n : ℕ}
    (h₁ : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ₁.evalForest φ = ξ₁.evalForest φ)
    (h₂ : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ₂.evalForest φ = ξ₂.evalForest φ) :
    ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      (ForestAlgebra.Character.convolution χ₁ χ₂).evalForest φ =
        (ForestAlgebra.Character.convolution ξ₁ ξ₂).evalForest φ := by
  intro φ hφ
  have hf := ForestAlgebra.LinearFunctional.AgreeUpToOrder.convolution
    (f := ForestAlgebra.LinearFunctional.ofCharacter χ₁)
    (f' := ForestAlgebra.LinearFunctional.ofCharacter ξ₁)
    (g := ForestAlgebra.LinearFunctional.ofCharacter χ₂)
    (g' := ForestAlgebra.LinearFunctional.ofCharacter ξ₂)
    (n := n) (fun φ' hφ' => h₁ φ' hφ') (fun φ' hφ' => h₂ φ' hφ') φ hφ
  rw [← ForestAlgebra.Character.linearFunctional_ofCharacter_convolution,
    ← ForestAlgebra.Character.linearFunctional_ofCharacter_convolution]
    at hf
  exact hf

/-- The square root of the canonical odd composition of the exact character
is the exact character. -/
private theorem sqrtCoeff_adjoint_exact [Field R] [CharZero R]
    [Invertible (2 : R)] (φ : RootedForest) :
    RootedForest.sqrtCoeff (ForestAlgebra.Character.convolution
      (ForestAlgebra.Character.adjointCharacter (toCharacter (exact R)))
      (toCharacter (exact R))) φ =
    (toCharacter (exact R)).evalForest φ := by
  have h := ForestAlgebra.Character.symmetricPart_of_isOdd
    (isOdd_toCharacter_exact (R := R))
  have h2 := congrArg (fun f : ForestAlgebra.LinearFunctional R =>
    f (ForestAlgebra.ofForest (R := R) φ)) h
  simp only [ForestAlgebra.Character.symmetricPart,
    ForestAlgebra.Character.sqrtFunctional_ofForest] at h2
  exact h2

/--
The symmetric component of a method has at least the order of the method:
if `ψ` agrees with the exact solution up to order `n`, so does `ψ⁻`
(arXiv:2507.21006, Propositions 7.1(3) and 7.2).
-/
theorem symmetricPart_agree_exact [Field R] [CharZero R] [Invertible (2 : R)]
    {ψ : ForestAlgebra.Character R} {n : ℕ}
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      ψ.evalForest φ = (toCharacter (exact R)).evalForest φ) :
    ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      ForestAlgebra.Character.symmetricPart ψ
          (ForestAlgebra.ofForest (R := R) φ) =
        (toCharacter (exact R)).evalForest φ := by
  intro φ hφ
  rw [ForestAlgebra.Character.symmetricPart,
    ForestAlgebra.Character.sqrtFunctional_ofForest]
  have hadj := adjointCharacter_evalForest_congr h
  have hconv := convolution_evalForest_congr hadj h
  rw [RootedForest.sqrtCoeff_congr n hconv φ hφ]
  exact sqrtCoeff_adjoint_exact φ

/-- Splitting a character convolution at the two boundary cuts. -/
theorem convolution_evalForest_boundary_split [Field R]
    (χ₁ χ₂ : ForestAlgebra.Character R) {τ : RootedForest} (hτne : τ ≠ 0) :
    (ForestAlgebra.Character.convolution χ₁ χ₂).evalForest τ =
      χ₂.evalForest τ + χ₁.evalForest τ +
        (((RootedForest.coproductTerms τ).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2).map fun term =>
          χ₁.evalForest term.1 * χ₂.evalForest term.2).sum := by
  have hs := RootedForest.sum_map_coproductTerms_split (R := R) hτne
    (fun term => χ₁.evalForest term.1 * χ₂.evalForest term.2)
  have h0 : (ForestAlgebra.Character.convolution χ₁ χ₂).evalForest τ =
      ((RootedForest.coproductTerms τ).map fun term =>
        χ₁.evalForest term.1 * χ₂.evalForest term.2).sum := by
    rw [show (ForestAlgebra.Character.convolution χ₁ χ₂).evalForest τ =
      ForestAlgebra.LinearFunctional.evalForest
        (ForestAlgebra.LinearFunctional.ofCharacter
          (ForestAlgebra.Character.convolution χ₁ χ₂)) τ from rfl,
      ForestAlgebra.Character.linearFunctional_ofCharacter_convolution,
      ForestAlgebra.LinearFunctional.evalForest_convolution]
    simp only [ForestAlgebra.LinearFunctional.evalForest_ofCharacter]
  rw [h0, hs]
  simp only [ForestAlgebra.Character.evalForest_zero, one_mul, mul_one]

/-- **The adjoint's defect at the first failing order**: if `ψ` agrees with
the exact solution up to order `n`, then at order `n + 1` the adjoint's
defect is `(-1)^n` times the defect of `ψ`
(arXiv:2507.21006, Section 7). -/
theorem adjointCharacter_eval_first_defect [Field R] [CharZero R]
    {ψ : ForestAlgebra.Character R} {n : ℕ}
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      ψ.evalForest φ = (toCharacter (exact R)).evalForest φ)
    {τ : RootedForest} (hτ : RootedForest.order τ = n + 1) :
    (ForestAlgebra.Character.adjointCharacter ψ).evalForest τ -
        (toCharacter (exact R)).evalForest τ =
      (-1 : R) ^ n *
        (ψ.evalForest τ - (toCharacter (exact R)).evalForest τ) := by
  classical
  set e : ForestAlgebra.Character R := toCharacter (exact R) with he
  have hτne : τ ≠ 0 := (RootedForest.order_pos_iff_ne_zero τ).1 (by omega)
  have hproper_sum : ψ (RootedForest.antipodeProperSum (R := R) τ) =
      e (RootedForest.antipodeProperSum (R := R) τ) := by
    rw [RootedForest.antipodeProperSum, map_list_sum, map_list_sum,
      List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
    have hleft : RootedForest.order term.1.1 ≤ n := by
      have := RootedForest.properCoproductTerms_left_order_lt term.2
      omega
    have hright : RootedForest.order term.1.2 ≤ n := by
      have := RootedForest.properCoproductTerms_right_order_lt term.2
      omega
    simp only [Function.comp_apply, map_mul]
    rw [character_apply_eq_of_agree h (fun ρ hρ => by
      rw [RootedForest.order_eq_of_mem_support_antipode hρ]
      exact hleft)]
    exact congrArg (_ * ·) (h term.1.2 hright)
  have hval : ∀ χ : ForestAlgebra.Character R,
      (ForestAlgebra.Character.adjointCharacter χ).evalForest τ =
        (-1 : R) ^ (n + 1) *
          (-χ.evalForest τ -
            χ (RootedForest.antipodeProperSum (R := R) τ)) := by
    intro χ
    rw [ForestAlgebra.Character.adjointCharacter_evalForest, hτ,
      RootedForest.antipode_eq_of_ne_zero hτne, map_sub, map_neg]
    rfl
  have he_odd : ForestAlgebra.Character.adjointCharacter e = e :=
    (ForestAlgebra.Character.isOdd_iff_adjointCharacter_eq e).1
      (isOdd_toCharacter_exact (R := R))
  have h1 := hval ψ
  have h2 := hval e
  rw [he_odd] at h2
  rw [h1, hproper_sum]
  have hpow : ((-1 : R)) ^ (n + 1) = (-1 : R) ^ n * (-1) := pow_succ _ _
  rw [hpow] at h2 ⊢
  linear_combination -h2

/--
**The symmetric component detects the leading defect**: if `ψ` agrees with
the exact solution up to an even order `n`, then at order `n + 1` the
symmetric component takes the same values as `ψ` itself. In particular a
method of order exactly `n` (with `n` even) has symmetric component of
order exactly `n` (arXiv:2507.21006, Section 7). -/
theorem symmetricPart_eval_first_defect [Field R] [CharZero R]
    [Invertible (2 : R)] {ψ : ForestAlgebra.Character R} {n : ℕ}
    (hn : Even n)
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      ψ.evalForest φ = (toCharacter (exact R)).evalForest φ)
    {τ : RootedForest} (hτ : RootedForest.order τ = n + 1) :
    ForestAlgebra.Character.symmetricPart ψ
      (ForestAlgebra.ofForest (R := R) τ) = ψ.evalForest τ := by
  classical
  set e : ForestAlgebra.Character R := toCharacter (exact R) with he
  have hτne : τ ≠ 0 := (RootedForest.order_pos_iff_ne_zero τ).1 (by omega)
  -- agreement of the square-root coefficients up to order n
  have hadj := adjointCharacter_evalForest_congr h
  have hconv := convolution_evalForest_congr hadj h
  have hσ := RootedForest.sqrtCoeff_congr n hconv
  have he_odd : ForestAlgebra.Character.adjointCharacter e = e :=
    (ForestAlgebra.Character.isOdd_iff_adjointCharacter_eq e).1
      (isOdd_toCharacter_exact (R := R))
  -- the adjoint's defect at order n + 1 equals the defect of ψ
  have hadj_defect :
      (ForestAlgebra.Character.adjointCharacter ψ).evalForest τ -
        e.evalForest τ = ψ.evalForest τ - e.evalForest τ := by
    simpa [hn.neg_one_pow, ← he] using adjointCharacter_eval_first_defect h hτ
  -- proper cross terms agree with the exact side
  have hcross : (((RootedForest.coproductTerms τ).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        (ForestAlgebra.Character.adjointCharacter ψ).evalForest term.1 *
          ψ.evalForest term.2).sum =
      (((RootedForest.coproductTerms τ).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        (ForestAlgebra.Character.adjointCharacter e).evalForest term.1 *
          e.evalForest term.2).sum := by
    refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
    obtain ⟨htm, htp⟩ := List.mem_filter.1 hterm
    have htp' : 0 < RootedForest.order term.1 ∧
        0 < RootedForest.order term.2 := by simpa using htp
    have horder := RootedForest.coproductTerms_order htm
    have hl : RootedForest.order term.1 ≤ n := by omega
    have hr : RootedForest.order term.2 ≤ n := by omega
    rw [hadj term.1 hl, h term.2 hr, he_odd]
  -- the square-root recursions at order n + 1
  have hτσ := RootedForest.two_mul_sqrtCoeff_add_proper
    (ForestAlgebra.Character.convolution
      (ForestAlgebra.Character.adjointCharacter ψ) ψ) hτne
  have hτσe := RootedForest.two_mul_sqrtCoeff_add_proper
    (ForestAlgebra.Character.convolution
      (ForestAlgebra.Character.adjointCharacter e) e) hτne
  -- proper square-root terms agree
  have hproper_σ : ((RootedForest.properCoproductTerms τ).map fun term =>
      RootedForest.sqrtCoeff (ForestAlgebra.Character.convolution
        (ForestAlgebra.Character.adjointCharacter ψ) ψ) term.1 *
      RootedForest.sqrtCoeff (ForestAlgebra.Character.convolution
        (ForestAlgebra.Character.adjointCharacter ψ) ψ) term.2).sum =
      ((RootedForest.properCoproductTerms τ).map fun term =>
      RootedForest.sqrtCoeff (ForestAlgebra.Character.convolution
        (ForestAlgebra.Character.adjointCharacter e) e) term.1 *
      RootedForest.sqrtCoeff (ForestAlgebra.Character.convolution
        (ForestAlgebra.Character.adjointCharacter e) e) term.2).sum := by
    refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
    have hl : RootedForest.order term.1 ≤ n := by
      have := RootedForest.properCoproductTerms_left_order_lt hterm
      omega
    have hr : RootedForest.order term.2 ≤ n := by
      have := RootedForest.properCoproductTerms_right_order_lt hterm
      omega
    rw [hσ term.1 hl, hσ term.2 hr]
  -- the exact side's square root is the exact character itself
  have hσe : ∀ φ : RootedForest,
      RootedForest.sqrtCoeff (ForestAlgebra.Character.convolution
        (ForestAlgebra.Character.adjointCharacter e) e) φ =
        e.evalForest φ := sqrtCoeff_adjoint_exact
  -- assemble
  rw [ForestAlgebra.Character.symmetricPart,
    ForestAlgebra.Character.sqrtFunctional_ofForest]
  have h2ne : (2 : R) ≠ 0 := two_ne_zero
  refine mul_left_cancel₀ h2ne ?_
  have hγψ := convolution_evalForest_boundary_split
    (ForestAlgebra.Character.adjointCharacter ψ) ψ hτne
  have hγe := convolution_evalForest_boundary_split
    (ForestAlgebra.Character.adjointCharacter e) e hτne
  rw [hγψ] at hτσ
  rw [hγe] at hτσe
  rw [hσe τ] at hτσe
  rw [hproper_σ] at hτσ
  rw [hcross] at hτσ
  have hAe : (ForestAlgebra.Character.adjointCharacter e).evalForest τ =
      e.evalForest τ := by rw [he_odd]
  linear_combination hτσ - hτσe + hadj_defect - hAe

/--
**Symmetric methods have even order**, in step form (Hairer–Nørsett–Wanner,
Theorem II.8.10; arXiv:2507.21006, Section 8): if a symmetric (odd) character
agrees with the exact solution up to an odd order `n`, the agreement extends
automatically to order `n + 1`.  Hence the finite order of a symmetric
B-series method is always even.
-/
theorem isOdd_agree_exact_succ [Field R] [CharZero R]
    {χ : ForestAlgebra.Character R}
    (hodd : ForestAlgebra.Character.IsOdd χ) {n : ℕ} (hn : Odd n)
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ n →
      χ.evalForest φ = (toCharacter (exact R)).evalForest φ) :
    ∀ φ : RootedForest, RootedForest.order φ ≤ n + 1 →
      χ.evalForest φ = (toCharacter (exact R)).evalForest φ := by
  intro φ hφ
  by_cases hle : RootedForest.order φ ≤ n
  · exact h φ hle
  push Not at hle
  have horder : RootedForest.order φ = n + 1 := le_antisymm hφ hle
  have hne : φ ≠ 0 := by
    intro h0
    rw [h0, RootedForest.order_zero] at horder
    exact Nat.succ_ne_zero n horder.symm
  have heven : Even (n + 1) := Odd.add_one hn
  -- for any odd character `ξ`, comparing with `ξ* = ξ` at the even order
  -- `n + 1` yields `2 ξ(φ) = -ξ(antipodeProperSum φ)`
  have hkey : ∀ ξ : ForestAlgebra.Character R,
      ForestAlgebra.Character.IsOdd ξ →
      2 * ξ.evalForest φ =
        -ξ (RootedForest.antipodeProperSum (R := R) φ) := by
    intro ξ hξ
    have hval : ξ.evalForest φ = ξ (RootedForest.antipode (R := R) φ) := by
      conv_lhs => rw [← (ForestAlgebra.Character.isOdd_iff_adjointCharacter_eq
        ξ).1 hξ]
      rw [ForestAlgebra.Character.adjointCharacter_evalForest, horder,
        heven.neg_one_pow, one_mul]
    have hrec : ξ (RootedForest.antipode (R := R) φ) =
        -ξ.evalForest φ -
          ξ (RootedForest.antipodeProperSum (R := R) φ) := by
      rw [RootedForest.antipode_eq_of_ne_zero hne, map_sub, map_neg]
      rfl
    linear_combination hval.trans hrec
  have hχ := hkey χ hodd
  have hexact := hkey (toCharacter (exact R)) (isOdd_toCharacter_exact (R := R))
  -- both proper-sum evaluations agree, since all proper cut components have
  -- order at most `n`
  have hsum : χ (RootedForest.antipodeProperSum (R := R) φ) =
      (toCharacter (exact R)) (RootedForest.antipodeProperSum (R := R) φ) := by
    rw [RootedForest.antipodeProperSum, map_list_sum, map_list_sum,
      List.map_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
    have hleft : RootedForest.order term.1.1 ≤ n := by
      have := RootedForest.properCoproductTerms_left_order_lt term.2
      omega
    have hright : RootedForest.order term.1.2 ≤ n := by
      have := RootedForest.properCoproductTerms_right_order_lt term.2
      omega
    simp only [Function.comp_apply, map_mul]
    rw [character_apply_eq_of_agree h (fun ψ hψ => by
      rw [RootedForest.order_eq_of_mem_support_antipode hψ]
      exact hleft)]
    exact congrArg (_ * ·) (h term.1.2 hright)
  rw [hsum] at hχ
  linear_combination (hχ - hexact) / 2

end

end Series

end BSeries
