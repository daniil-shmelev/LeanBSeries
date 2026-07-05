/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.SquareRoot

/-!
# n-th roots of characters

The general convolution roots of arXiv:2507.21006, Theorem 6.1: for every
character `ψ` and `n` with `n` invertible, there is a normalized functional
`ρ` with `ρ^{⋆n} = ψ`. The construction avoids iterated coproducts by a
single recursion on the pair (forest order, convolution power): unrolling
`ρ^{⋆(k+1)} = ρ ⋆ ρ^{⋆k}` through the boundary cuts gives

  `ρ^{⋆m}(φ) = m ρ(φ) + Σ_{k=2}^{m} Σ_{proper} ρ(P) ρ^{⋆(k-1)}(T)`,

so `ρ(φ)` is determined at level `m = n` by division, with all remaining
data of strictly smaller order.
-/

namespace BSeries

open HopfAlgebras

universe u

namespace RootedForest

open HopfAlgebras.RootedForest

open ForestAlgebra

noncomputable section

variable {R : Type u} [CommRing R]

/-- The joint data of an `n`-th root and its convolution powers:
`rootData ψ n k φ = ρ^{⋆k}(φ)` for the `n`-th root `ρ` of `ψ`. -/
noncomputable def rootData (ψ : Character R) (n : ℕ) [Invertible (n : R)] :
    ℕ → RootedForest → R := fun k φ => by
  classical
  exact
    if hφ : φ = 0 then 1
    else
      match k with
      | 0 => 0
      | 1 =>
          ⅟(n : R) * (ψ.evalForest φ -
            ∑ j ∈ Finset.range (n - 1),
              ((properCoproductTerms φ).attach.map fun term =>
                rootData ψ n 1 term.1.1 *
                  rootData ψ n (j + 1) term.1.2).sum)
      | (k' + 2) =>
          rootData ψ n 1 φ + rootData ψ n (k' + 1) φ +
            ((properCoproductTerms φ).attach.map fun term =>
              rootData ψ n 1 term.1.1 *
                rootData ψ n (k' + 1) term.1.2).sum
termination_by k φ => (RootedForest.order φ, k)
decreasing_by
  · exact Prod.Lex.left _ _ (properCoproductTerms_left_order_lt term.2)
  · exact Prod.Lex.left _ _ (properCoproductTerms_right_order_lt term.2)
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (properCoproductTerms_left_order_lt term.2)
  · exact Prod.Lex.left _ _ (properCoproductTerms_right_order_lt term.2)

variable (ψ : Character R) (n : ℕ) [Invertible (n : R)]

@[simp]
theorem rootData_zero_forest (k : ℕ) : rootData ψ n k 0 = 1 := by
  rw [rootData.eq_def]
  simp

theorem rootData_zero_of_ne {φ : RootedForest} (hφ : φ ≠ 0) :
    rootData ψ n 0 φ = 0 := by
  rw [rootData.eq_def]
  simp [hφ]

theorem rootData_one_of_ne {φ : RootedForest} (hφ : φ ≠ 0) :
    rootData ψ n 1 φ =
      ⅟(n : R) * (ψ.evalForest φ -
        ∑ j ∈ Finset.range (n - 1),
          ((properCoproductTerms φ).map fun term =>
            rootData ψ n 1 term.1 * rootData ψ n (j + 1) term.2).sum) := by
  rw [rootData.eq_def]
  simp only [dif_neg hφ]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact List.sum_attach_map (properCoproductTerms φ) fun term =>
    rootData ψ n 1 term.1 * rootData ψ n (j + 1) term.2

theorem rootData_succ_succ_of_ne (k : ℕ) {φ : RootedForest} (hφ : φ ≠ 0) :
    rootData ψ n (k + 2) φ =
      rootData ψ n 1 φ + rootData ψ n (k + 1) φ +
        ((properCoproductTerms φ).map fun term =>
          rootData ψ n 1 term.1 * rootData ψ n (k + 1) term.2).sum := by
  rw [rootData.eq_def]
  simp only [dif_neg hφ]
  congr 1
  exact List.sum_attach_map (properCoproductTerms φ) fun term =>
    rootData ψ n 1 term.1 * rootData ψ n (k + 1) term.2

/-- The unrolled power identity:
`ρ^{⋆m}(φ) = m ρ(φ) + Σ_{k=2}^{m} S_k(φ)` on non-empty forests. -/
theorem rootData_eq_smul_add (m : ℕ) {φ : RootedForest} (hφ : φ ≠ 0) :
    rootData ψ n (m + 1) φ =
      (m + 1 : ℕ) • rootData ψ n 1 φ +
        ∑ j ∈ Finset.range m,
          ((properCoproductTerms φ).map fun term =>
            rootData ψ n 1 term.1 * rootData ψ n (j + 1) term.2).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [rootData_succ_succ_of_ne ψ n m hφ, ih, Finset.sum_range_succ]
      simp only [nsmul_eq_mul]
      push_cast
      ring

/-- **The defining property of the `n`-th root data**: at level `n`, the
recursion inverts to `ρ^{⋆n}(φ) = ψ(φ)` (arXiv:2507.21006, Theorem 6.1,
the recursion step). -/
theorem rootData_top (hn : n ≠ 0) {φ : RootedForest} (hφ : φ ≠ 0) :
    rootData ψ n n φ = ψ.evalForest φ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)).symm⟩
  rw [rootData_eq_smul_add ψ (m + 1) m hφ, rootData_one_of_ne ψ (m + 1) hφ]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc,
    show ((m : R) + 1) * ⅟((m + 1 : ℕ) : R) =
      ((m + 1 : ℕ) : R) * ⅟((m + 1 : ℕ) : R) from by push_cast; ring,
    mul_invOf_self, one_mul]
  ring

end

end RootedForest

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

namespace Character

open HopfAlgebras.ForestAlgebra.Character

noncomputable section

variable {R : Type u} [CommRing R] (ψ : Character R) (n : ℕ)
  [Invertible (n : R)]

/-- The `n`-th root of a character, as a linear functional
(arXiv:2507.21006, Theorem 6.1). -/
noncomputable def nthRootFunctional : LinearFunctional R :=
  Finsupp.linearCombination R (RootedForest.rootData ψ n 1)

@[simp]
theorem nthRootFunctional_ofForest (φ : RootedForest) :
    nthRootFunctional ψ n (ofForest (R := R) φ) =
      RootedForest.rootData ψ n 1 φ := by
  rw [nthRootFunctional, ofForest]
  change (Finsupp.linearCombination R (RootedForest.rootData ψ n 1))
      (Finsupp.single φ (1 : R)) = RootedForest.rootData ψ n 1 φ
  rw [Finsupp.linearCombination_single]
  rw [one_smul]

/-- The convolution powers of the `n`-th root functional realize the
joint root data. -/
theorem evalForest_convolutionPower_nthRootFunctional :
    ∀ (k : ℕ) (φ : RootedForest),
      LinearFunctional.evalForest
        (LinearFunctional.convolutionPower (nthRootFunctional ψ n) (k + 1))
        φ = RootedForest.rootData ψ n (k + 1) φ
  | 0, φ => by
      rw [LinearFunctional.convolutionPower_succ,
        LinearFunctional.convolutionPower_zero,
        LinearFunctional.convolution_counit_right]
      show nthRootFunctional ψ n (ofForest (R := R) φ) = _
      rw [nthRootFunctional_ofForest]
  | k + 1, φ => by
      classical
      by_cases hφ : φ = 0
      · subst hφ
        rw [RootedForest.rootData_zero_forest]
        rw [LinearFunctional.convolutionPower_succ]
        rw [LinearFunctional.evalForest,
          LinearFunctional.convolution_ofForest,
          RootedForest.coproductTerms_zero]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        have h1 : nthRootFunctional ψ n (ofForest (R := R) 0) = 1 := by
          rw [nthRootFunctional_ofForest, RootedForest.rootData_zero_forest]
        have h2 := evalForest_convolutionPower_nthRootFunctional k 0
        rw [RootedForest.rootData_zero_forest] at h2
        rw [h1, one_mul]
        exact h2
      · rw [LinearFunctional.convolutionPower_succ,
          LinearFunctional.evalForest,
          LinearFunctional.convolution_ofForest,
          RootedForest.sum_map_coproductTerms_split (R := R) hφ]
        have hb1 : nthRootFunctional ψ n (ofForest (R := R) 0) *
            (LinearFunctional.convolutionPower (nthRootFunctional ψ n)
              (k + 1)) (ofForest (R := R) φ) =
            RootedForest.rootData ψ n (k + 1) φ := by
          rw [nthRootFunctional_ofForest, RootedForest.rootData_zero_forest,
            one_mul]
          exact evalForest_convolutionPower_nthRootFunctional k φ
        have hb2 : nthRootFunctional ψ n (ofForest (R := R) φ) *
            (LinearFunctional.convolutionPower (nthRootFunctional ψ n)
              (k + 1)) (ofForest (R := R) 0) =
            RootedForest.rootData ψ n 1 φ := by
          have h2 := evalForest_convolutionPower_nthRootFunctional k 0
          rw [RootedForest.rootData_zero_forest] at h2
          rw [nthRootFunctional_ofForest]
          rw [show (LinearFunctional.convolutionPower (nthRootFunctional ψ n)
            (k + 1)) (ofForest (R := R) 0) = 1 from h2, mul_one]
        have hfil : (((RootedForest.coproductTerms φ).filter fun term =>
            0 < RootedForest.order term.1 ∧
              0 < RootedForest.order term.2).map fun term =>
            nthRootFunctional ψ n (ofForest (R := R) term.1) *
              (LinearFunctional.convolutionPower (nthRootFunctional ψ n)
                (k + 1)) (ofForest (R := R) term.2)).sum =
            (((RootedForest.coproductTerms φ).filter fun term =>
            0 < RootedForest.order term.1 ∧
              0 < RootedForest.order term.2).map fun term =>
            RootedForest.rootData ψ n 1 term.1 *
              RootedForest.rootData ψ n (k + 1) term.2).sum := by
          refine congrArg List.sum (List.map_congr_left fun term hterm => ?_)
          rw [nthRootFunctional_ofForest]
          exact congrArg (_ * ·)
            (evalForest_convolutionPower_nthRootFunctional k term.2)
        rw [hb1, hb2, hfil]
        -- match against the recursion; the proper sums differ only in the
        -- filtered presentation
        rw [RootedForest.rootData_succ_succ_of_ne ψ n k hφ]
        rw [show ((RootedForest.coproductTerms φ).filter fun term =>
          0 < RootedForest.order term.1 ∧
            0 < RootedForest.order term.2) =
          RootedForest.properCoproductTerms φ from rfl]
        ring

/-- **Existence of `n`-th convolution roots** (arXiv:2507.21006,
Theorem 6.1): the `n`-th power of the root functional is the character. -/
theorem convolutionPower_nthRootFunctional (hn : n ≠ 0) :
    LinearFunctional.convolutionPower (nthRootFunctional ψ n) n =
      LinearFunctional.ofCharacter ψ := by
  classical
  apply LinearFunctional.ext_evalForest
  intro φ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)).symm⟩
  rw [evalForest_convolutionPower_nthRootFunctional]
  by_cases hφ : φ = 0
  · subst hφ
    rw [RootedForest.rootData_zero_forest]
    show (1 : R) = ψ (ofForest (R := R) 0)
    rw [ofForest_zero, map_one]
  · rw [RootedForest.rootData_top ψ (m + 1) (Nat.succ_ne_zero m) hφ]
    rfl

end

end Character

end ForestAlgebra

end BSeries
