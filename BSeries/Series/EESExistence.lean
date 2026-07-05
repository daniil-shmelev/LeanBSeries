/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.EES
import BSeries.Numerics.Enumeration
import BSeries.Numerics.ExplicitDensity
import BSeries.Numerics.Reindex

/-!
# Construction of characters with prescribed exact orders

The two building blocks of the existence theorem for EES schemes
(arXiv:2507.21006, Section 8): for every even `n` there is an **odd**
character agreeing with the exact solution up to order `n` but not `n + 1`
(a symmetric method of order exactly `n`), and for every odd `m` there is
an **even** character whose antisymmetric order is exactly `m`.

Both are obtained from Butcher's density theorem 317A: prescribe the
elementary weights `1/τ!` up to the target order and introduce a deliberate
defect one order higher, then pass to the symmetric or antisymmetric
component; the defect-transfer lemmas show the defect survives.
-/

namespace BSeries

open HopfAlgebras

/-- The chain (tall) tree of order `k + 1`. -/
def PTree.tallTree : ℕ → PTree
  | 0 => .node []
  | k + 1 => .node [tallTree k]

open HopfAlgebras.PTree in
theorem PTree.order_tallTree : ∀ k, PTree.order (PTree.tallTree k) = k + 1
  | 0 => rfl
  | k + 1 => by
      rw [tallTree, order_node, orderList_cons, orderList_nil,
        order_tallTree k]
      omega

namespace ForestAlgebra

open HopfAlgebras.ForestAlgebra

namespace Character

open HopfAlgebras.ForestAlgebra.Character

universe w

noncomputable section

variable {R : Type w}

/-- The witness forest of order `n + 1`: a single chain tree. -/
private def tallForest (n : ℕ) : RootedForest :=
  RootedForest.singleton (RootedTree.ofPTree (PTree.tallTree n))

private theorem order_tallForest (n : ℕ) :
    RootedForest.order (tallForest n) = n + 1 := by
  rw [tallForest, RootedForest.order_singleton, RootedTree.order_ofPTree,
    PTree.order_tallTree]

/-- A Runge–Kutta character of order exactly `k`: it matches the exact
weights up to order `k` and has a deliberate defect `+1` at every tree of
order `k + 1`. -/
private theorem exists_character_agree_defect (R : Type w) [Field R]
    [CharZero R] (k : ℕ) :
    ∃ ψ : Character R,
      (∀ ρ : RootedForest, RootedForest.order ρ ≤ k →
        ψ.evalForest ρ =
          (Series.toCharacter (Series.exact R)).evalForest ρ) ∧
      ψ.evalForest (tallForest k) =
        (Series.toCharacter (Series.exact R)).evalForest (tallForest k)
          + 1 := by
  classical
  obtain ⟨ι, hι, rk, hrk⟩ := RungeKutta.exists_rk_forall_treeWeight
    (RootedTree.treesUpToOrder (k + 1))
    (fun τ => if RootedTree.order τ ≤ k
      then (RootedTree.treeFactorial τ : R)⁻¹
      else (RootedTree.treeFactorial τ : R)⁻¹ + 1)
  refine ⟨Series.toCharacter (RungeKutta.series rk), ?_, ?_⟩
  · have hord : RungeKutta.HasOrder rk k := by
      rw [RungeKutta.hasOrder_iff_treeWeight]
      intro τ hτ
      rw [hrk τ (RootedTree.mem_treesUpToOrder (le_trans hτ (Nat.le_succ k))),
        if_pos hτ]
    have h1 := (RungeKutta.hasOrder_iff_toCharacter_evalForest rk k).1 hord
    intro ρ hρ
    rw [h1 ρ hρ]
    exact (Series.toCharacter_exact_ofForest ρ).symm
  · have hτmem : RootedTree.ofPTree (PTree.tallTree k) ∈
        RootedTree.treesUpToOrder (k + 1) := by
      refine RootedTree.mem_treesUpToOrder ?_
      rw [RootedTree.order_ofPTree, PTree.order_tallTree]
    have hτord : ¬ RootedTree.order (RootedTree.ofPTree (PTree.tallTree k))
        ≤ k := by
      rw [RootedTree.order_ofPTree, PTree.order_tallTree]
      omega
    have hval := hrk _ hτmem
    rw [if_neg hτord] at hval
    have hw : (Series.toCharacter (RungeKutta.series rk)).evalForest
        (tallForest k) = RungeKutta.treeWeight rk
          (RootedTree.ofPTree (PTree.tallTree k)) := by
      rw [tallForest, RungeKutta.toCharacter_series_evalForest,
        RungeKutta.forestWeight_singleton]
    have hexact : (Series.toCharacter (Series.exact R)).evalForest
        (tallForest k) =
        (RootedTree.treeFactorial (RootedTree.ofPTree (PTree.tallTree k))
          : R)⁻¹ := by
      rw [show (Series.toCharacter (Series.exact R)).evalForest
        (tallForest k) = Series.toCharacter (Series.exact R)
          (ForestAlgebra.ofForest (R := R) (tallForest k)) from rfl,
        Series.toCharacter_exact_ofForest, tallForest,
        RootedForest.treeFactorial_singleton]
    rw [hw, hval, hexact]

/-- **Symmetric methods of every even order exist, sharply**: for even `n`
there is an odd character agreeing with the exact solution up to order `n`
and failing at order `n + 1` (arXiv:2507.21006, Section 8). -/
theorem exists_isOdd_agree_defect (R : Type w) [Field R] [CharZero R]
    [Invertible (2 : R)] {n : ℕ} (hn : Even n) :
    ∃ φ : Character R, IsOdd φ ∧
      (∀ ρ : RootedForest, RootedForest.order ρ ≤ n →
        φ.evalForest ρ =
          (Series.toCharacter (Series.exact R)).evalForest ρ) ∧
      ∃ τ : RootedForest, RootedForest.order τ = n + 1 ∧
        φ.evalForest τ ≠
          (Series.toCharacter (Series.exact R)).evalForest τ := by
  obtain ⟨ψ, hagree, hdefect⟩ := exists_character_agree_defect R n
  have hφeval : ∀ ρ : RootedForest, (symmetricPartChar ψ).evalForest ρ =
      symmetricPart ψ (ofForest (R := R) ρ) := fun ρ => by
    rw [show (symmetricPartChar ψ).evalForest ρ =
      LinearFunctional.ofCharacter (symmetricPartChar ψ)
        (ofForest (R := R) ρ) from rfl, ofCharacter_symmetricPartChar]
  refine ⟨symmetricPartChar ψ, isOdd_symmetricPartChar ψ, ?_,
    tallForest n, order_tallForest n, ?_⟩
  · intro ρ hρ
    rw [hφeval ρ]
    exact Series.symmetricPart_agree_exact hagree ρ hρ
  · rw [hφeval, Series.symmetricPart_eval_first_defect hn hagree
      (order_tallForest n), hdefect]
    intro heq
    have : (1 : R) = 0 := by linear_combination heq
    exact one_ne_zero this

/-- **Even characters of every odd antisymmetric order exist, sharply**:
for odd `m` there is an even character whose antisymmetric component (which
is itself) vanishes up to order `m` and fails at order `m + 1`
(arXiv:2507.21006, Section 8). -/
theorem exists_isEven_antisym_defect (R : Type w) [Field R] [CharZero R]
    [Invertible (2 : R)] {m : ℕ} (hm : Odd m) :
    ∃ ζ : Character R, IsEven ζ ∧
      (∀ ρ : RootedForest, RootedForest.order ρ ≤ m →
        ζ.evalForest ρ = LinearFunctional.evalForest
          (LinearFunctional.counit R) ρ) ∧
      ∃ τ : RootedForest, RootedForest.order τ = m + 1 ∧
        ζ.evalForest τ ≠ LinearFunctional.evalForest
          (LinearFunctional.counit R) τ := by
  obtain ⟨ψ, hagree, hdefect⟩ := exists_character_agree_defect R m
  have hζeval : ∀ ρ : RootedForest, (antisymmetricPartChar ψ).evalForest ρ =
      antisymmetricPart ψ (ofForest (R := R) ρ) := fun ρ => by
    rw [show (antisymmetricPartChar ψ).evalForest ρ =
      LinearFunctional.ofCharacter (antisymmetricPartChar ψ)
        (ofForest (R := R) ρ) from rfl, ofCharacter_antisymmetricPartChar]
  have hζeven : IsEven (antisymmetricPartChar ψ) := by
    apply linearFunctional_ofCharacter_injective
    rw [ofCharacter_involution, ofCharacter_antisymmetricPartChar,
      compGradingInvolution_antisymmetricPart]
  refine ⟨antisymmetricPartChar ψ, hζeven, ?_, tallForest m,
    order_tallForest m, ?_⟩
  · intro ρ hρ
    rw [hζeval ρ]
    exact hasAntisymOrder_of_agree_exact hagree ρ hρ
  · rw [hζeval, antisymmetricPart_eval_first_defect hm hagree
      (order_tallForest m), hdefect,
      LinearFunctional.evalForest_counit]
    have hτne : tallForest m ≠ 0 := by
      intro h0
      have := order_tallForest m
      rw [h0, RootedForest.order_zero] at this
      exact Nat.succ_ne_zero m this.symm
    classical
    rw [show ForestAlgebra.counitCoeff (R := R) (tallForest m) = 0 from by
      simp [ForestAlgebra.counitCoeff, hτne]]
    intro heq
    have : (1 : R) = 0 := by linear_combination heq
    exact one_ne_zero this

/-- **Existence of EES characters** (arXiv:2507.21006, Section 8, the core
of the existence theorem): for even `n` and odd `m > n` there is a
character of order exactly `n` whose antisymmetric order is exactly `m`,
namely `γ = ζ ⋆ φ` for the constructed even `ζ` and odd `φ`. -/
theorem exists_character_ees_orders (R : Type w) [Field R] [CharZero R]
    [Invertible (2 : R)] {n m : ℕ} (hn : Even n) (hm : Odd m)
    (hnm : n < m) :
    ∃ γ : Character R,
      (∀ ρ : RootedForest, RootedForest.order ρ ≤ n →
        γ.evalForest ρ =
          (Series.toCharacter (Series.exact R)).evalForest ρ) ∧
      (∃ τ : RootedForest, RootedForest.order τ = n + 1 ∧
        γ.evalForest τ ≠
          (Series.toCharacter (Series.exact R)).evalForest τ) ∧
      HasAntisymOrder γ m ∧ ¬ HasAntisymOrder γ (m + 1) := by
  obtain ⟨φ, hφodd, hφagree, τφ, hτφ, hφdef⟩ := exists_isOdd_agree_defect R hn
  obtain ⟨ζ, hζeven, hζagree, τζ, hτζ, hζdef⟩ :=
    exists_isEven_antisym_defect R hm
  set γ : Character R := convolution ζ φ with hγ
  have he_norm : LinearFunctional.ofCharacter ζ (ofForest (R := R) 0) = 1 := by
    show ζ (ofForest (R := R) 0) = 1
    rw [ofForest_zero]
    exact map_one ζ
  have ho_norm : LinearFunctional.ofCharacter φ (ofForest (R := R) 0) = 1 := by
    show φ (ofForest (R := R) 0) = 1
    rw [ofForest_zero]
    exact map_one φ
  have he : LinearFunctional.compGradingInvolution
      (LinearFunctional.ofCharacter ζ) = LinearFunctional.ofCharacter ζ := by
    rw [← ofCharacter_involution, hζeven]
  have ho : LinearFunctional.convolution
      (LinearFunctional.compGradingInvolution
        (LinearFunctional.ofCharacter φ)) (LinearFunctional.ofCharacter φ) =
      LinearFunctional.counit R := by
    rw [← ofCharacter_involution]
    have hinv : involution φ = inverseCharacter φ :=
      linearFunctional_ofCharacter_injective (by
        rw [ofCharacter_inverseCharacter]
        exact hφodd)
    rw [hinv, ← linearFunctional_ofCharacter_convolution,
      convolution_inverseCharacter_left, linearFunctional_ofCharacter_unit]
  have hdec : LinearFunctional.convolution (LinearFunctional.ofCharacter ζ)
      (LinearFunctional.ofCharacter φ) = LinearFunctional.ofCharacter γ := by
    rw [← linearFunctional_ofCharacter_convolution]
  have hanti : LinearFunctional.ofCharacter ζ = antisymmetricPart γ :=
    antisymmetricPart_unique γ he_norm ho_norm he ho hdec
  -- γ agrees with φ up to order m
  have hγφ : ∀ ρ : RootedForest, RootedForest.order ρ ≤ m →
      γ.evalForest ρ = φ.evalForest ρ := by
    have hζfun : LinearFunctional.AgreeUpToOrder
        (LinearFunctional.ofCharacter ζ) (LinearFunctional.counit R) m := by
      intro ρ hρ
      exact hζagree ρ hρ
    have hconv := LinearFunctional.AgreeUpToOrder.convolution hζfun
      (LinearFunctional.agreeUpToOrder_refl
        (LinearFunctional.ofCharacter φ) m)
    intro ρ hρ
    have h1 := hconv ρ hρ
    rw [hdec, LinearFunctional.convolution_counit_left] at h1
    exact h1
  refine ⟨γ, ?_, ⟨τφ, hτφ, ?_⟩, ?_, ?_⟩
  · intro ρ hρ
    rw [hγφ ρ (le_trans hρ (le_of_lt hnm)), hφagree ρ hρ]
  · rw [hγφ τφ (by omega)]
    exact hφdef
  · intro ρ hρ
    rw [show LinearFunctional.evalForest (antisymmetricPart γ) ρ =
      antisymmetricPart γ (ofForest (R := R) ρ) from rfl, ← hanti]
    exact hζagree ρ hρ
  · intro hcon
    have h1 := hcon τζ (le_of_eq hτζ)
    rw [show LinearFunctional.evalForest (antisymmetricPart γ) τζ =
      antisymmetricPart γ (ofForest (R := R) τζ) from rfl, ← hanti] at h1
    exact hζdef h1

/-- Characters agreeing on all trees of order at most `n` agree on all
forests of order at most `n` (characters are multiplicative). -/
theorem evalForest_congr_of_tree_congr [CommRing R] {χ ξ : Character R}
    {n : ℕ}
    (h : ∀ τ : RootedTree, RootedTree.order τ ≤ n →
      χ.evalForest (RootedForest.singleton τ) =
        ξ.evalForest (RootedForest.singleton τ)) :
    ∀ ρ : RootedForest, RootedForest.order ρ ≤ n →
      χ.evalForest ρ = ξ.evalForest ρ := by
  intro ρ
  induction ρ using Multiset.induction_on with
  | empty =>
      intro _
      rw [show ((0 : Multiset RootedTree) : RootedForest) =
        (0 : RootedForest) from rfl]
      rw [Character.evalForest_zero, Character.evalForest_zero]
  | cons τ s ih =>
      intro hρ
      have hsplit : (τ ::ₘ s : RootedForest) =
          RootedForest.singleton τ + s := rfl
      rw [hsplit, Character.evalForest_add, Character.evalForest_add]
      have horder : RootedForest.order (RootedForest.singleton τ) +
          RootedForest.order (s : RootedForest) ≤ n := by
        rw [← RootedForest.order_add, ← hsplit]
        exact hρ
      have hτn : RootedTree.order τ ≤ n := by
        have := RootedForest.order_singleton τ
        omega
      have hsn : RootedForest.order (s : RootedForest) ≤ n := by omega
      rw [h τ hτn, ih hsn]

/-- Order-agreement between two characters transports to their
antisymmetric components. -/
theorem antisymmetricPart_evalForest_congr [Field R] [Invertible (2 : R)]
    {χ ξ : Character R} {k : ℕ}
    (h : ∀ φ : RootedForest, RootedForest.order φ ≤ k →
      χ.evalForest φ = ξ.evalForest φ) :
    ∀ ρ : RootedForest, RootedForest.order ρ ≤ k →
      antisymmetricPart χ (ofForest (R := R) ρ) =
        antisymmetricPart ξ (ofForest (R := R) ρ) := by
  have hadj := Series.adjointCharacter_evalForest_congr_pair h
  have hconv := Series.convolution_evalForest_congr hadj h
  have hσ := RootedForest.sqrtCoeff_congr k hconv
  intro ρ hρ
  have hg : LinearFunctional.AgreeUpToOrder
      (LinearFunctional.compGradingInvolution (symmetricPart χ))
      (LinearFunctional.compGradingInvolution (symmetricPart ξ)) k := by
    intro φ hφ
    rw [LinearFunctional.evalForest,
      LinearFunctional.compGradingInvolution_ofForest,
      LinearFunctional.evalForest,
      LinearFunctional.compGradingInvolution_ofForest,
      symmetricPart, sqrtFunctional_ofForest,
      symmetricPart, sqrtFunctional_ofForest, hσ φ hφ]
  have hf : LinearFunctional.AgreeUpToOrder
      (LinearFunctional.ofCharacter χ) (LinearFunctional.ofCharacter ξ)
      k := fun φ hφ => h φ hφ
  exact LinearFunctional.AgreeUpToOrder.convolution hf hg ρ hρ

/-- **Existence of Runge–Kutta methods with EES orders**
(arXiv:2507.21006, Section 8, Existence of EES Runge–Kutta Schemes,
without the explicitness refinement): for every even `n > 0` and odd
`m > n` there is a Runge–Kutta method of order exactly `n` whose
antisymmetric order is exactly `m`. -/
theorem exists_rk_ees_orders (R : Type w) [Field R] [CharZero R]
    [Invertible (2 : R)] {n m : ℕ} (hn : Even n) (hm : Odd m)
    (hnm : n < m) :
    ∃ (ι : Type) (_ : Fintype ι) (rk : RungeKutta ι R),
      (RungeKutta.HasOrder rk n ∧ ¬ RungeKutta.HasOrder rk (n + 1)) ∧
      (HasAntisymOrder (Series.toCharacter (RungeKutta.series rk)) m ∧
        ¬ HasAntisymOrder (Series.toCharacter (RungeKutta.series rk))
          (m + 1)) := by
  classical
  obtain ⟨γ, hγagree, ⟨τφ, hτφ, hγdef⟩, hγanti, hγnot⟩ :=
    exists_character_ees_orders R hn hm hnm
  -- match γ by a Runge–Kutta scheme through order m + 1
  obtain ⟨ι, hι, rk, hrk⟩ := RungeKutta.exists_rk_forall_treeWeight
    (RootedTree.treesUpToOrder (m + 1))
    (fun τ => γ.evalForest (RootedForest.singleton τ))
  set ψ : Character R := Series.toCharacter (RungeKutta.series rk) with hψ
  have htree : ∀ τ : RootedTree, RootedTree.order τ ≤ m + 1 →
      ψ.evalForest (RootedForest.singleton τ) =
        γ.evalForest (RootedForest.singleton τ) := by
    intro τ hτ
    rw [hψ, RungeKutta.toCharacter_series_evalForest,
      RungeKutta.forestWeight_singleton]
    exact hrk τ (RootedTree.mem_treesUpToOrder hτ)
  have hforest := evalForest_congr_of_tree_congr htree
  have hanti := antisymmetricPart_evalForest_congr hforest
  refine ⟨ι, hι, rk, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [RungeKutta.hasOrder_iff_toCharacter_evalForest]
    intro ρ hρ
    have h1 := hforest ρ (by omega)
    have h2 := hγagree ρ hρ
    rw [show (Series.toCharacter (Series.exact R)).evalForest ρ =
      Series.toCharacter (Series.exact R)
        (ForestAlgebra.ofForest (R := R) ρ) from rfl,
      Series.toCharacter_exact_ofForest] at h2
    rw [← h2, ← h1]
  · intro hcon
    rw [RungeKutta.hasOrder_iff_toCharacter_evalForest] at hcon
    have h1 := hcon τφ (le_of_eq hτφ)
    have h2 := hforest τφ (by omega)
    refine hγdef ?_
    rw [show (Series.toCharacter (Series.exact R)).evalForest τφ =
      Series.toCharacter (Series.exact R)
        (ForestAlgebra.ofForest (R := R) τφ) from rfl,
      Series.toCharacter_exact_ofForest]
    rw [← h2]
    exact h1
  · intro ρ hρ
    rw [show LinearFunctional.evalForest (antisymmetricPart ψ) ρ =
      antisymmetricPart ψ (ofForest (R := R) ρ) from rfl,
      hanti ρ (by omega)]
    exact hγanti ρ hρ
  · intro hcon
    refine hγnot ?_
    intro ρ hρ
    have h1 := hcon ρ hρ
    rw [show LinearFunctional.evalForest (antisymmetricPart ψ) ρ =
      antisymmetricPart ψ (ofForest (R := R) ρ) from rfl,
      hanti ρ hρ] at h1
    exact h1

/-- **Existence of EES Runge–Kutta schemes**
(arXiv:2507.21006, Section 8, Theorem "Existence of EES Runge–Kutta
Schemes"): for every even `n > 0` and every odd `m > n` there is an
explicit Runge–Kutta scheme belonging to `EES(n, m)`. -/
theorem exists_isEES (R : Type w) [Field R] [CharZero R]
    [Invertible (2 : R)] {n m : ℕ} (hn : Even n) (hm : Odd m)
    (hnm : n < m) :
    ∃ (ι : Type) (_ : LinearOrder ι) (_ : Fintype ι)
      (rk : RungeKutta ι R), RungeKutta.IsEES rk n m := by
  classical
  obtain ⟨γ, hγagree, ⟨τφ, hτφ, hγdef⟩, hγanti, hγnot⟩ :=
    exists_character_ees_orders R hn hm hnm
  obtain ⟨ι, hlo, hι, rk, hexp, hrk⟩ :=
    RungeKutta.exists_explicit_rk_forall_treeWeight
      (RootedTree.treesUpToOrder (m + 1))
      (fun τ => γ.evalForest (RootedForest.singleton τ))
  set ψ : Character R := Series.toCharacter (RungeKutta.series rk) with hψ
  have htree : ∀ τ : RootedTree, RootedTree.order τ ≤ m + 1 →
      ψ.evalForest (RootedForest.singleton τ) =
        γ.evalForest (RootedForest.singleton τ) := by
    intro τ hτ
    rw [hψ, RungeKutta.toCharacter_series_evalForest,
      RungeKutta.forestWeight_singleton]
    exact hrk τ (RootedTree.mem_treesUpToOrder hτ)
  have hforest := evalForest_congr_of_tree_congr htree
  have hanti := antisymmetricPart_evalForest_congr hforest
  refine ⟨ι, hlo, hι, rk, hexp, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [RungeKutta.hasOrder_iff_toCharacter_evalForest]
    intro ρ hρ
    have h1 := hforest ρ (by omega)
    have h2 := hγagree ρ hρ
    rw [show (Series.toCharacter (Series.exact R)).evalForest ρ =
      Series.toCharacter (Series.exact R)
        (ForestAlgebra.ofForest (R := R) ρ) from rfl,
      Series.toCharacter_exact_ofForest] at h2
    rw [← h2, ← h1]
  · intro hcon
    rw [RungeKutta.hasOrder_iff_toCharacter_evalForest] at hcon
    have h1 := hcon τφ (le_of_eq hτφ)
    have h2 := hforest τφ (by omega)
    refine hγdef ?_
    rw [show (Series.toCharacter (Series.exact R)).evalForest τφ =
      Series.toCharacter (Series.exact R)
        (ForestAlgebra.ofForest (R := R) τφ) from rfl,
      Series.toCharacter_exact_ofForest]
    rw [← h2]
    exact h1
  · intro ρ hρ
    rw [show LinearFunctional.evalForest (antisymmetricPart ψ) ρ =
      antisymmetricPart ψ (ofForest (R := R) ρ) from rfl,
      hanti ρ (by omega)]
    exact hγanti ρ hρ
  · intro hcon
    refine hγnot ?_
    intro ρ hρ
    have h1 := hcon ρ hρ
    rw [show LinearFunctional.evalForest (antisymmetricPart ψ) ρ =
      antisymmetricPart ψ (ofForest (R := R) ρ) from rfl,
      hanti ρ hρ] at h1
    exact h1

/-- Forests of order one consist of a single one-node tree. -/
private theorem eq_bullet_forest_of_order_one {rho : RootedForest}
    (h : RootedForest.order rho = 1) :
    rho = RootedForest.singleton RootedTree.bullet := by
  have hne : rho ≠ 0 := by
    intro h0
    rw [h0, RootedForest.order_zero] at h
    omega
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
  obtain ⟨s, rfl⟩ := Multiset.exists_cons_of_mem ha
  have hsplit : (a ::ₘ s : RootedForest) =
      RootedForest.singleton a + s := rfl
  rw [hsplit, RootedForest.order_add, RootedForest.order_singleton] at h
  have hapos := RootedTree.order_pos a
  have hs0 : RootedForest.order (s : RootedForest) = 0 := by omega
  have hs : (s : RootedForest) = 0 :=
    (RootedForest.order_eq_zero_iff _).1 hs0
  have hbr : RootedTree.order a =
      RootedForest.order (RootedTree.branches a) + 1 := by
    conv_lhs => rw [← RootedForest.graft_branches a]
    rw [RootedForest.order_graft]
    omega
  have hbr0 : RootedTree.branches a = 0 :=
    (RootedForest.order_eq_zero_iff _).1 (by omega)
  have ha_bullet : a = RootedTree.bullet := by
    conv_lhs => rw [← RootedForest.graft_branches a]
    rw [hbr0, RootedForest.graft_zero]
  rw [hsplit, hs, add_zero, ha_bullet]

/-- A character realized by some Runge–Kutta method. -/
def IsRKCharacter [Field R] (χ : Character R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (rk : RungeKutta ι R),
    χ = Series.toCharacter (RungeKutta.series rk)

/-- A consistent method: the first-order weight is `1`. -/
def IsConsistent [Field R] (χ : Character R) : Prop :=
  χ.evalForest (RootedForest.singleton RootedTree.bullet) = 1

/-- **S-equivalence classes contain `0` or infinitely many consistent
Runge–Kutta characters** (arXiv:2507.21006, Section 7, the infinitude
half of the `n` theorem): if a class contains one consistent RK
character, the antisymmetric family produces infinitely many. -/
theorem infinite_consistent_rk_sEquiv (R : Type w) [Field R] [CharZero R]
    [Invertible (2 : R)] {ψ : Character R} (hRK : IsRKCharacter ψ)
    (hcons : IsConsistent ψ) :
    {χ : Character R |
      IsRKCharacter χ ∧ IsConsistent χ ∧ SEquiv χ ψ}.Infinite := by
  classical
  obtain ⟨ι, hι, rkψ, hrkψ⟩ := hRK
  set ω : R → Character R := fun l =>
    Series.toCharacter (RungeKutta.series (RungeKutta.antisymScheme l))
    with hω
  have hω_bullet : ∀ l : R,
      (ω l).evalForest (RootedForest.singleton RootedTree.bullet) = 0 := by
    intro l
    rw [hω]
    rw [RungeKutta.toCharacter_series_evalForest,
      RungeKutta.forestWeight_singleton,
      show RootedTree.bullet = RootedTree.ofPTree PTree.bullet from rfl,
      RungeKutta.treeWeight_ofPTree]
    exact RungeKutta.weightBullet_antisymScheme l
  set c₂ : RootedForest :=
    RootedForest.singleton (RootedTree.ofPTree (PTree.node [PTree.node []]))
    with hc₂
  have hc₂ord : RootedForest.order c₂ = 2 := by
    rw [hc₂, RootedForest.order_singleton, RootedTree.order_ofPTree]
    rfl
  have hω_c₂ : ∀ l : R, (ω l).evalForest c₂ = 4 * l ^ 2 := by
    intro l
    rw [hω, hc₂, RungeKutta.toCharacter_series_evalForest,
      RungeKutta.forestWeight_singleton, RungeKutta.treeWeight_ofPTree]
    exact RungeKutta.weight_chain2_antisymScheme l
  have hval : ∀ l : R, (convolution (ω l) ψ).evalForest c₂ =
      4 * l ^ 2 + ψ.evalForest c₂ := by
    intro l
    have hne : c₂ ≠ 0 := by
      intro h0
      rw [h0, RootedForest.order_zero] at hc₂ord
      omega
    rw [Series.convolution_evalForest_boundary_split (ω l) ψ hne]
    have hfil : (((RootedForest.coproductTerms c₂).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        (ω l).evalForest term.1 * ψ.evalForest term.2).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.1 hx
      obtain ⟨htm, htp⟩ := List.mem_filter.1 hterm
      have htp' : 0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2 := by simpa using htp
      have horder := RootedForest.coproductTerms_order htm
      rw [hc₂ord] at horder
      have hP1 : RootedForest.order term.1 = 1 := by omega
      rw [eq_bullet_forest_of_order_one hP1, hω_bullet l, zero_mul]
    rw [hfil, hω_c₂]
    ring
  set g : ℕ → Character R := fun k =>
    convolution (ω (((k + 1 : ℕ) : R))) ψ with hg
  have hginj : Function.Injective g := by
    intro k k' hkk
    have h1 := congrArg (fun χ : Character R => χ.evalForest c₂) hkk
    simp only [hg] at h1
    rw [hval, hval] at h1
    have hsq : (((k + 1 : ℕ) : R)) ^ 2 = (((k' + 1 : ℕ) : R)) ^ 2 := by
      linear_combination h1 / 4
    have hnat : ((k + 1) ^ 2 : ℕ) = ((k' + 1) ^ 2 : ℕ) := by
      exact_mod_cast hsq
    have h2 := Nat.pow_left_injective (two_ne_zero) hnat
    omega
  refine Set.infinite_of_injective_forall_mem hginj fun k => ?_
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨Bool ⊕ ι, inferInstance,
      RungeKutta.compose (RungeKutta.antisymScheme _) rkψ, by
        rw [RungeKutta.toCharacter_series_compose, ← hrkψ]⟩
  · show (g k).evalForest (RootedForest.singleton RootedTree.bullet) = 1
    have hne : RootedForest.singleton RootedTree.bullet ≠ 0 :=
      RootedForest.singleton_ne_zero _
    rw [hg]
    rw [Series.convolution_evalForest_boundary_split _ _ hne]
    have hfil : (((RootedForest.coproductTerms
        (RootedForest.singleton RootedTree.bullet)).filter fun term =>
        0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2).map fun term =>
        (ω (((k + 1 : ℕ) : R))).evalForest term.1 *
          ψ.evalForest term.2).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.1 hx
      obtain ⟨htm, htp⟩ := List.mem_filter.1 hterm
      have htp' : 0 < RootedForest.order term.1 ∧
          0 < RootedForest.order term.2 := by simpa using htp
      have horder := RootedForest.coproductTerms_order htm
      rw [RootedForest.order_singleton] at horder
      have hb1 : RootedTree.order RootedTree.bullet = 1 := rfl
      omega
    rw [hfil, hcons, hω_bullet]
    ring
  · show SEquiv (g k) ψ
    show symmetricPart (g k) = symmetricPart ψ
    have hωeq : involution (ω (((k + 1 : ℕ) : R))) =
        ω (((k + 1 : ℕ) : R)) :=
      RungeKutta.isEven_toCharacter_antisymScheme _
    have hψplus_norm : antisymmetricPart ψ (ofForest (R := R) 0) = 1 := by
      rw [antisymmetricPart, LinearFunctional.convolution_ofForest,
        RootedForest.coproductTerms_zero]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [LinearFunctional.compGradingInvolution_ofForest,
        RootedForest.order_zero, pow_zero, one_mul, symmetricPart,
        sqrtFunctional_ofForest, RootedForest.sqrtCoeff_zero]
      show ψ (ofForest (R := R) 0) * 1 = 1
      rw [ofForest_zero, map_one, mul_one]
    refine (symmetricPart_unique (g k)
      (e := LinearFunctional.convolution
        (LinearFunctional.ofCharacter (ω (((k + 1 : ℕ) : R))))
        (antisymmetricPart ψ))
      (o := symmetricPart ψ) ?_ ?_ ?_ ?_ ?_).symm
    · rw [LinearFunctional.convolution_ofForest,
        RootedForest.coproductTerms_zero]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      rw [hψplus_norm]
      show (ω (((k + 1 : ℕ) : R))) (ofForest (R := R) 0) * 1 = 1
      rw [ofForest_zero, map_one, mul_one]
    · rw [symmetricPart, sqrtFunctional_ofForest,
        RootedForest.sqrtCoeff_zero]
    · rw [← LinearFunctional.convolution_compGradingInvolution]
      congr 1
      · rw [← ofCharacter_involution, hωeq]
      · exact compGradingInvolution_antisymmetricPart ψ
    · exact convolution_compGradingInvolution_symmetricPart ψ
    · rw [LinearFunctional.convolution_assoc,
        convolution_antisymmetricPart_symmetricPart,
        ← linearFunctional_ofCharacter_convolution]

/-- **The zero value is attained**: the S-equivalence class of the unit
(the identity method, whose class is the even characters) contains no
consistent character (arXiv:2507.21006, Section 7, the `0`-half of the
`n` theorem). -/
theorem not_isConsistent_of_sEquiv_unit [Field R] [CharZero R]
    [Invertible (2 : R)] {χ : Character R} (h : SEquiv χ (unit R)) :
    ¬ IsConsistent χ := by
  intro hcons
  have hsym : symmetricPart χ = LinearFunctional.counit R := by
    rw [show symmetricPart χ = symmetricPart (unit R) from h,
      symmetricPart_of_isOdd isOdd_unit, linearFunctional_ofCharacter_unit]
  have hdec := convolution_antisymmetricPart_symmetricPart χ
  rw [hsym, LinearFunctional.convolution_counit_right] at hdec
  have heven := compGradingInvolution_antisymmetricPart χ
  rw [hdec] at heven
  have hb := congrArg (fun f : LinearFunctional R =>
    f (ofForest (R := R) (RootedForest.singleton RootedTree.bullet))) heven
  simp only [LinearFunctional.compGradingInvolution_ofForest,
    RootedForest.order_singleton] at hb
  have hb1 : RootedTree.order RootedTree.bullet = 1 := rfl
  rw [hb1, pow_one, neg_one_mul] at hb
  have hval : (LinearFunctional.ofCharacter χ) (ofForest (R := R)
      (RootedForest.singleton RootedTree.bullet)) = 1 := hcons
  rw [hval] at hb
  have : (2 : R) = 0 := by linear_combination -hb
  exact two_ne_zero this

end

end Character

end ForestAlgebra

end BSeries
