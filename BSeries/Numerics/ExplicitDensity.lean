/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Series.EES
import BSeries.Numerics.Density
import BSeries.Numerics.Enumeration

/-!
# Density of explicit Runge–Kutta methods

Butcher's Theorem 317A holds with the methods restricted to **explicit**
tableaux (Butcher, *Numerical Methods for ODEs*, Remark after Theorem 317A;
arXiv:2507.21006, Remark `rmk:explicit_rk_density`): all four constructions
of the density proof — the zero scheme, block-diagonal sums, weight
scalings, tableau scalings, and the one-stage extension — preserve strict
lower-triangularity with respect to the lexicographic stage orders.
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w}

section Preserve

theorem isExplicit_zeroScheme [Zero R] : IsExplicit (zeroScheme R) :=
  fun _ _ _ => rfl

theorem isExplicit_dirSum [LinearOrder ι] [LinearOrder κ] [Zero R]
    {rk₁ : RungeKutta ι R} {rk₂ : RungeKutta κ R}
    (h₁ : IsExplicit rk₁) (h₂ : IsExplicit rk₂) :
    IsExplicit (ι := ι ⊕ₗ κ) (dirSum rk₁ rk₂) := by
  intro i j hij
  rcases i with a | a <;> rcases j with b | b
  · exact h₁ a b (Sum.Lex.inl_le_inl_iff.1 hij)
  · rfl
  · rfl
  · exact h₂ a b (Sum.Lex.inr_le_inr_iff.1 hij)

theorem isExplicit_scaleWeights [LinearOrder ι] [Mul R] [Zero R] (c : R)
    {rk : RungeKutta ι R} (h : IsExplicit rk) :
    IsExplicit (scaleWeights c rk) :=
  fun i j hij => h i j hij

theorem isExplicit_smulScheme [LinearOrder ι] [MulZeroClass R] (c : R)
    {rk : RungeKutta ι R} (h : IsExplicit rk) :
    IsExplicit (smulScheme c rk) := by
  intro i j hij
  show c * rk.A i j = 0
  rw [h i j hij, mul_zero]

theorem isExplicit_extendScheme [LinearOrder ι] [Zero R] [One R]
    {rk : RungeKutta ι R} (h : IsExplicit rk) :
    IsExplicit (ι := ι ⊕ₗ PUnit) (extendScheme rk) := by
  intro i j hij
  rcases i with a | a <;> rcases j with b | b
  · exact h a b (Sum.Lex.inl_le_inl_iff.1 hij)
  · rfl
  · exact absurd hij Sum.Lex.not_inr_le_inl
  · rfl

end Preserve

section ExplicitDensity

variable [CommSemiring R]

/-- A vector of prescribed elementary weights is **explicitly** achievable
if some explicit Runge–Kutta method realizes it. -/
def AchievableWeightsE (T₀ : Finset RootedTree) (w : T₀ → R) : Prop :=
  ∃ (ι : Type) (_ : LinearOrder ι) (_ : Fintype ι) (rk : RungeKutta ι R),
    IsExplicit rk ∧ ∀ t : T₀, treeWeight rk (t : RootedTree) = w t

theorem achievableWeightsE_zero (T₀ : Finset RootedTree) :
    AchievableWeightsE T₀ (0 : T₀ → R) :=
  ⟨PUnit, inferInstance, inferInstance, zeroScheme R, isExplicit_zeroScheme,
    fun _ => treeWeight_zeroScheme _⟩

theorem AchievableWeightsE.add {T₀ : Finset RootedTree} {w₁ w₂ : T₀ → R}
    (h₁ : AchievableWeightsE T₀ w₁) (h₂ : AchievableWeightsE T₀ w₂) :
    AchievableWeightsE T₀ (w₁ + w₂) := by
  obtain ⟨ι, _, _, rk₁, he₁, hrk₁⟩ := h₁
  obtain ⟨κ, _, _, rk₂, he₂, hrk₂⟩ := h₂
  refine ⟨ι ⊕ₗ κ, inferInstance, inferInstanceAs (Fintype (ι ⊕ κ)),
    dirSum rk₁ rk₂, isExplicit_dirSum he₁ he₂, fun t => by
      have h := treeWeight_dirSum rk₁ rk₂ (t : RootedTree)
      rw [hrk₁ t, hrk₂ t] at h
      exact h⟩

theorem AchievableWeightsE.smul {T₀ : Finset RootedTree} {w : T₀ → R}
    (c : R) (h : AchievableWeightsE T₀ w) :
    AchievableWeightsE T₀ (c • w) := by
  obtain ⟨ι, _, _, rk, he, hrk⟩ := h
  exact ⟨ι, ‹_›, ‹_›, scaleWeights c rk, isExplicit_scaleWeights c he,
    fun t => by
      rw [treeWeight_scaleWeights, hrk]
      rfl⟩

theorem AchievableWeightsE.graded {T₀ : Finset RootedTree} {w : T₀ → R}
    (c : R) (h : AchievableWeightsE T₀ w) :
    AchievableWeightsE T₀
      (fun t => c ^ RootedTree.order (t : RootedTree) * w t) := by
  obtain ⟨ι, _, _, rk, he, hrk⟩ := h
  exact ⟨ι, ‹_›, ‹_›, smulScheme c rk, isExplicit_smulScheme c he,
    fun t => by
      rw [treeWeight_smulScheme, hrk]⟩

/-- The explicitly achievable weight vectors form a submodule. -/
def achievableSubmoduleE (R : Type w) [CommSemiring R]
    (T₀ : Finset RootedTree) : Submodule R (T₀ → R) where
  carrier := {w | AchievableWeightsE T₀ w}
  zero_mem' := achievableWeightsE_zero T₀
  add_mem' := AchievableWeightsE.add
  smul_mem' := fun c _ hx => AchievableWeightsE.smul c hx

/-- Graded annihilation, explicit version. -/
theorem annihilator_gradedE {R : Type w} [Field R] [Infinite R]
    {T₀ : Finset RootedTree} (ξ : T₀ → R)
    (h : ∀ w : T₀ → R, AchievableWeightsE T₀ w → ∑ t : T₀, ξ t * w t = 0)
    (d : ℕ) {w : T₀ → R} (hw : AchievableWeightsE T₀ w) :
    ∑ t ∈ Finset.univ.filter
      (fun t : T₀ => RootedTree.order (t : RootedTree) = d),
      ξ t * w t = 0 := by
  classical
  set P : Polynomial R := ∑ t : T₀,
    Polynomial.C (ξ t * w t) *
      Polynomial.X ^ (RootedTree.order (t : RootedTree)) with hP
  have heval : ∀ c : R, P.eval c = 0 := by
    intro c
    have hach := h _ (hw.graded c)
    rw [hP]
    rw [Polynomial.eval_finsetSum]
    rw [← hach]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring
  have hroots : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    have huniv : {x : R | P.IsRoot x} = Set.univ :=
      Set.eq_univ_of_forall heval
    rw [huniv]
    exact Set.infinite_univ
  have hcoeff := congrArg (fun q : Polynomial R => q.coeff d) hroots
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero, mul_ite, mul_one,
    mul_zero] at hcoeff
  rw [Finset.sum_filter]
  simpa [eq_comm] using hcoeff

private theorem order_le_of_mem_forest' {a : RootedTree} {φ : RootedForest}
    (ha : a ∈ φ) : RootedTree.order a ≤ RootedForest.order φ := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [show (a ::ₘ rest : RootedForest) =
    RootedForest.singleton a + rest from rfl, RootedForest.order_add,
    RootedForest.order_singleton]
  exact Nat.le_add_right _ _

/-- **Density of explicit Runge–Kutta methods** (Butcher, Theorem 317A with
the explicitness remark; arXiv:2507.21006, `rmk:explicit_rk_density`): any
finite prescription of elementary weights is realized by an **explicit**
Runge–Kutta method. -/
theorem exists_explicit_rk_treeWeight {R : Type w} [Field R] [Infinite R] :
    ∀ (n : ℕ) (T₀ : Finset RootedTree), T₀.sup RootedTree.order ≤ n →
      ∀ β : RootedTree → R,
        AchievableWeightsE T₀ (fun t => β (t : RootedTree)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T₀ hsup β
  classical
  suffices htop : achievableSubmoduleE R T₀ = ⊤ by
    have : (fun t : T₀ => β (t : RootedTree)) ∈ achievableSubmoduleE R T₀ := by
      rw [htop]
      exact Submodule.mem_top
    exact this
  by_contra hne
  have hlt : achievableSubmoduleE R T₀ < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨f, hf0, hker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hann : ∀ w : T₀ → R, AchievableWeightsE T₀ w → f w = 0 := by
    intro w hw
    have hmem : f w ∈ (achievableSubmoduleE R T₀).map f :=
      Submodule.mem_map_of_mem hw
    rw [hker] at hmem
    exact (Submodule.mem_bot R).1 hmem
  set ξ : T₀ → R := fun t => f (fun u => if t = u then 1 else 0) with hξ
  have hfw : ∀ w : T₀ → R, f w = ∑ t, w t * ξ t := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, smul_eq_mul, hξ]
  have hsum0 : ∀ w : T₀ → R, AchievableWeightsE T₀ w →
      ∑ t, ξ t * w t = 0 := by
    intro w hw
    have := hann w hw
    rw [hfw] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hξ0 : ∃ t₀ : T₀, ξ t₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hf0 (LinearMap.ext fun w => ?_)
    rw [hfw]
    simp [hall]
  obtain ⟨t₀, ht₀⟩ := hξ0
  set d : ℕ := RootedTree.order (t₀ : RootedTree) with hd
  have hgr := fun (w : T₀ → R) (hw : AchievableWeightsE T₀ w) =>
    annihilator_gradedE ξ hsum0 d hw
  set C : Finset RootedTree :=
    (T₀.filter fun a => RootedTree.order a = d).biUnion
      (fun a => (RootedTree.branches a).toFinset) with hC
  have hd_pos : 1 ≤ d := RootedTree.order_pos _
  have hd_le : d ≤ n := le_trans (Finset.le_sup t₀.2) hsup
  have hmemC : ∀ {t : T₀}, RootedTree.order (t : RootedTree) = d →
      ∀ {a : RootedTree}, a ∈ RootedTree.branches (t : RootedTree) →
      a ∈ C := by
    intro t htd a ha
    rw [hC]
    exact Finset.mem_biUnion.2 ⟨t, Finset.mem_filter.2 ⟨t.2, htd⟩,
      Multiset.mem_toFinset.2 ha⟩
  have hCsup : C.sup RootedTree.order ≤ n - 1 := by
    refine Finset.sup_le fun a ha => ?_
    rw [hC] at ha
    obtain ⟨t, htmem, hat⟩ := Finset.mem_biUnion.1 ha
    have htd := (Finset.mem_filter.1 htmem).2
    have h1 : RootedTree.order a ≤
        RootedForest.order (RootedTree.branches t) :=
      order_le_of_mem_forest' (Multiset.mem_toFinset.1 hat)
    have h2 : RootedTree.order t =
        RootedForest.order (RootedTree.branches t) + 1 := by
      conv_lhs => rw [← RootedForest.graft_branches t]
      rw [RootedForest.order_graft]
      omega
    omega
  have hkey : ∀ μ : RootedTree → R,
      ∑ t ∈ Finset.univ.filter
        (fun t : T₀ => RootedTree.order (t : RootedTree) = d),
        ξ t * ((RootedTree.branches (t : RootedTree)).map μ).prod = 0 := by
    intro μ
    obtain ⟨ι, _, _, rk, hexp, hrk⟩ := ih (n - 1) (by omega) C hCsup μ
    have hach : AchievableWeightsE T₀
        (fun t => treeWeight (extendScheme rk) (t : RootedTree)) :=
      ⟨ι ⊕ₗ PUnit, inferInstance, inferInstanceAs (Fintype (ι ⊕ PUnit)),
        extendScheme rk, isExplicit_extendScheme hexp, fun t => rfl⟩
    have h0 := hgr _ hach
    rw [← h0]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htd := (Finset.mem_filter.1 ht).2
    rw [treeWeight_extendScheme, forestWeight]
    refine congrArg (ξ t * ·) (congrArg Multiset.prod
      (Multiset.map_congr rfl fun a ha => ?_))
    exact (hrk ⟨a, hmemC htd ha⟩).symm
  set Q : MvPolynomial RootedTree R :=
    ∑ t ∈ Finset.univ.filter
      (fun t : T₀ => RootedTree.order (t : RootedTree) = d),
      MvPolynomial.monomial
        (Multiset.toFinsupp (RootedTree.branches (t : RootedTree))) (ξ t)
    with hQ
  have hQeval : ∀ μ : RootedTree → R, MvPolynomial.eval μ Q = 0 := by
    intro μ
    rw [hQ, map_sum, ← hkey μ]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [MvPolynomial.eval_monomial]
    congr 1
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [Finset.prod_multiset_map_count]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Multiset.toFinsupp_apply]
  have hQ0 : Q = 0 := MvPolynomial.funext fun μ => by
    rw [hQeval μ, map_zero]
  have ht₀mem : t₀ ∈ Finset.univ.filter
      (fun t : T₀ => RootedTree.order (t : RootedTree) = d) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hd.symm⟩
  have hcoeff := congrArg
    (MvPolynomial.coeff
      (Multiset.toFinsupp (RootedTree.branches (t₀ : RootedTree)))) hQ0
  rw [hQ] at hcoeff
  rw [MvPolynomial.coeff_sum] at hcoeff
  rw [Finset.sum_eq_single t₀ (fun t ht hne' => ?_)
    (fun h => absurd ht₀mem h)] at hcoeff
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at hcoeff
    simp only [MvPolynomial.coeff_zero] at hcoeff
    exact ht₀ hcoeff
  · rw [MvPolynomial.coeff_monomial, if_neg]
    intro heq
    refine hne' ?_
    have hbr : RootedTree.branches (t : RootedTree) =
        RootedTree.branches (t₀ : RootedTree) :=
      Multiset.toFinsupp.injective heq
    have htt₀ : (t : RootedTree) = (t₀ : RootedTree) := by
      rw [← RootedForest.graft_branches (t : RootedTree),
        ← RootedForest.graft_branches (t₀ : RootedTree), hbr]
    exact Subtype.ext htt₀

/-- Explicit density, packaged for arbitrary finite tree sets. -/
theorem exists_explicit_rk_forall_treeWeight {R : Type w} [Field R]
    [Infinite R] (T₀ : Finset RootedTree) (β : RootedTree → R) :
    ∃ (ι : Type) (_ : LinearOrder ι) (_ : Fintype ι)
      (rk : RungeKutta ι R), IsExplicit rk ∧
        ∀ t ∈ T₀, treeWeight rk t = β t := by
  obtain ⟨ι, hlo, hι, rk, hexp, hrk⟩ :=
    exists_explicit_rk_treeWeight (T₀.sup RootedTree.order) T₀ le_rfl β
  exact ⟨ι, hlo, hι, rk, hexp, fun t ht => hrk ⟨t, ht⟩⟩

end ExplicitDensity

end RungeKutta

end BSeries
