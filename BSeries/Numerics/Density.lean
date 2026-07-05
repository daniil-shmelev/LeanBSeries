/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Composition
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Tableau constructions for the independence of elementary weights

The three constructions underlying Butcher's Theorem 317A (independence of
the elementary weights / density of Runge–Kutta methods):

* `dirSum` — the block-diagonal tableau, whose elementary weights are the
  **sums** of the constituents' weights;
* `smulScheme` — scaling every coefficient by `c`, which scales the weight
  of a tree `t` by `c^{|t|}`;
* `extendScheme` — appending a single quadrature stage whose row is `bᵀ`
  and moving all quadrature weight onto it, whose elementary weights are
  the **products of the full weights of the children** of the root.

(Butcher, *Numerical Methods for ODEs*, Section 317.)
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w}

/-- The block-diagonal sum of two tableaux. -/
def dirSum [Zero R] (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    RungeKutta (ι ⊕ κ) R where
  A
    | .inl i, .inl j => rk₁.A i j
    | .inl _, .inr _ => 0
    | .inr _, .inl _ => 0
    | .inr i, .inr j => rk₂.A i j
  b
    | .inl j => rk₁.b j
    | .inr j => rk₂.b j

/-- The tableau with every coefficient scaled by `c`. -/
def smulScheme [Mul R] (c : R) (rk : RungeKutta ι R) : RungeKutta ι R where
  A i j := c * rk.A i j
  b j := c * rk.b j

/-- The tableau extended by one stage whose row is `bᵀ`, with all
quadrature weight moved onto the new stage. -/
def extendScheme [Zero R] [One R] (rk : RungeKutta ι R) :
    RungeKutta (ι ⊕ PUnit) R where
  A
    | .inl i, .inl j => rk.A i j
    | .inl _, .inr _ => 0
    | .inr _, .inl j => rk.b j
    | .inr _, .inr _ => 0
  b
    | .inl _ => 0
    | .inr _ => 1

variable [Fintype ι] [Fintype κ] [CommSemiring R]

mutual

theorem stageWeight_dirSum_inl (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (t : PTree) (i : ι),
      stageWeight (dirSum rk₁ rk₂) t (.inl i) = stageWeight rk₁ t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_dirSum_inl rk₁ rk₂ ts i]

theorem stageWeightList_dirSum_inl
    (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (ts : List PTree) (i : ι),
      stageWeightList (dirSum rk₁ rk₂) ts (.inl i) =
        stageWeightList rk₁ ts i
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_dirSum_inl rk₁ rk₂ ts i]
      congr 1
      rw [Fintype.sum_sum_type]
      have h2 : ∑ j : κ, (dirSum rk₁ rk₂).A (.inl i) (.inr j) *
          stageWeight (dirSum rk₁ rk₂) t (.inr j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        show (0 : R) * _ = 0
        rw [zero_mul]
      rw [h2, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stageWeight_dirSum_inl rk₁ rk₂ t j]
      rfl

end

mutual

theorem stageWeight_dirSum_inr (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (t : PTree) (i : κ),
      stageWeight (dirSum rk₁ rk₂) t (.inr i) = stageWeight rk₂ t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_dirSum_inr rk₁ rk₂ ts i]

theorem stageWeightList_dirSum_inr
    (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R) :
    ∀ (ts : List PTree) (i : κ),
      stageWeightList (dirSum rk₁ rk₂) ts (.inr i) =
        stageWeightList rk₂ ts i
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_dirSum_inr rk₁ rk₂ ts i]
      congr 1
      rw [Fintype.sum_sum_type]
      have h1 : ∑ j : ι, (dirSum rk₁ rk₂).A (.inr i) (.inl j) *
          stageWeight (dirSum rk₁ rk₂) t (.inl j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        show (0 : R) * _ = 0
        rw [zero_mul]
      rw [h1, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stageWeight_dirSum_inr rk₁ rk₂ t j]
      rfl

end

/-- **The elementary weights of a block-diagonal sum are the sums of the
elementary weights** (Butcher, Section 317, eq. (317a)). -/
theorem weight_dirSum (rk₁ : RungeKutta ι R) (rk₂ : RungeKutta κ R)
    (t : PTree) :
    weight (dirSum rk₁ rk₂) t = weight rk₁ t + weight rk₂ t := by
  rw [weight, Fintype.sum_sum_type, weight, weight]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [stageWeight_dirSum_inl rk₁ rk₂ t j]
    rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [stageWeight_dirSum_inr rk₁ rk₂ t j]
    rfl

mutual

theorem stageWeight_smulScheme (c : R) (rk : RungeKutta ι R) :
    ∀ (t : PTree) (i : ι),
      stageWeight (smulScheme c rk) t i =
        c ^ (PTree.order t - 1) * stageWeight rk t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_smulScheme c rk ts i, PTree.order_node]
      congr 2
      omega

theorem stageWeightList_smulScheme (c : R) (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (i : ι),
      stageWeightList (smulScheme c rk) ts i =
        c ^ PTree.orderList ts * stageWeightList rk ts i
  | [], i => by simp
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_smulScheme c rk ts i, PTree.orderList_cons, pow_add]
      have hj : ∀ j, (smulScheme c rk).A i j *
          stageWeight (smulScheme c rk) t j =
          c ^ (PTree.order t) * (rk.A i j * stageWeight rk t j) := fun j => by
        show c * rk.A i j * _ = _
        rw [stageWeight_smulScheme c rk t j]
        have hpos : 1 ≤ PTree.order t := PTree.order_pos t
        calc c * rk.A i j * (c ^ (PTree.order t - 1) * stageWeight rk t j)
            = c ^ (PTree.order t - 1 + 1) *
                (rk.A i j * stageWeight rk t j) := by
              rw [pow_succ]
              ring
          _ = c ^ (PTree.order t) * (rk.A i j * stageWeight rk t j) := by
              congr 2
              omega
      rw [Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
      ring

end

/-- **Scaling the tableau scales the weight of `t` by `c^{|t|}`**
(Butcher, Section 317). -/
theorem weight_smulScheme (c : R) (rk : RungeKutta ι R) (t : PTree) :
    weight (smulScheme c rk) t = c ^ PTree.order t * weight rk t := by
  rw [weight, weight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show c * rk.b i * _ = _
  rw [stageWeight_smulScheme c rk t i]
  have hpos : 1 ≤ PTree.order t := PTree.order_pos t
  calc c * rk.b i * (c ^ (PTree.order t - 1) * stageWeight rk t i)
      = c ^ (PTree.order t - 1 + 1) * (rk.b i * stageWeight rk t i) := by
        rw [pow_succ]
        ring
    _ = c ^ PTree.order t * (rk.b i * stageWeight rk t i) := by
        congr 2
        omega

mutual

theorem stageWeight_extendScheme_inl (rk : RungeKutta ι R) :
    ∀ (t : PTree) (i : ι),
      stageWeight (extendScheme rk) t (.inl i) = stageWeight rk t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_extendScheme_inl rk ts i]

theorem stageWeightList_extendScheme_inl (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (i : ι),
      stageWeightList (extendScheme rk) ts (.inl i) =
        stageWeightList rk ts i
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_extendScheme_inl rk ts i]
      congr 1
      rw [Fintype.sum_sum_type]
      have h2 : ∑ j : PUnit, (extendScheme rk).A (.inl i) (.inr j) *
          stageWeight (extendScheme rk) t (.inr j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        show (0 : R) * _ = 0
        rw [zero_mul]
      rw [h2, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stageWeight_extendScheme_inl rk t j]
      rfl

end

/-- The added stage of `extendScheme` evaluates the product of the full
weights of a forest. -/
theorem stageWeightList_extendScheme_inr (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (u : PUnit),
      stageWeightList (extendScheme rk) ts (.inr u) =
        (ts.map fun t => weight rk t).prod
  | [], _ => rfl
  | t :: ts, u => by
      rw [stageWeightList_cons, stageWeightList_extendScheme_inr rk ts u,
        List.map_cons, List.prod_cons]
      congr 1
      rw [Fintype.sum_sum_type]
      have h2 : ∑ j : PUnit, (extendScheme rk).A (.inr u) (.inr j) *
          stageWeight (extendScheme rk) t (.inr j) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        show (0 : R) * _ = 0
        rw [zero_mul]
      rw [h2, add_zero, weight]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stageWeight_extendScheme_inl rk t j]
      rfl

/-- **The extended scheme's elementary weight is the product of the full
weights of the root's children** (Butcher, Section 317: the one-stage
extension realizing `Φ'(t) = Π_j Φ(t_j)`). -/
theorem weight_extendScheme (rk : RungeKutta ι R) (ts : List PTree) :
    weight (extendScheme rk) (.node ts) =
      (ts.map fun t => weight rk t).prod := by
  rw [weight, Fintype.sum_sum_type]
  have h1 : ∑ j : ι, (extendScheme rk).b (.inl j) *
      stageWeight (extendScheme rk) (.node ts) (.inl j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    show (0 : R) * _ = 0
    rw [zero_mul]
  rw [h1, zero_add]
  have h2 : ∀ u : PUnit, (extendScheme rk).b (.inr u) *
      stageWeight (extendScheme rk) (.node ts) (.inr u) =
      (ts.map fun t => weight rk t).prod := fun u => by
    show (1 : R) * _ = _
    rw [one_mul, stageWeight_node, stageWeightList_extendScheme_inr rk ts u]
  rw [Finset.sum_congr rfl fun u _ => h2 u]
  simp

section Achievable

/-- The scheme with all coefficients zero. -/
def zeroScheme (R : Type w) [Zero R] : RungeKutta PUnit R where
  A _ _ := 0
  b _ := 0

theorem treeWeight_zeroScheme (τ : RootedTree) :
    treeWeight (zeroScheme R) τ = 0 := by
  refine Quotient.inductionOn τ fun t => ?_
  show weight (zeroScheme R) t = 0
  rw [weight]
  refine Finset.sum_eq_zero fun i _ => ?_
  show (0 : R) * _ = 0
  rw [zero_mul]

omit [Fintype ι] [Fintype κ] [CommSemiring R] in
set_option linter.overlappingInstances false in
/-- Scaling only the quadrature weights `b`. Since `b` enters each
elementary weight exactly once, this scales all weights linearly. -/
def scaleWeights [Mul R] (c : R) (rk : RungeKutta ι R) : RungeKutta ι R where
  A := rk.A
  b j := c * rk.b j


mutual

theorem stageWeight_scaleWeights (c : R) (rk : RungeKutta ι R) :
    ∀ (t : PTree) (i : ι),
      stageWeight (scaleWeights c rk) t i = stageWeight rk t i
  | .node ts, i => by
      rw [stageWeight_node, stageWeight_node,
        stageWeightList_scaleWeights c rk ts i]

theorem stageWeightList_scaleWeights (c : R) (rk : RungeKutta ι R) :
    ∀ (ts : List PTree) (i : ι),
      stageWeightList (scaleWeights c rk) ts i = stageWeightList rk ts i
  | [], _ => rfl
  | t :: ts, i => by
      rw [stageWeightList_cons, stageWeightList_cons,
        stageWeightList_scaleWeights c rk ts i]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stageWeight_scaleWeights c rk t j]
      rfl

end

theorem weight_scaleWeights (c : R) (rk : RungeKutta ι R) (t : PTree) :
    weight (scaleWeights c rk) t = c * weight rk t := by
  rw [weight, weight, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [stageWeight_scaleWeights c rk t i]
  show c * rk.b i * _ = _
  ring

theorem treeWeight_scaleWeights (c : R) (rk : RungeKutta ι R)
    (τ : RootedTree) :
    treeWeight (scaleWeights c rk) τ = c * treeWeight rk τ :=
  Quotient.inductionOn τ fun t => weight_scaleWeights c rk t

theorem treeWeight_dirSum (rk₁ : RungeKutta ι R)
    (rk₂ : RungeKutta κ R) (τ : RootedTree) :
    treeWeight (dirSum rk₁ rk₂) τ = treeWeight rk₁ τ + treeWeight rk₂ τ :=
  Quotient.inductionOn τ fun t => weight_dirSum rk₁ rk₂ t

theorem treeWeight_smulScheme (c : R) (rk : RungeKutta ι R)
    (τ : RootedTree) :
    treeWeight (smulScheme c rk) τ =
      c ^ RootedTree.order τ * treeWeight rk τ := by
  refine Quotient.inductionOn τ fun t => ?_
  show weight (smulScheme c rk) t =
    c ^ RootedTree.order (RootedTree.ofPTree t) * weight rk t
  rw [RootedTree.order_ofPTree]
  exact weight_smulScheme c rk t

/-- **The extended scheme evaluates the product of the children's full
weights**: `Φ'(τ) = forestWeight(branches τ)` (Butcher, Section 317). -/
theorem treeWeight_extendScheme (rk : RungeKutta ι R) (τ : RootedTree) :
    treeWeight (extendScheme rk) τ =
      forestWeight rk (RootedTree.branches τ) := by
  refine Quotient.inductionOn τ fun t => ?_
  cases t with
  | node ts =>
    show weight (extendScheme rk) (.node ts) =
      forestWeight rk (RootedTree.branches (RootedTree.ofPTree (.node ts)))
    rw [weight_extendScheme, RootedTree.branches_ofPTree_node,
      forestWeight_ofPTree_list]
    rw [weightList]

end Achievable

section Density

variable {R : Type w} [CommSemiring R]

/-- A vector of prescribed elementary weights on a finite set of trees is
achievable if some Runge–Kutta method realizes it. -/
def AchievableWeights (T₀ : Finset RootedTree) (w : T₀ → R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (rk : RungeKutta ι R),
    ∀ t : T₀, treeWeight rk (t : RootedTree) = w t

theorem achievableWeights_zero (T₀ : Finset RootedTree) :
    AchievableWeights T₀ (0 : T₀ → R) :=
  ⟨PUnit, inferInstance, zeroScheme R, fun _ => treeWeight_zeroScheme _⟩

theorem AchievableWeights.add {T₀ : Finset RootedTree} {w₁ w₂ : T₀ → R}
    (h₁ : AchievableWeights T₀ w₁) (h₂ : AchievableWeights T₀ w₂) :
    AchievableWeights T₀ (w₁ + w₂) := by
  obtain ⟨ι, _, rk₁, hrk₁⟩ := h₁
  obtain ⟨κ, _, rk₂, hrk₂⟩ := h₂
  exact ⟨ι ⊕ κ, inferInstance, dirSum rk₁ rk₂, fun t => by
    rw [treeWeight_dirSum, hrk₁, hrk₂]
    rfl⟩

theorem AchievableWeights.smul {T₀ : Finset RootedTree} {w : T₀ → R}
    (c : R) (h : AchievableWeights T₀ w) :
    AchievableWeights T₀ (c • w) := by
  obtain ⟨ι, _, rk, hrk⟩ := h
  exact ⟨ι, ‹_›, scaleWeights c rk, fun t => by
    rw [treeWeight_scaleWeights, hrk]
    rfl⟩

/-- The graded scaling: `c^{|t|}`-weighted vectors are achievable. -/
theorem AchievableWeights.graded {T₀ : Finset RootedTree} {w : T₀ → R}
    (c : R) (h : AchievableWeights T₀ w) :
    AchievableWeights T₀
      (fun t => c ^ RootedTree.order (t : RootedTree) * w t) := by
  obtain ⟨ι, _, rk, hrk⟩ := h
  exact ⟨ι, ‹_›, smulScheme c rk, fun t => by
    rw [treeWeight_smulScheme, hrk]⟩

/-- The achievable weight vectors form a submodule
(Butcher, Section 317: "the set of possible values ... is a vector
space"). -/
def achievableSubmodule (R : Type w) [CommSemiring R]
    (T₀ : Finset RootedTree) : Submodule R (T₀ → R) where
  carrier := {w | AchievableWeights T₀ w}
  zero_mem' := achievableWeights_zero T₀
  add_mem' := AchievableWeights.add
  smul_mem' := fun c _ hx => AchievableWeights.smul c hx

/-- **Graded annihilation**: a linear relation among the elementary
weights valid for all Runge–Kutta methods splits into relations among
trees of equal order (Butcher, Section 317, via the scaling `c^{|t|}`
and a polynomial identity). -/
theorem annihilator_graded {R : Type w} [Field R] [Infinite R]
    {T₀ : Finset RootedTree} (ξ : T₀ → R)
    (h : ∀ w : T₀ → R, AchievableWeights T₀ w → ∑ t : T₀, ξ t * w t = 0)
    (d : ℕ) {w : T₀ → R} (hw : AchievableWeights T₀ w) :
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

/-- Members of a forest have order at most the order of the forest. -/
private theorem order_le_of_mem_forest {a : RootedTree} {φ : RootedForest}
    (ha : a ∈ φ) : RootedTree.order a ≤ RootedForest.order φ := by
  obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [show (a ::ₘ rest : RootedForest) =
    RootedForest.singleton a + rest from rfl, RootedForest.order_add,
    RootedForest.order_singleton]
  exact Nat.le_add_right _ _

/-- **Butcher's Theorem 317A** (independence of the elementary weights /
density of Runge–Kutta methods): for any finite set of trees `T₀` and any
prescription `β` of values, there is a Runge–Kutta method whose elementary
weights realize `β` on `T₀` (Butcher, *Numerical Methods for ODEs*,
Theorem 317A). -/
theorem exists_rk_treeWeight {R : Type w} [Field R] [Infinite R] :
    ∀ (n : ℕ) (T₀ : Finset RootedTree), T₀.sup RootedTree.order ≤ n →
      ∀ β : RootedTree → R, AchievableWeights T₀ (fun t => β (t : RootedTree)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T₀ hsup β
  classical
  -- it suffices that the achievable weight vectors are everything
  suffices htop : achievableSubmodule R T₀ = ⊤ by
    have : (fun t : T₀ => β (t : RootedTree)) ∈ achievableSubmodule R T₀ := by
      rw [htop]
      exact Submodule.mem_top
    exact this
  by_contra hne
  have hlt : achievableSubmodule R T₀ < ⊤ := lt_top_iff_ne_top.2 hne
  -- a nonzero functional annihilating all achievable vectors
  obtain ⟨f, hf0, hker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hann : ∀ w : T₀ → R, AchievableWeights T₀ w → f w = 0 := by
    intro w hw
    have hmem : f w ∈ (achievableSubmodule R T₀).map f :=
      Submodule.mem_map_of_mem hw
    rw [hker] at hmem
    exact (Submodule.mem_bot R).1 hmem
  -- extract the coefficients of the functional
  set ξ : T₀ → R := fun t => f (fun u => if t = u then 1 else 0) with hξ
  have hfw : ∀ w : T₀ → R, f w = ∑ t, w t * ξ t := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, smul_eq_mul, hξ]
  have hsum0 : ∀ w : T₀ → R, AchievableWeights T₀ w →
      ∑ t, ξ t * w t = 0 := by
    intro w hw
    have := hann w hw
    rw [hfw] at this
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  -- some coefficient is nonzero
  have hξ0 : ∃ t₀ : T₀, ξ t₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hf0 (LinearMap.ext fun w => ?_)
    rw [hfw]
    simp [hall]
  obtain ⟨t₀, ht₀⟩ := hξ0
  set d : ℕ := RootedTree.order (t₀ : RootedTree) with hd
  -- the order-d slice of ξ also annihilates
  have hgr := fun (w : T₀ → R) (hw : AchievableWeights T₀ w) =>
    annihilator_graded ξ hsum0 d hw
  -- the children of the order-d trees have strictly smaller order
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
      order_le_of_mem_forest (Multiset.mem_toFinset.1 hat)
    have h2 : RootedTree.order t =
        RootedForest.order (RootedTree.branches t) + 1 := by
      conv_lhs => rw [← RootedForest.graft_branches t]
      rw [RootedForest.order_graft]
      omega
    omega
  -- every assignment of children weights is realizable, giving the
  -- vanishing of a multivariate polynomial identity
  have hkey : ∀ μ : RootedTree → R,
      ∑ t ∈ Finset.univ.filter
        (fun t : T₀ => RootedTree.order (t : RootedTree) = d),
        ξ t * ((RootedTree.branches (t : RootedTree)).map μ).prod = 0 := by
    intro μ
    obtain ⟨ι, _, rk, hrk⟩ := ih (n - 1) (by omega) C hCsup μ
    have hach : AchievableWeights T₀
        (fun t => treeWeight (extendScheme rk) (t : RootedTree)) :=
      ⟨ι ⊕ PUnit, inferInstance, extendScheme rk, fun t => rfl⟩
    have h0 := hgr _ hach
    rw [← h0]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htd := (Finset.mem_filter.1 ht).2
    rw [treeWeight_extendScheme, forestWeight]
    refine congrArg (ξ t * ·) (congrArg Multiset.prod
      (Multiset.map_congr rfl fun a ha => ?_))
    exact (hrk ⟨a, hmemC htd ha⟩).symm
  -- as a polynomial identity in the children variables
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
  -- extract the coefficient of `t₀`'s monomial
  have ht₀mem : t₀ ∈ Finset.univ.filter
      (fun t : T₀ => RootedTree.order (t : RootedTree) = d) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hd.symm⟩
  have hcoeff := congrArg
    (MvPolynomial.coeff
      (Multiset.toFinsupp (RootedTree.branches (t₀ : RootedTree)))) hQ0
  rw [hQ] at hcoeff
  rw [MvPolynomial.coeff_sum] at hcoeff
  rw [Finset.sum_eq_single t₀ (fun t ht hne' => ?_) (fun h => absurd ht₀mem h)]
    at hcoeff
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

/-- **Butcher's Theorem 317A**, packaged: any finite prescription of
elementary weights is realized by some Runge–Kutta method. -/
theorem exists_rk_forall_treeWeight {R : Type w} [Field R] [Infinite R]
    (T₀ : Finset RootedTree) (β : RootedTree → R) :
    ∃ (ι : Type) (_ : Fintype ι) (rk : RungeKutta ι R),
      ∀ t ∈ T₀, treeWeight rk t = β t := by
  obtain ⟨ι, hι, rk, hrk⟩ :=
    exists_rk_treeWeight (T₀.sup RootedTree.order) T₀ le_rfl β
  exact ⟨ι, hι, rk, fun t ht => hrk ⟨t, ht⟩⟩

end Density

end RungeKutta

end BSeries
