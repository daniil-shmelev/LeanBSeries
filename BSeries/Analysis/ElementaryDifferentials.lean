/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.RungeKutta
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Elementary differentials: the analytic semantics of B-series

For a vector field `f : E → E`, the **elementary differential** of a
rooted tree is defined recursively by
`F(τ)(y) = f⁽ᵏ⁾(y)[F(τ₁)(y), …, F(τₖ)(y)]` where `τ₁, …, τₖ` are the
branches of `τ` (`elemDiff`). This is the semantics under which the
algebraic order conditions of `BSeries.Numerics.RungeKutta` speak about
actual ODEs: the derivatives of a solution of `y' = f(y)` are sums of
elementary differentials.

This file provides:

* the general recursive definition `elemDiff` on planar trees;
* the **flow-derivative theorems** at the first orders: for a solution
  of `y' = f(y)`, `y' = F(•)(y)` and `y'' = F([•])(y)` — the first
  instances of the classical expansion whose general form (over all
  trees of order `k`, with monotone-labelling multiplicities) is the
  content of Butcher's Taylor expansion;
* the **local error bound of the explicit Euler method**:
  `‖y(h) − y(0) − h·f(y(0))‖ ≤ L·M·h²` for Lipschitz `f` — the
  analytic realisation of the order-1 conditions
  (`explicitEuler_hasOrderOne`).

The higher flow derivatives and the general order-`p` local error
theorem for arbitrary tableaux are future work; the definitions here
fix their semantics.
-/

namespace BSeries

open HopfAlgebras
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Elementary differentials -/

/-- Tree order is at most the order of any containing list. -/
private theorem order_le_orderList (t : PTree) :
    ∀ ts : List PTree, t ∈ ts → PTree.order t ≤ PTree.orderList ts
  | [], h => nomatch h
  | u :: ts, h => by
      rcases List.mem_cons.mp h with h | h
      · subst h
        rw [PTree.orderList_cons]
        omega
      · have := order_le_orderList t ts h
        rw [PTree.orderList_cons]
        omega

/-- The order of every branch is smaller than the order of the tree. -/
private theorem order_get_lt (ts : List PTree) (i : Fin ts.length) :
    PTree.order ts[i] < PTree.order (PTree.node ts) := by
  have hle := order_le_orderList ts[i] ts (List.getElem_mem _)
  have h := PTree.order_eq_one_add_orderList_children (PTree.node ts)
  rw [show (PTree.node ts).children = ts from rfl] at h
  omega

/-- The **elementary differential** of a planar rooted tree with
respect to a vector field: `F(•) = f` and
`F([τ₁ ⋯ τₖ])(y) = f⁽ᵏ⁾(y)[F(τ₁)(y), …, F(τₖ)(y)]`. -/
noncomputable def elemDiff (f : E → E) : PTree → E → E
  | .node ts, y =>
      iteratedFDeriv ℝ ts.length f y fun i => elemDiff f ts[i] y
  termination_by t => PTree.order t
  decreasing_by exact order_get_lt ts i

theorem elemDiff_node (f : E → E) (ts : List PTree) (y : E) :
    elemDiff f (.node ts) y =
      iteratedFDeriv ℝ ts.length f y fun i => elemDiff f ts[i] y := by
  rw [elemDiff]

/-- The elementary differential of the single vertex is the vector
field itself. -/
@[simp]
theorem elemDiff_bullet (f : E → E) (y : E) :
    elemDiff f (.node []) y = f y := by
  rw [elemDiff_node]
  exact iteratedFDeriv_zero_apply _

/-- The elementary differential of the 2-chain is `f'(y)[f(y)]`. -/
theorem elemDiff_chain2 (f : E → E) (y : E) :
    elemDiff f (.node [.node []]) y = fderiv ℝ f y (f y) := by
  rw [elemDiff_node]
  have h : (fun i : Fin ([PTree.node []] : List PTree).length =>
      elemDiff f ([PTree.node []])[i] y) = fun _ => f y := by
    funext i
    fin_cases i
    exact elemDiff_bullet f y
  exact (congrArg (iteratedFDeriv ℝ
    ([PTree.node []] : List PTree).length f y) h).trans
    (iteratedFDeriv_one_apply _)

/-! ### Flow derivatives: `y' = f(y)` differentiates along trees -/

section Flow

variable {f : E → E} {y : ℝ → E}

/-- **First flow derivative**: `y' = F(•)(y)`. -/
theorem flow_deriv_one (hy : ∀ t, HasDerivAt y (f (y t)) t) (t : ℝ) :
    deriv y t = elemDiff f (.node []) (y t) := by
  rw [(hy t).deriv, elemDiff_bullet]

/-- **Second flow derivative**: `y'' = F([•])(y)` for a `C¹` vector
field. -/
theorem flow_deriv_two (hf : ContDiff ℝ 1 f)
    (hy : ∀ t, HasDerivAt y (f (y t)) t) (t : ℝ) :
    deriv (deriv y) t = elemDiff f (.node [.node []]) (y t) := by
  have hderiv : deriv y = fun s => f (y s) := funext fun s => (hy s).deriv
  rw [hderiv]
  have hcomp : HasDerivAt (fun s => f (y s))
      (fderiv ℝ f (y t) (f (y t))) t := by
    have hfd : HasFDerivAt f (fderiv ℝ f (y t)) (y t) :=
      (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
    exact (hfd.comp_hasDerivAt t (hy t))
  rw [hcomp.deriv, elemDiff_chain2]

end Flow

/-! ### The Euler local error: order-1 conditions analytically -/

/-- **Local error of the explicit Euler method**: for a Lipschitz
vector field bounded by `M` along the solution, one Euler step of size
`h` deviates from the flow by at most `L·M·h²` — the analytic content
of the order-1 conditions (`explicitEuler_hasOrderOne`). -/
theorem euler_local_error {f : E → E} {y : ℝ → E} {L M : ℝ≥0} {h : ℝ}
    (hh : 0 ≤ h) (hL : LipschitzWith L f)
    (hy : ∀ t, HasDerivAt y (f (y t)) t)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) h, ‖f (y t)‖ ≤ M) :
    ‖y h - y 0 - h • f (y 0)‖ ≤ L * M * h ^ 2 := by
  -- first: the solution moves at speed at most `M`
  have hyM : ∀ t ∈ Set.Icc (0 : ℝ) h, ‖y t - y 0‖ ≤ (M : ℝ) * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s _ => (hy s).hasDerivWithinAt)
      (fun s hs => hM s (Set.Ico_subset_Icc_self hs))
  -- the defect of the Euler step
  set g : ℝ → E := fun t => y t - y 0 - t • f (y 0) with hg
  have hgderiv : ∀ t ∈ Set.Icc (0 : ℝ) h,
      HasDerivWithinAt g (f (y t) - f (y 0)) (Set.Icc 0 h) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => y s - y 0) (f (y t)) t :=
      (hy t).sub_const (y 0)
    have h2 : HasDerivAt (fun s : ℝ => s • f (y 0)) (f (y 0)) t := by
      simpa using (hasDerivAt_id t).smul_const (f (y 0))
    exact (h1.sub h2).hasDerivWithinAt
  have hgbound : ∀ t ∈ Set.Ico (0 : ℝ) h,
      ‖f (y t) - f (y 0)‖ ≤ (L : ℝ) * M * h := by
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) h := Set.Ico_subset_Icc_self ht
    calc ‖f (y t) - f (y 0)‖ ≤ (L : ℝ) * ‖y t - y 0‖ := by
          simpa [dist_eq_norm] using hL.dist_le_mul (y t) (y 0)
      _ ≤ (L : ℝ) * ((M : ℝ) * (t - 0)) :=
          mul_le_mul_of_nonneg_left (hyM t ht') (by positivity)
      _ ≤ (L : ℝ) * ((M : ℝ) * h) := by
          have h1 : t - 0 ≤ h := by
            have := ht'.2
            linarith
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
      _ = (L : ℝ) * M * h := by ring
  have hfinal := norm_image_sub_le_of_norm_deriv_le_segment'
    hgderiv hgbound h ⟨hh, le_rfl⟩
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero] at hfinal
  calc ‖y h - y 0 - h • f (y 0)‖ = ‖g h‖ := rfl
    _ ≤ (L : ℝ) * M * h * (h - 0) := hfinal
    _ = (L : ℝ) * M * h ^ 2 := by ring

end BSeries
