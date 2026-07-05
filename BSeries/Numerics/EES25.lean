/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.Williamson
import BSeries.Numerics.AntisymCriterion
import BSeries.Algebra.ComputableRatFunc

/-!
# The EES(2,5;x) family

The three-stage `EES(2,5;x)` Runge–Kutta family (arXiv:2507.21006,
Proposition 8.4; arXiv:2509.20599, Proposition 2.1), defined for
`x ∉ {1, ±1/2}`:

  `c = (0, (1+2x)/(4(1-x)), 3/(4(1-x)))`, `b = (x, 1/2, 1/2 - x)`.

We prove, for every admissible parameter `x` over any field of
characteristic `≠ 2`:

* the family is explicit, and specialises to the concrete `ees25` scheme
  at `x = 1/4`;
* **the family is Williamson 2N** (arXiv:2509.20599, Proposition 3.1),
  with the closed-form two-register coefficients of equations (14)–(15);
* the stability coefficients `Σᵢ bᵢ = 1`, `Σᵢ bᵢ cᵢ = 1/2` and
  `Σᵢⱼ bᵢ aᵢⱼ cⱼ = 1/8` are independent of `x`, so the linear stability
  polynomial of the whole family is `R(ρ) = 1 + ρ + ρ²/2 + ρ³/8`
  (the algebraic core of arXiv:2509.20599, Theorem 2.2).
-/

namespace BSeries

open HopfAlgebras

namespace RungeKutta

universe v w

variable {R : Type v}

/-- The three-stage `EES(2,5;x)` family (arXiv:2507.21006,
Proposition 8.4), defined for `x ∉ {1, ±1/2}`. -/
def ees25 [Field R] (x : R) : RungeKutta (Fin 3) R :=
  threeStageExplicit R
    ((1 + 2 * x) / (4 * (1 - x)))
    ((4 * x - 1) ^ 2 / (4 * (x - 1) * (1 - 4 * x ^ 2)))
    ((1 - x) / (1 - 4 * x ^ 2))
    x (1 / 2) (1 / 2 - x)

/-- The family is explicit for every parameter. -/
theorem isExplicit_ees25 [Field R] (x : R) :
    IsExplicit (ees25 x) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [ees25, threeStageExplicit]

/-- The Williamson 2N coefficients of the `EES(2,5;x)` family
(arXiv:2509.20599, equations (14)–(15)). -/
def ees25LowStorage [Field R] (x : R) : LowStorage 3 R where
  A := ![0, (4 * x ^ 2 - 2 * x + 1) / (2 * (x - 1)),
    -((4 * x ^ 2 - 2 * x + 1) / ((2 * x - 1) ^ 2 * (2 * x + 1)))]
  B := ![(2 * x + 1) / (4 * (1 - x)), (1 - x) / (1 - 4 * x ^ 2),
    (1 - 2 * x) / 2]

section Entries

variable [Field R] (x : R)

/-! Entrywise evaluation of the family tableau and its low-storage data;
each is a definitional reduction of a vector literal. -/

private theorem famA10 :
    (ees25 x).A 1 0 = (1 + 2 * x) / (4 * (1 - x)) := rfl

private theorem famA20 :
    (ees25 x).A 2 0 =
      (4 * x - 1) ^ 2 / (4 * (x - 1) * (1 - 4 * x ^ 2)) := rfl

private theorem famA21 :
    (ees25 x).A 2 1 = (1 - x) / (1 - 4 * x ^ 2) := rfl

private theorem famB0 : (ees25 x).b 0 = x := rfl

private theorem famB1 : (ees25 x).b 1 = 1 / 2 := rfl

private theorem famB2 : (ees25 x).b 2 = 1 / 2 - x := rfl

private theorem lsA1 :
    (ees25LowStorage x).A 1 =
      (4 * x ^ 2 - 2 * x + 1) / (2 * (x - 1)) := rfl

private theorem lsA2 :
    (ees25LowStorage x).A 2 =
      -((4 * x ^ 2 - 2 * x + 1) / ((2 * x - 1) ^ 2 * (2 * x + 1))) := rfl

private theorem lsB0 :
    (ees25LowStorage x).B 0 = (2 * x + 1) / (4 * (1 - x)) := rfl

private theorem lsB1 :
    (ees25LowStorage x).B 1 = (1 - x) / (1 - 4 * x ^ 2) := rfl

private theorem lsB2 :
    (ees25LowStorage x).B 2 = (1 - 2 * x) / 2 := rfl

private theorem famAbscissa0 : abscissa (ees25 x) 0 = 0 :=
  threeStageExplicit_abscissa_zero _ _ _ _ _ _

private theorem famAbscissa1 :
    abscissa (ees25 x) 1 = (1 + 2 * x) / (4 * (1 - x)) :=
  threeStageExplicit_abscissa_one _ _ _ _ _ _

private theorem famAbscissa2 :
    abscissa (ees25 x) 2 =
      (4 * x - 1) ^ 2 / (4 * (x - 1) * (1 - 4 * x ^ 2)) +
        (1 - x) / (1 - 4 * x ^ 2) :=
  threeStageExplicit_abscissa_two _ _ _ _ _ _

end Entries

section Nonzero

variable [Field R] {x : R}

private theorem aux_ne_zero (hx1 : x ≠ 1) (hx2 : 2 * x ≠ 1)
    (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0) :
    (1 : R) - x ≠ 0 ∧ x - 1 ≠ 0 ∧ (1 : R) - 2 * x ≠ 0 ∧ 2 * x - 1 ≠ 0 ∧
      2 * x + 1 ≠ 0 ∧ (4 : R) ≠ 0 ∧ (1 : R) - 4 * x ^ 2 ≠ 0 ∧
      (1 : R) - x ^ 2 * 4 ≠ 0 ∧
      (1 : R) - x * 2 - x ^ 2 * 4 + x ^ 3 * 8 ≠ 0 ∧
      (4 : R) - x * 4 ≠ 0 ∧ (-2 : R) + x * 2 ≠ 0 ∧
      (-4 : R) + x * 4 + x ^ 2 * 16 - x ^ 3 * 16 ≠ 0 ∧
      (2 * x - 1) ^ 2 ≠ 0 ∧ 4 * ((1 : R) - x) ≠ 0 ∧ 2 * (x - 1) ≠ 0 ∧
      (2 * x - 1) ^ 2 * (2 * x + 1) ≠ 0 ∧
      4 * (x - 1) * ((1 : R) - 4 * x ^ 2) ≠ 0 ∧ (8 : R) ≠ 0 := by
  have h1x : (1 : R) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have h12 : (1 : R) - 2 * x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx2)
  have h21 : 2 * x - 1 ≠ 0 := sub_ne_zero.mpr hx2
  have h21' : 2 * x + 1 ≠ 0 := fun h => hx3 (by linear_combination h)
  have h4 : (4 : R) ≠ 0 := by
    have h22 := mul_ne_zero h2 h2
    intro h
    exact h22 (by linear_combination h)
  have hq : (1 : R) - 4 * x ^ 2 ≠ 0 := by
    have hprod := mul_ne_zero h12 h21'
    intro h
    exact hprod (by linear_combination h)
  have hq2 : (1 : R) - x ^ 2 * 4 ≠ 0 := fun h => hq (by linear_combination h)
  have hcube : (1 : R) - x * 2 - x ^ 2 * 4 + x ^ 3 * 8 ≠ 0 := by
    have hp := mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h21) h21')
      (one_ne_zero (α := R))
    intro h
    exact mul_ne_zero (pow_ne_zero 2 h21) h21' (by linear_combination h)
  have h4x : (4 : R) - x * 4 ≠ 0 := by
    have := mul_ne_zero h4 h1x
    intro h
    exact this (by linear_combination h)
  have hm2 : (-2 : R) + x * 2 ≠ 0 := by
    have := mul_ne_zero h2 hx1'
    intro h
    exact this (by linear_combination h)
  have hbig : (-4 : R) + x * 4 + x ^ 2 * 16 - x ^ 3 * 16 ≠ 0 := by
    have := mul_ne_zero (mul_ne_zero h4 hx1') hq
    intro h
    exact this (by linear_combination h)
  have h8 : (8 : R) ≠ 0 := by
    have := mul_ne_zero h4 h2
    intro h
    exact this (by linear_combination h)
  exact ⟨h1x, hx1', h12, h21, h21', h4, hq, hq2, hcube, h4x, hm2, hbig,
    pow_ne_zero 2 h21, mul_ne_zero h4 h1x, mul_ne_zero h2 hx1',
    mul_ne_zero (pow_ne_zero 2 h21) h21',
    mul_ne_zero (mul_ne_zero h4 hx1') hq, h8⟩

/-- The closed-form two-register coefficients (14)–(15) induce exactly
the `EES(2,5;x)` Butcher tableau. -/
theorem toRK_ees25LowStorage (hx1 : x ≠ 1) (hx2 : 2 * x ≠ 1)
    (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0) :
    (ees25LowStorage x).toRK = ees25 x := by
  obtain ⟨h1x, hx1', h12, h21, h21', h4, hq, hq2, hcube, h4x, hm2, hbig,
    hsq, hd1, hd2, hd3, hd4, h8⟩ := aux_ne_zero hx1 hx2 hx3 h2
  have hk01 : ((0 : Fin 3) : ℕ) + 1 = ((1 : Fin 3) : ℕ) := rfl
  have hk12 : ((1 : Fin 3) : ℕ) + 1 = ((2 : Fin 3) : ℕ) := rfl
  have hlast : (ees25LowStorage x).toRK.b 2 =
      (ees25LowStorage x).B 2 :=
    LowStorage.toRK_b_last _
  have ez : ∀ i j : Fin 3, i ≤ j →
      (ees25LowStorage x).toRK.A i j = (ees25 x).A i j := by
    intro i j hij
    rw [LowStorage.toRK_A_of_le _ hij]
    fin_cases i <;> fin_cases j <;>
      simp_all [ees25, threeStageExplicit]
  have e10 : (ees25LowStorage x).toRK.A 1 0 = (ees25 x).A 1 0 := by
    rw [LowStorage.toRK_A_succ_self _ hk01, lsB0, famA10]
    ring
  have e21 : (ees25LowStorage x).toRK.A 2 1 = (ees25 x).A 2 1 := by
    rw [LowStorage.toRK_A_succ_self _ hk12, lsB1, famA21]
  have e20 : (ees25LowStorage x).toRK.A 2 0 = (ees25 x).A 2 0 := by
    rw [LowStorage.toRK_A_of_lt _ hk01 (by decide),
      LowStorage.toRK_A_succ_self _ hk12, lsB0, lsA1, lsB1, famA20]
    field_simp [hq2, hcube, h4x, hm2, hbig, hsq, hd1, hd2, hd3, hd4, h8]
    ring
  have eb2 : (ees25LowStorage x).toRK.b 2 = (ees25 x).b 2 := by
    rw [hlast, lsB2, famB2, div_eq_iff h2, sub_mul, one_div,
      inv_mul_cancel₀ h2]
    ring
  have eb1 : (ees25LowStorage x).toRK.b 1 = (ees25 x).b 1 := by
    rw [LowStorage.toRK_b_succ _ hk12, hlast, lsB1, lsA2, lsB2, famB1]
    field_simp [hq2, hcube, h4x, hm2, hbig, hsq, hd1, hd2, hd3, hd4, h8]
    have hD : (1 - x * 2 - x ^ 2 * 4 + x ^ 3 * 8) *
        (1 - x * 2 - x ^ 2 * 4 + x ^ 3 * 8)⁻¹ = 1 :=
      mul_inv_cancel₀ hcube
    linear_combination (-1 + 2 * x - 4 * x ^ 2) * hD
  have eb0 : (ees25LowStorage x).toRK.b 0 = (ees25 x).b 0 := by
    rw [LowStorage.toRK_b_succ _ hk01, LowStorage.toRK_b_succ _ hk12, hlast,
      lsB0, lsA1, lsB1, lsA2, lsB2, famB0]
    field_simp [hq2, hcube, h4x, hm2, hbig, hsq, hd1, hd2, hd3, hd4, h8]
    ring
  refine ext (fun i j => ?_) (fun j => ?_)
  · fin_cases i <;> fin_cases j
    · exact ez _ _ (by decide)
    · exact ez _ _ (by decide)
    · exact ez _ _ (by decide)
    · exact e10
    · exact ez _ _ (by decide)
    · exact ez _ _ (by decide)
    · exact e20
    · exact e21
    · exact ez _ _ (by decide)
  · fin_cases j
    · exact eb0
    · exact eb1
    · exact eb2

/-- **The entire `EES(2,5;x)` family is Williamson 2N**
(arXiv:2509.20599, Proposition 3.1), realised by the closed-form
two-register coefficients (14)–(15). -/
theorem isWilliamson2N_ees25 (hx1 : x ≠ 1) (hx2 : 2 * x ≠ 1)
    (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0) :
    IsWilliamson2N (ees25 x) :=
  ⟨ees25LowStorage x, toRK_ees25LowStorage hx1 hx2 hx3 h2⟩

end Nonzero

/-! ### The CF-EES(2,5;x) family

Bazavov's commutator-free lift of the low-storage coefficients produces
the `CF-EES(2,5;x)` integrator on any space carrying an exponential
action (arXiv:2509.20599, equation (16)). -/

/-- The `CF-EES(2,5;x)` commutator-free method (arXiv:2509.20599,
equation (16)): the Bazavov lift of the Williamson 2N form of
`EES(2,5;x)`. -/
noncomputable def cfEES25 [Field R] (x : R) :
    CommutatorFreeMethod (Fin 3) R :=
  (ees25LowStorage x).toCommutatorFree

/-- **On a flat space `CF-EES(2,5;x)` collapses to the classical
`EES(2,5;x)` step** (arXiv:2509.20599, Section 3): under the translation
action the commutator-free step is the Runge–Kutta update
`y + Σⱼ bⱼ Kⱼ`. -/
theorem cfEES25_step_translation [Field R] {x : R} (hx1 : x ≠ 1)
    (hx2 : 2 * x ≠ 1) (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0)
    {E : Type w} [AddCommMonoid E] [Module R E] (K : Fin 3 → E) (y : E) :
    (cfEES25 x).step (ExponentialAction.translation E) K y =
      y + ∑ j, (ees25 x).b j • K j := by
  rw [cfEES25, LowStorage.toCommutatorFree_step_translation,
    toRK_ees25LowStorage hx1 hx2 hx3 h2]

/-- The stage points of `CF-EES(2,5;x)` on a flat space are the classical
Runge–Kutta stage values. -/
theorem cfEES25_stagePoint_translation [Field R] {x : R}
    (hx1 : x ≠ 1) (hx2 : 2 * x ≠ 1) (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0)
    {E : Type w} [AddCommMonoid E] [Module R E] (K : Fin 3 → E) (i : Fin 3)
    (y : E) :
    (cfEES25 x).stagePoint (ExponentialAction.translation E) K i y =
      y + ∑ j, (ees25 x).A i j • K j := by
  rw [cfEES25, LowStorage.toCommutatorFree_stagePoint_translation,
    toRK_ees25LowStorage hx1 hx2 hx3 h2]

/-! ### The paper's reference point `x = 1/10`

arXiv:2509.20599 fixes `x = 1/10` (minimising the leading error) and
records the resulting numerical tables; we machine-check them against the
general closed forms. -/

/-- At `x = 1/10` the Williamson coefficients evaluate to
`B = (1/3, 15/16, 2/5)`, `A = (0, -7/15, -35/32)`
(arXiv:2509.20599, Appendix D). -/
theorem ees25LowStorage_tenth :
    (ees25LowStorage (1 / 10 : ℚ)).B = ![1 / 3, 15 / 16, 2 / 5] ∧
      (ees25LowStorage (1 / 10 : ℚ)).A = ![0, -7 / 15, -35 / 32] := by
  constructor <;> · funext i; revert i; native_decide

/-- The exponential weight table of `CF-EES(2,5;1/10)`
(arXiv:2509.20599, Proposition D.1): row `l` lists the coefficients
`β_{l,i}` of the slopes inside the `l`-th exponential. -/
theorem beta_ees25LowStorage_tenth :
    ∀ l i : Fin 3, (ees25LowStorage (1 / 10 : ℚ)).beta l i =
      ![![1 / 3, 0, 0], ![-7 / 16, 15 / 16, 0],
        ![49 / 240, -7 / 16, 2 / 5]] l i := by
  native_decide

/-- The Euclidean consistency check of Proposition D.1: the columns of
the exponential weight table sum to the quadrature weights,
`Σ_l β_{l,i} = b_i`. -/
theorem sum_beta_eq_b_ees25LowStorage_tenth :
    ∀ i : Fin 3, (∑ l, (ees25LowStorage (1 / 10 : ℚ)).beta l i) =
      (ees25 (1 / 10 : ℚ)).b i := by
  native_decide

/-! ### Stability coefficients

The linear stability polynomial of an explicit three-stage scheme is
`R(ρ) = 1 + (Σᵢ bᵢ) ρ + (Σᵢ bᵢ cᵢ) ρ² + (Σᵢⱼ bᵢ aᵢⱼ cⱼ) ρ³`. The three
coefficients below are independent of `x`, giving
`R(ρ) = 1 + ρ + ρ²/2 + ρ³/8` for the whole family — the algebraic core
of arXiv:2509.20599, Theorem 2.2. -/

/-- The quadrature weights of `EES(2,5;x)` sum to one, for every `x`
(the `ρ`-coefficient of the stability polynomial). -/
theorem weightBullet_ees25 [Field R] {x : R} (h2 : (2 : R) ≠ 0) :
    weightBullet (ees25 x) = 1 := by
  rw [weightBullet, Fin.sum_univ_three, famB0, famB1, famB2,
    show x + 1 / 2 + (1 / 2 - x) = 1 / 2 + 1 / 2 from by ring,
    ← add_div, show (1 : R) + 1 = 2 from by norm_num, div_self h2]

/-- The `ρ²`-coefficient of the stability polynomial of `EES(2,5;x)` is
`1/2`, independent of `x` (equivalently, the order-two chain condition
holds for the whole family). -/
theorem weight_chain2_ees25 [Field R] {x : R} (hx1 : x ≠ 1)
    (hx2 : 2 * x ≠ 1) (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0) :
    weight (ees25 x) PTree.chain2 = 1 / 2 := by
  obtain ⟨h1x, hx1', h12, h21, h21', h4, hq, hq2, hcube, h4x, hm2, hbig,
    hsq, hd1, hd2, hd3, hd4, h8⟩ := aux_ne_zero hx1 hx2 hx3 h2
  rw [weight, Fin.sum_univ_three]
  simp only [stageWeight_chain2]
  rw [famAbscissa0, famAbscissa1, famAbscissa2, famB0, famB1, famB2]
  field_simp [hq2, hcube, h4x, hm2, hbig, hsq, hd1, hd2, hd3, hd4, h8]
  ring

/-- The `ρ³`-coefficient of the stability polynomial of `EES(2,5;x)` is
`1/8`, independent of `x` (arXiv:2509.20599, Theorem 2.2). -/
theorem weight_chain3_ees25 [Field R] {x : R} (hx1 : x ≠ 1)
    (hx2 : 2 * x ≠ 1) (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0) :
    weight (ees25 x) PTree.chain3 = 1 / 8 := by
  obtain ⟨h1x, hx1', h12, h21, h21', h4, hq, hq2, hcube, h4x, hm2, hbig,
    hsq, hd1, hd2, hd3, hd4, h8⟩ := aux_ne_zero hx1 hx2 hx3 h2
  rw [weight, Fin.sum_univ_three]
  simp only [stageWeight_chain3, Fin.sum_univ_three]
  rw [famAbscissa0, famAbscissa1, famAbscissa2, famB0, famB1, famB2,
    famA10, famA20, famA21,
    show (ees25 x).A 0 0 = 0 from rfl,
    show (ees25 x).A 0 1 = 0 from rfl,
    show (ees25 x).A 0 2 = 0 from rfl,
    show (ees25 x).A 1 1 = 0 from rfl,
    show (ees25 x).A 1 2 = 0 from rfl,
    show (ees25 x).A 2 2 = 0 from rfl]
  field_simp [hq2, hcube, h4x, hm2, hbig, hsq, hd1, hd2, hd3, hd4, h8]
  ring

/-! ### Order two, symbolically -/

/-- **`EES(2,5;x)` has order two for every admissible parameter** over
any field of characteristic `≠ 2`. -/
theorem hasOrder_two_ees25 [Field R] {x : R} (hx1 : x ≠ 1)
    (hx2 : 2 * x ≠ 1) (hx3 : 2 * x ≠ -1) (h2 : (2 : R) ≠ 0) :
    HasOrder (ees25 x) 2 := by
  rw [hasOrder_iff_treeWeight]
  intro τ hτ
  have hpos := RootedTree.order_pos τ
  have h12 : RootedTree.order τ = 1 ∨ RootedTree.order τ = 2 := by omega
  rcases h12 with h | h
  · rw [RootedTree.eq_bullet_of_order_one h,
      show RootedTree.bullet = RootedTree.ofPTree PTree.bullet from rfl,
      treeWeight_ofPTree, RootedTree.treeFactorial_ofPTree,
      show PTree.bullet = PTree.node [] from rfl]
    have hval : weight (ees25 x) (PTree.node []) = 1 := by
      rw [show (PTree.node [] : PTree) = PTree.bullet from rfl,
        weight_bullet]
      exact weightBullet_ees25 (x := x) h2
    rw [hval]
    norm_num [PTree.treeFactorial]
  · rw [RootedTree.eq_chain_of_order_two h, graft_singleton_bullet,
      treeWeight_ofPTree, RootedTree.treeFactorial_ofPTree]
    have hval : weight (ees25 x) (PTree.node [PTree.node []]) = 1 / 2 :=
      weight_chain2_ees25 hx1 hx2 hx3 h2
    rw [hval,
      show (PTree.treeFactorial (PTree.node [PTree.node []]) : ℕ) = 2 from
        rfl, one_div]
    norm_num

/-! ### The generic parameter: `EES(2,5;X)` is an EES(2,5) scheme

Instantiating at the generic parameter `X : CRatFunc ℚ` — i.e. working
with rational functions of an indeterminate — the remaining order
conditions of arXiv:2507.21006, Section 8 hold as identities of rational
functions, verified by `native_decide` over the computable field
`CRatFunc ℚ`. -/

section Generic

open CRatFunc

private theorem gx1 : (X : CRatFunc ℚ) ≠ 1 := by native_decide

private theorem gx2 : 2 * (X : CRatFunc ℚ) ≠ 1 := by native_decide

private theorem gx3 : 2 * (X : CRatFunc ℚ) ≠ -1 := by native_decide

private theorem g2 : (2 : CRatFunc ℚ) ≠ 0 := by native_decide

/-- `EES(2,5;X)` has order two at the generic parameter. -/
theorem hasOrder_two_ees25_generic :
    HasOrder (ees25 (X : CRatFunc ℚ)) 2 :=
  hasOrder_two_ees25 gx1 gx2 gx3 g2

/-- `EES(2,5;X)` does not have order three: the cherry-tree condition
fails as an identity of rational functions. -/
theorem not_hasOrder_three_ees25_generic :
    ¬ HasOrder (ees25 (X : CRatFunc ℚ)) 3 := by
  intro h
  rw [hasOrder_iff_treeWeight] at h
  have hval := h (RootedTree.ofPTree
    (PTree.node [PTree.node [], PTree.node []])) (by
      rw [RootedTree.order_ofPTree]
      rfl)
  rw [treeWeight_ofPTree, RootedTree.treeFactorial_ofPTree] at hval
  rw [show (PTree.treeFactorial
    (PTree.node [PTree.node [], PTree.node []]) : ℕ) = 3 from rfl] at hval
  have hne : weight (ees25 (X : CRatFunc ℚ))
      (PTree.node [PTree.node [], PTree.node []]) *
      ((3 : ℕ) : CRatFunc ℚ) ≠ 1 := by
    native_decide
  refine hne ?_
  rw [hval]
  have h30 : ((3 : ℕ) : CRatFunc ℚ) ≠ 0 := by native_decide
  field_simp

set_option maxHeartbeats 2000000 in
private theorem weight_compose_eq_ees25_generic :
    ∀ t ∈ (List.range 6).flatMap PTree.treesOfOrder,
      weight (compose (ees25 (X : CRatFunc ℚ)) (ees25 X)) t =
        weight (compose (adjointScheme (ees25 X)) (ees25 X)) t := by
  native_decide

/-- **`EES(2,5;X)` has antisymmetric order five at the generic
parameter**: the composed-weight identities hold as identities of
rational functions on all planar trees of order at most five. -/
theorem hasAntisymOrder_five_ees25_generic :
    ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series (ees25 (X : CRatFunc ℚ)))) 5 := by
  rw [hasAntisymOrder_iff_weight_compose_eq]
  intro t ht
  refine weight_compose_eq_ees25_generic t ?_
  refine List.mem_flatMap.2 ⟨PTree.order t, ?_, PTree.mem_treesOfOrder t⟩
  exact List.mem_range.2 (by have := PTree.order_pos t; omega)

set_option maxHeartbeats 2000000 in
/-- `EES(2,5;X)` does not have antisymmetric order six: the six-chain is
a witness at the generic parameter. -/
theorem not_hasAntisymOrder_six_ees25_generic :
    ¬ ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series (ees25 (X : CRatFunc ℚ)))) 6 := by
  rw [hasAntisymOrder_iff_weight_compose_eq]
  intro h
  have h1 := h (PTree.tallTree 5) (by rw [PTree.order_tallTree])
  have h2 : weight (compose (ees25 (X : CRatFunc ℚ)) (ees25 X))
      (PTree.tallTree 5) ≠
      weight (compose (adjointScheme (ees25 X)) (ees25 X))
        (PTree.tallTree 5) := by
    native_decide
  exact h2 h1

/-- **The `EES(2,5;x)` family is an `EES(2,5)` scheme at the generic
parameter** (arXiv:2507.21006, Section 8): explicit, of order exactly
two, and of antisymmetric order exactly five, as identities of rational
functions in the parameter. -/
theorem isEES_ees25_generic : IsEES (ees25 (X : CRatFunc ℚ)) 2 5 :=
  ⟨isExplicit_ees25 X,
    ⟨hasOrder_two_ees25_generic, not_hasOrder_three_ees25_generic⟩,
    ⟨hasAntisymOrder_five_ees25_generic,
      not_hasAntisymOrder_six_ees25_generic⟩⟩

end Generic

end RungeKutta

end BSeries
