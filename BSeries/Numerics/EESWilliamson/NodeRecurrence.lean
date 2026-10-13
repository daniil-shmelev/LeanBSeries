/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniil Shmelev
-/
import BSeries.Numerics.EESWilliamson.BlockSwap

/-!
# The node recurrence forced by the antisymmetric order condition

The diagonal and second superdiagonal of the block-swap identity determine a second-order recurrence for the composite abscissae. Regularity excludes its singular coefficient `r₃ = 1/4`.
-/

namespace BSeries.RungeKutta

open HopfAlgebras Matrix
open scoped BigOperators

noncomputable section

variable {R : Type*} [Field R] [CharZero R] [Invertible (2 : R)] {s : ℕ}

/-- The diagonal part of the master identity gives successive differences of the bidiagonal coefficients. -/
theorem forwardBackward_subdiagonal_difference {rk : RungeKutta (Fin s) R}
    (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → R} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (i : Fin (s + s)) :
    krylovSubdiagonal t (i.val + 1) - krylovSubdiagonal t i.val =
      1 - 2 * rk.forwardBackward.abscissa i := by
  have h := forwardBackward_master_identity hexp hcons hdet hanti ht i i le_rfl
  simp only [Nat.sub_self, Nat.zero_add, stabilityCoeff_one_of_consistent hcons] at h
  change (_ + _ - 1) * 1 + _ * 1 = 0 at h
  linear_combination h

/-- The second superdiagonal gives the undivided node recurrence. -/
theorem forwardBackward_node_recurrence_raw {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hdet : rk.forwardBackward.krylovMatrix.det ≠ 0)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    {t : Fin (s + s - 1) → R} (ht : IsKrylovBidiagonal rk.forwardBackward t)
    (k : ℕ) (hk : k + 2 < s + s) :
    (1 - 4 * stabilityCoeff rk 3) *
        (rk.forwardBackward.abscissa ⟨k, by omega⟩ +
          rk.forwardBackward.abscissa ⟨k + 2, hk⟩) -
      4 * stabilityCoeff rk 3 * rk.forwardBackward.abscissa ⟨k + 1, by omega⟩ +
        6 * stabilityCoeff rk 3 - 1 = 0 := by
  let i₀ : Fin (s + s) := ⟨k, by omega⟩
  let i₁ : Fin (s + s) := ⟨k + 1, by omega⟩
  let i₂ : Fin (s + s) := ⟨k + 2, hk⟩
  have hm := forwardBackward_master_identity hexp hcons hdet hanti ht i₀ i₂ (by
    change k ≤ k + 2; omega)
  have h₀ := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht i₀
  have h₁ := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht i₁
  have h₂ := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht i₂
  simp only [i₀, i₁, i₂, Nat.add_sub_cancel_left] at hm h₀ h₁ h₂
  rw [stabilityCoeff_two_of_hasAntisymOrder hs hexp hcons hanti] at hm
  linear_combination 2 * hm - 2 * stabilityCoeff rk 3 * h₀ -
    2 * stabilityCoeff rk 3 * h₁ - 2 * stabilityCoeff rk 3 * h₂

/-- If `r₃ = 1/4`, the second and third nodes coincide, and the bidiagonal relation kills a nonzero Krylov pivot. -/
theorem stabilityCoeff_three_ne_quarter {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1)) :
    stabilityCoeff rk 3 ≠ 1 / 4 := by
  intro hr
  have hexpc := isExplicit_forwardBackward rk hexp
  have hsub := forwardBackward_subdiagonal_ne_zero (by omega : 0 < s) hexp hcons hanti
  have hdet := det_krylovMatrix_ne_zero hexpc hsub
  obtain ⟨t, ht, ht₀⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  let i₁ : Fin (s + s) := ⟨1, by omega⟩
  let i₂ : Fin (s + s) := ⟨2, by omega⟩
  have hc₁ : rk.forwardBackward.abscissa i₁ = 1 / 2 := by
    have h := forwardBackward_node_recurrence_raw hs hexp hcons hdet hanti ht 0 (by omega)
    rw [hr] at h
    dsimp [i₁]
    linear_combination -h
  have hc₂ : rk.forwardBackward.abscissa i₂ = 1 / 2 := by
    have h := forwardBackward_node_recurrence_raw hs hexp hcons hdet hanti ht 1 (by omega)
    rw [hr] at h
    dsimp [i₂]
    linear_combination -h
  have ht₁ : t ⟨1, by omega⟩ = 1 := by
    have h := forwardBackward_subdiagonal_difference hexp hcons hdet hanti ht i₁
    rw [hc₁] at h
    dsimp [i₁] at h
    rw [krylovSubdiagonal_succ t 1 (by omega),
      krylovSubdiagonal_succ t 0 (by omega), ht₀] at h
    linear_combination h
  have h := ht ⟨1, by omega⟩ i₂
  change rk.forwardBackward.abscissa i₂ * _ = rk.forwardBackward.abscissa i₁ * _ + _ at h
  rw [hc₁, hc₂, ht₁, one_mul] at h
  have hpivot := krylovMatrix_diag_ne_zero hexpc hsub i₂
  apply hpivot
  change stageWeight rk.forwardBackward (PTree.tallTree 2) i₂ = 0
  linear_combination -h

/-- The normalized recurrence is well defined; it will have coefficient `2 cos ω` after the spectral argument. -/
theorem forwardBackward_node_recurrence {rk : RungeKutta (Fin s) R}
    (hs : 2 ≤ s) (hexp : IsExplicit rk) (hcons : weightBullet rk = 1)
    (hanti : ForestAlgebra.Character.HasAntisymOrder
      (Series.toCharacter (series rk)) (2 * s - 1))
    (k : ℕ) (hk : k + 2 < s + s) :
    rk.forwardBackward.abscissa ⟨k + 2, hk⟩ -
        (4 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3)) *
          rk.forwardBackward.abscissa ⟨k + 1, by omega⟩ +
        rk.forwardBackward.abscissa ⟨k, by omega⟩ =
      1 - 2 * stabilityCoeff rk 3 / (1 - 4 * stabilityCoeff rk 3) := by
  have hdet := det_krylovMatrix_ne_zero (isExplicit_forwardBackward rk hexp)
    (forwardBackward_subdiagonal_ne_zero (by omega) hexp hcons hanti)
  obtain ⟨t, ht, _⟩ := exists_forwardBackward_bidiagonal hs hexp hcons hanti
  have hraw := forwardBackward_node_recurrence_raw hs hexp hcons hdet hanti ht k hk
  have hden : 1 - 4 * stabilityCoeff rk 3 ≠ 0 := by
    intro h
    apply stabilityCoeff_three_ne_quarter hs hexp hcons hanti
    linear_combination -h / 4
  field_simp
  linear_combination hraw

end

end BSeries.RungeKutta
