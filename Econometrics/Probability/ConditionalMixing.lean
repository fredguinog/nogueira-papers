/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.Probability.LpConvergence

/-!
# Conditional Mixing Bounds and Cross-Sectional Orthogonality

This file defines structures encoding the consequence of conditional
expectation decoupling for mixing arrays and cross-sectional
orthogonality, and proves that the associated cross-terms vanish
in L² when the coefficient process has bounded second moments.

## Main definitions

* `ProbabilityTheory.CondMixingBound` : bound on `E[(cᵀe)²]` by
  `C · E[‖c‖²]`.
* `ProbabilityTheory.CrossSectionalOrthogonalityBound` : bound on
  `E[(cᵀe)²]` by `K · T`.

## Main results

* `ProbabilityTheory.crossTerm_l2_tendsto` : the scaled cross-term
  variance tends to zero under a `CondMixingBound`.
* `ProbabilityTheory.cross_term_vanishes_by_orthogonality` :
  `T⁻¹ c'e →ₚ 0` under a `CrossSectionalOrthogonalityBound`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open Matrix

namespace ProbabilityTheory

/-! ### Conditional mixing bound -/

/-- Encodes the consequence of conditional expectation decoupling
for mixing arrays. If `e` is a mean-zero mixing sequence and `c`
is a random coefficient measurable with respect to the conditioning
σ-algebra, then `E[(c'e)²] ≤ C · E[‖c‖²]`. -/
structure CondMixingBound {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (c e : (T : ℕ) → Ω →
      Matrix (Fin T) (Fin 1) ℝ) where
  C : ℝ
  hC_pos : 0 < C
  bound : ∀ T,
    ∫ ω, (((c T ω)ᵀ * e T ω) 0 0) ^ 2 ∂μ ≤
      C * ∫ ω, ((c T ω)ᵀ * c T ω) 0 0 ∂μ

/-- The scaled cross-term variance tends to zero under a
`CondMixingBound` with bounded coefficient norm. -/
lemma crossTerm_l2_tendsto {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    (c e : (T : ℕ) → Ω →
      Matrix (Fin T) (Fin 1) ℝ)
    (b : CondMixingBound μ c e)
    (h_c_bounded : ∃ M, ∀ (T : ℕ),
      (T : ℝ)⁻¹ *
        ∫ ω, ((c T ω)ᵀ * c T ω) 0 0 ∂μ ≤ M) :
    Tendsto (fun (T : ℕ) =>
      ∫ ω, ((T : ℝ)⁻¹ *
        ((c T ω)ᵀ * e T ω) 0 0) ^ 2 ∂μ)
      atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := h_c_bounded
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
  · have h_upper : Tendsto
        (fun (T : ℕ) => (T : ℝ)⁻¹ * (b.C * M))
        atTop (nhds 0) := by
      have h_zero : (0 : ℝ) = 0 * (b.C * M) := by
        ring
      rw [h_zero]
      exact Tendsto.mul
        (tendsto_inv_atTop_zero.comp
          tendsto_natCast_atTop_atTop)
        tendsto_const_nhds
    exact h_upper
  · apply Filter.Eventually.of_forall
    intro T; apply integral_nonneg
    intro ω; exact sq_nonneg _
  · apply Filter.Eventually.of_forall
    intro T
    have heq : ∀ ω,
        ((T : ℝ)⁻¹ *
          ((c T ω)ᵀ * e T ω) 0 0) ^ 2 =
        (T : ℝ)⁻¹ ^ 2 *
          (((c T ω)ᵀ * e T ω) 0 0) ^ 2 := by
      intro ω; ring
    simp_rw [heq]
    rw [integral_const_mul]
    calc (T : ℝ)⁻¹ ^ 2 *
        ∫ ω, (((c T ω)ᵀ * e T ω) 0 0) ^ 2 ∂μ
      ≤ (T : ℝ)⁻¹ ^ 2 *
          (b.C * ∫ ω,
            ((c T ω)ᵀ * c T ω) 0 0 ∂μ) :=
        mul_le_mul_of_nonneg_left (b.bound T)
          (by positivity)
      _ = (T : ℝ)⁻¹ * b.C *
          ((T : ℝ)⁻¹ *
            ∫ ω, ((c T ω)ᵀ * c T ω) 0 0 ∂μ) :=
        by ring
      _ ≤ (T : ℝ)⁻¹ * b.C * M := by
          by_cases hT : (T : ℝ) = 0
          · rw [hT]; simp
          · exact mul_le_mul_of_nonneg_left (hM T)
              (mul_nonneg (by positivity)
                b.hC_pos.le)
      _ = (T : ℝ)⁻¹ * (b.C * M) := by ring

/-! ### Cross-sectional orthogonality bound -/

/-- Encodes cross-sectional orthogonality (Assumption 2.2a).
The variance of the inner product `c'e` grows at most linearly
with `T`, so the scaled cross term `T⁻¹ c'e` converges to 0 in
L² at rate `1/T`. -/
structure CrossSectionalOrthogonalityBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (c e : (T : ℕ) → Ω →
      Matrix (Fin T) (Fin 1) ℝ) where
  K : ℝ
  h_var_bound : ∀ T, 0 < T →
    ∫ ω, (((c T ω)ᵀ * e T ω) 0 0) ^ 2 ∂μ ≤
      K * (T : ℝ)

/-- Given a cross-sectional orthogonality bound
`E[(c'e)²] ≤ K·T`, the scaled cross term `T⁻¹ c'e`
converges to 0 in probability via the L² route:
`E[(T⁻¹ c'e)²] = T⁻² E[(c'e)²] ≤ K/T → 0`. -/
lemma cross_term_vanishes_by_orthogonality
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (c e : (T : ℕ) → Ω →
      Matrix (Fin T) (Fin 1) ℝ)
    (b : CrossSectionalOrthogonalityBound μ c e)
    (h_meas : ∀ (T : ℕ),
      AEStronglyMeasurable (fun ω =>
        (T : ℝ)⁻¹ *
          ((c T ω)ᵀ * e T ω) 0 0) μ)
    (h_int : ∀ (T : ℕ),
      Integrable (fun ω =>
        ((T : ℝ)⁻¹ *
          ((c T ω)ᵀ * e T ω) 0 0 - 0) ^ 2) μ) :
    TendstoInMeasure μ
      (fun (T : ℕ) ω => (T : ℝ)⁻¹ *
        ((c T ω)ᵀ * e T ω) 0 0)
      atTop (fun _ => 0) := by
  have h_L2 : Tendsto (fun (T : ℕ) =>
      ∫ ω, ((T : ℝ)⁻¹ *
        ((c T ω)ᵀ * e T ω) 0 0 - 0) ^ 2 ∂μ)
      atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
    · have h_lim : Tendsto
          (fun T : ℕ => b.K * (T : ℝ)⁻¹)
          atTop (nhds 0) := by
        have h_zero : (0 : ℝ) = b.K * 0 := by
          ring
        rw [h_zero]
        exact Tendsto.const_mul b.K
          (tendsto_inv_atTop_zero.comp
            tendsto_natCast_atTop_atTop)
      exact h_lim
    · filter_upwards with T
      apply integral_nonneg
      intro ω; exact sq_nonneg _
    · have h_pos : ∀ᶠ T : ℕ in atTop,
          0 < T := by
        filter_upwards
          [Filter.eventually_atTop.mpr
            ⟨1, fun _ h => h⟩] with T hT
        exact Nat.pos_of_ne_zero (by omega)
      filter_upwards [h_pos] with T hT
      have heq : ∀ ω,
          ((T : ℝ)⁻¹ *
            ((c T ω)ᵀ * e T ω) 0 0 - 0) ^ 2 =
          (T : ℝ)⁻¹ ^ 2 *
            (((c T ω)ᵀ * e T ω) 0 0) ^ 2 := by
        intro ω; ring
      simp_rw [heq]
      rw [integral_const_mul]
      calc (T : ℝ)⁻¹ ^ 2 *
          ∫ ω, (((c T ω)ᵀ * e T ω) 0 0) ^ 2 ∂μ
        _ ≤ (T : ℝ)⁻¹ ^ 2 *
            (b.K * (T : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (b.h_var_bound T hT) (sq_nonneg _)
        _ = b.K * ((T : ℝ)⁻¹ *
            ((T : ℝ)⁻¹ * (T : ℝ))) := by ring
        _ = b.K * ((T : ℝ)⁻¹ * 1) := by
            congr 2
            exact inv_mul_cancel₀
              (Nat.cast_ne_zero.mpr
                (ne_of_gt hT))
        _ = b.K * (T : ℝ)⁻¹ := by ring
  exact l2_tendstoInMeasure μ h_meas h_int h_L2

end ProbabilityTheory
