/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.Probability.LpConvergence
import Econometrics.LinearAlgebra.Matrix.AnnihilatorTrace
import Econometrics.LinearAlgebra.Matrix.TraceNorm

/-!
# Trace Concentration for Quadratic Forms

This file defines the generic trace-variance bound for quadratic forms of a noise
process and proves that the variance of the annihilator quadratic form vanishes
at rate `O(1/T)`.

## Main definitions

* `ProbabilityTheory.HasTraceVarianceBound` : `Var(eᵀPe) ≤ K · tr(PPᵀ)`.

## Main results

* `traceVariance_tendsto_zero` : the annihilator variance tends to zero.
-/

open MeasureTheory Filter Topology ProbabilityTheory Matrix

namespace ProbabilityTheory

/--
Phase 2.4: Generic Consequence of Bounded 4th Moments (Assumption 2.2d).
For a weakly dependent process with bounded 4th moments, the variance of any
quadratic form P is bounded by K * Tr(P Pᵀ).
-/
def HasTraceVarianceBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {T : ℕ}
    (e : Ω → Matrix (Fin T) (Fin 1) ℝ) (K : ℝ) : Prop :=
  ∀ P : Matrix (Fin T) (Fin T) ℝ,
    ∫ ω, (((e ω)ᵀ * P * (e ω)) 0 0 - ∫ ω', (((e ω')ᵀ * P * (e ω')) 0 0) ∂μ)^2 ∂μ ≤
        K * Matrix.trace (P * Pᵀ)

/--
If the noise process satisfies the generic trace-variance bound uniformly with constant K,
and we scale the irrelevant subspace projection matrix by T⁻¹, the variance vanishes at rate K/T.
This explicitly bridges the 4th moment bound to the required concentration limit.
-/
lemma traceVariance_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : (T : ℕ) → Ω → Matrix (Fin T) (Fin 1) ℝ)
    (K : ℝ) (hK_pos : 0 ≤ K)
    (h_var_bound : ∀ T, HasTraceVarianceBound μ (e T) K)
    (N_irrel : ℕ) (U_mat : (T : ℕ) → Matrix (Fin T) (Fin N_irrel) ℝ) :
    Tendsto (fun (T : ℕ) => ∫ ω,
      (((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat T) * e T ω)) -
       (∫ ω', ((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat T) * e T ω')) ∂μ))^2 ∂μ)
    atTop (nhds 0) := by
  have h_bound : ∀ T : ℕ, 0 < T →
      ∫ ω, (((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat T) * e T ω)) -
            (∫ ω', ((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat T) * e T ω')) ∂μ))^2 ∂μ
      ≤ K * (T : ℝ)⁻¹ := by
    intro T hT
    let P := (T : ℝ)⁻¹ • annihilator (U_mat T)
    have h_quad : ∀ ω, ((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat T) * e T ω)) =
        (((e T ω)ᵀ * P * (e T ω)) 0 0) := by
      intro ω
      have h_sq : sqNorm (annihilator (U_mat T) * e T ω) =
          Matrix.trace ((annihilator (U_mat T))ᵀ * annihilator (U_mat T) * (e T ω * (e T ω)ᵀ)) := by
        exact sqNorm_mul_eq_trace (annihilator (U_mat T)) (e T ω)
      have h_symm := annihilator_transpose (U_mat T)
      have h_idemp := annihilator_mul_self (U_mat T)
      have h_trace_equiv : sqNorm (annihilator (U_mat T) * e T ω) =
          Matrix.trace (annihilator (U_mat T) * (e T ω * (e T ω)ᵀ)) := by
        rw [h_sq, h_symm, h_idemp]
      have h_RHS : (((e T ω)ᵀ * P * (e T ω)) 0 0) = Matrix.trace (P * (e T ω * (e T ω)ᵀ)) := by
        have hd : (((e T ω)ᵀ * P * (e T ω)) 0 0) = Matrix.trace (((e T ω)ᵀ * P) * (e T ω)) := by
          dsimp [Matrix.trace, Matrix.diag]
          rw [Fin.sum_univ_one]
        rw [hd, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      rw [h_trace_equiv, h_RHS]
      dsimp [P]
      rw [Matrix.smul_mul, Matrix.trace_smul]
      rfl
    simp_rw [h_quad]
    have h_var := h_var_bound T P
    have h_trace_P : Matrix.trace (P * Pᵀ) = (T : ℝ)⁻¹^2 * Matrix.trace (annihilator (U_mat T)) :=
        by
      dsimp [P]
      have h_symm := annihilator_transpose (U_mat T)
      have h_idemp := annihilator_mul_self (U_mat T)
      rw [Matrix.transpose_smul, h_symm]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h_idemp]
      rw [Matrix.trace_smul]
      simp [smul_eq_mul, sq]
    have h_trace_bound : Matrix.trace (annihilator (U_mat T)) ≤ (T : ℝ) := by
      rw [trace_annihilator_eq_codim]
      have h_rank_pos : 0 ≤ (Matrix.rank (U_mat T) : ℝ) := Nat.cast_nonneg _
      linarith
    calc ∫ ω, (((e T ω)ᵀ * P * (e T ω)) 0 0 - ∫ ω', (((e T ω')ᵀ * P * (e T ω')) 0 0) ∂μ)^2 ∂μ
      _ ≤ K * Matrix.trace (P * Pᵀ) := h_var
      _ = K * ((T : ℝ)⁻¹^2 * Matrix.trace (annihilator (U_mat T))) := by rw [h_trace_P]
      _ = K * (T : ℝ)⁻¹^2 * Matrix.trace (annihilator (U_mat T)) := by ring
      _ ≤ K * (T : ℝ)⁻¹^2 * (T : ℝ) := by
          apply mul_le_mul_of_nonneg_left h_trace_bound
          apply mul_nonneg hK_pos
          exact sq_nonneg _
      _ = K * ((T : ℝ)⁻¹ * (T : ℝ)⁻¹ * (T : ℝ)) := by ring
      _ = K * ((T : ℝ)⁻¹ * ((T : ℝ)⁻¹ * (T : ℝ))) := by rw [mul_assoc]
      _ = K * ((T : ℝ)⁻¹ * 1) := by
          congr 2
          have hT_ne : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hT)
          exact inv_mul_cancel₀ hT_ne
      _ = K * (T : ℝ)⁻¹ := by ring
  have h_lim : Tendsto (fun T : ℕ => K * (T : ℝ)⁻¹) atTop (nhds 0) := by
    have h_zero : (0 : ℝ) = K * 0 := by ring
    rw [h_zero]
    exact Tendsto.const_mul K (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
  · filter_upwards with T
    apply integral_nonneg
    intro ω
    exact sq_nonneg _
  · have h_pos : ∀ᶠ T : ℕ in atTop, 0 < T := by
      have h1 : ∀ᶠ (T : ℕ) in atTop, 1 ≤ T := Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩
      filter_upwards [h1] with T hT
      exact Nat.pos_of_ne_zero (by omega)
    filter_upwards [h_pos] with T hT
    exact h_bound T hT

end ProbabilityTheory
