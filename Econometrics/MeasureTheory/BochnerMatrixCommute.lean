/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.LinearAlgebra.Matrix.Instances

/-!
# Commutation of Trace and Bochner Integral

This file proves that the trace of a constant matrix times the Bochner integral
of a matrix-valued function equals the integral of the trace, using the
continuous linear map commutation theorem.

## Main results

* `trace_integral_comm` : `tr(A · ∫ f dμ) = ∫ tr(A · f) dμ`.
-/

open MeasureTheory ProbabilityTheory Matrix

/-- The linear map `M ↦ trace(A * M)`. -/
noncomputable def traceMulLinearMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
  Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ
    where
  toFun M := Matrix.trace (A * M)
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply]

/-- `traceMulLinearMap` upgraded to a continuous linear map
(automatic in finite dimensions). -/
noncomputable def traceMulCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
  Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (traceMulLinearMap A)

/-- `tr(A * ∫ f dμ) = ∫ tr(A * f) dμ` for matrix-valued Bochner
integrals. -/
lemma trace_integral_comm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → Matrix (Fin n) (Fin n) ℝ) (hf : Integrable f μ) :
    Matrix.trace (A * ∫ ω, f ω ∂μ) = ∫ ω, Matrix.trace (A * f ω) ∂μ := by
  let L := traceMulCLM A
  -- L applies the trace-mul operation. We use the ContinuousLinearMap commutation theorem.
  have h1 : ∫ ω, L (f ω) ∂μ = L (∫ ω, f ω ∂μ) :=
    ContinuousLinearMap.integral_comp_comm L hf
  exact h1.symm
