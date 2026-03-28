/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.LinearAlgebra.Matrix.Instances

/-!
# Covariance Matrix

This file defines the covariance matrix of a vector-valued random variable
and provides the key trace identity under scalar covariance.

## Main definitions

* `ProbabilityTheory.covMatrix` : the covariance matrix `E[(X − μ)(X − μ)ᵀ]`.
* `ProbabilityTheory.HasScalarCovariance` : the hypothesis `Cov(X) = σ² I`.

## Main results

* `trace_mul_scalar_cov` : `tr(A · Cov) = σ² · tr(A)`.
-/

open MeasureTheory ProbabilityTheory Matrix


variable {Ω : Type*} [MeasurableSpace Ω]

/-- The covariance matrix of a vector-valued random variable:
`Cov(f) = E[(f − μ)(f − μ)ᵀ]`.
noncomputable for a vector-valued random variable -/
noncomputable def covMatrix {n : ℕ} (μ : Measure Ω) (f : Ω →
    Matrix (Fin n) (Fin 1) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∫ ω, (f ω - ∫ ω', f ω' ∂μ) * (f ω - ∫ ω', f ω' ∂μ)ᵀ ∂μ

/-- Covariance simplifies to the uncentered outer product if the mean is zero -/
lemma covMatrix_of_mean_zero {n : ℕ} {μ : Measure Ω} {f : Ω → Matrix (Fin n) (Fin 1) ℝ}
    (h_mean : ∫ ω, f ω ∂μ = 0) :
    covMatrix μ f = ∫ ω, f ω * (f ω)ᵀ ∂μ := by
  unfold covMatrix
  simp_rw [h_mean, sub_zero]

/-- Canonical hypothesis form for scalar covariance: Cov(f) = σ² * I -/
def HasScalarCovariance {n : ℕ} (μ : Measure Ω) (f : Ω →
    Matrix (Fin n) (Fin 1) ℝ) (σ_sq : ℝ) : Prop :=
  covMatrix μ f = σ_sq • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- The key consequence lemma: tr(A * Cov(f)) = σ² * tr(A) -/
lemma trace_mul_scalar_cov {n : ℕ} {μ : Measure Ω} {f : Ω → Matrix (Fin n) (Fin 1) ℝ} {σ_sq : ℝ}
    (h_cov : HasScalarCovariance μ f σ_sq) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (A * covMatrix μ f) = σ_sq * Matrix.trace A := by
  unfold HasScalarCovariance at h_cov
  rw [h_cov]
  -- Expand matrix multiplication with scalar
  rw [Matrix.mul_smul, Matrix.mul_one]
  -- Prove trace(σ_sq • A) = σ_sq * trace(A)
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
