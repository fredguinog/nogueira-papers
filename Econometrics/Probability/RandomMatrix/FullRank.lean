/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.MeasureTheory.PolynomialZeroSet

/-!
# Almost Sure Invertibility of Random Matrices

This file proves that a random matrix whose distribution is absolutely continuous
with respect to Lebesgue measure is invertible almost surely, by showing that the
determinant—a nonzero polynomial—vanishes on a measure-zero set.

## Main definitions

* `ProbabilityTheory.matrixFinProdEquiv` : flattening `Fin n × Fin n ≃ Fin (n*n)`.
* `ProbabilityTheory.detMvPoly` : the determinant as a multivariate polynomial.

## Main results

* `randomMatrix_invertible_ae` : `μ {ω | det(A ω) = 0} = 0`.
-/

open MeasureTheory Set MvPolynomial Matrix

namespace ProbabilityTheory

variable {n : ℕ}

/-! ### 1. Equivalence mapping matrix indices to a flat 1D array. -/
/-- Equivalence mapping matrix indices to a flat 1D array. -/
noncomputable def matrixFinProdEquiv (n : ℕ) : Fin n × Fin n ≃ Fin (n * n) :=
  (Fintype.equivFin (Fin n × Fin n)).trans (Equiv.cast (by simp))

/-! ### 2. Define the determinant as an MvPolynomial over Fin (n * n) -/
/-- The determinant as a multivariate polynomial over `Fin (n * n)`. -/
noncomputable def detMvPoly (n : ℕ) : MvPolynomial (Fin (n * n)) ℝ :=
  ∑ σ : Equiv.Perm (Fin n), (σ.sign : ℝ) • ∏ i : Fin n, X (matrixFinProdEquiv n (σ i, i))

/-! ### 3. Prove it evaluates exactly to the matrix determinant -/
lemma eval_detMvPoly (M : Matrix (Fin n) (Fin n) ℝ) :
    eval (fun k => M ((matrixFinProdEquiv n).symm k).1 ((matrixFinProdEquiv n).symm k).2)
        (detMvPoly n) = M.det := by
  unfold detMvPoly
  rw [map_sum, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [smul_eval, map_prod, eval_X, Equiv.symm_apply_apply]
  rw [Units.smul_def, zsmul_eq_mul]

/-! ### 4. Prove it is not the zero polynomial (by evaluating at the identity matrix) -/
lemma detMvPoly_ne_zero (n : ℕ) : detMvPoly n ≠ 0 := by
  intro h
  have h_eval : eval (fun k => (1 : Matrix (Fin n) (Fin n) ℝ) ((matrixFinProdEquiv n).symm k).1
      ((matrixFinProdEquiv n).symm k).2) (detMvPoly n) = 0 := by
    rw [h, map_zero]
  rw [eval_detMvPoly] at h_eval
  have h_det_one : (1 : Matrix (Fin n) (Fin n) ℝ).det = 1 := Matrix.det_one
  rw [h_det_one] at h_eval
  exact one_ne_zero h_eval

/-! ### 5. Flattening function to map a Matrix to a 1D vector for measure evaluation -/
/-- Flattening function: maps a matrix to a 1D vector. -/
noncomputable def matToVec (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) : Fin (n * n) → ℝ :=
  fun k => M ((matrixFinProdEquiv n).symm k).1 ((matrixFinProdEquiv n).symm k).2

/-- `MeasurableSpace` instance for `Matrix` via the underlying Pi type. -/
noncomputable instance Matrix.instMeasurableSpaceReal :
    MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) := MeasurableSpace.pi

/--
The core Random Matrix Theorem for Phase 2.2:
A random matrix distributed absolutely continuously with respect to Lebesgue measure
is invertible (full rank) almost surely.
-/
theorem randomMatrix_invertible_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA_meas : Measurable A)
    (h_abs_cont : Measure.map (fun ω => matToVec n (A ω)) μ ≪ volume) :
    μ {ω : Ω | (A ω).det = 0} = 0 := by
  let Z := {v : Fin (n * n) → ℝ | eval v (detMvPoly n) = 0}
  have hZ_vol : volume Z = 0 :=
    MeasureTheory.volume_mvPolynomial_roots (n * n) (detMvPoly n) (detMvPoly_ne_zero n)
  have hZ_meas : MeasurableSet Z := MeasureTheory.measurableSet_mvPolynomial_roots (detMvPoly n)
  have h_map_zero : (Measure.map (fun ω => matToVec n (A ω)) μ) Z = 0 :=
    h_abs_cont hZ_vol
  have h_set_eq : {ω : Ω | (A ω).det = 0} = (fun ω => matToVec n (A ω)) ⁻¹' Z := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [← eval_detMvPoly (A ω)]
    rfl
  have h_flat_meas : Measurable (fun ω => matToVec n (A ω)) := by
    apply measurable_pi_lambda; intro k
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hA_meas)
  rw [h_set_eq, ← Measure.map_apply h_flat_meas hZ_meas]
  exact h_map_zero

end ProbabilityTheory
