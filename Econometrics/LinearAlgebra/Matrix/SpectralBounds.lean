/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.LinearAlgebra.Matrix.MoorePenrose
import Econometrics.LinearAlgebra.Matrix.Norms
import Econometrics.LinearAlgebra.Matrix.AnnihilatorTrace

/-!
# Spectral Bounds and Projector Estimates

This file combines the matrix norm bounds with eigenvalue lower bounds to
derive the master geometric lemma bounding the squared norm of a projected
vector by spectral and norm data.

## Main results

* `Matrix.inner_sq_le_sqNorm_mul` : Cauchy–Schwarz for `sqNorm`.
* `Matrix.qform_inv_le` : quadratic form bound through the inverse.
* `Matrix.proj_sqNorm_le` : the master projector bound.
-/

namespace Matrix
variable {T r : ℕ} [NeZero T]

/-- Algebraic squeeze: `Y² ≤ Y·Z` implies `Y ≤ Z`. -/
lemma le_of_mul_sq_le_mul {Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (h : Y * Y ≤ Y * Z) : Y ≤ Z := by
  by_cases hY0 : Y = 0
  · rw [hY0]; exact hZ
  · have hY_pos : 0 < Y := lt_of_le_of_ne hY (Ne.symm hY0)
    exact le_of_mul_le_mul_left h hY_pos

/-! ### 2. Bound a quadratic form by the minimum eigenvalue of the original matrix -/
omit [NeZero T] in
lemma qform_inv_le (X : Matrix (Fin T) (Fin r) ℝ) (w : Matrix (Fin r) (Fin 1) ℝ)
    (lambda_min : ℝ) (h_pos : 0 < lambda_min)
    (h_inv : IsUnit (Xᵀ * X).det)
    (h_eigen : ∀ u : Matrix (Fin r) (Fin 1) ℝ, lambda_min * sqNorm u ≤ (uᵀ * (Xᵀ * X) * u) 0 0) :
    (wᵀ * (Xᵀ * X)⁻¹ * w) 0 0 ≤ (1 / lambda_min) * sqNorm w := by
  let A := Xᵀ * X
  let u := A⁻¹ * w
  have hA_inv : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ h_inv
  have h_Au : A * u = w := by
    calc A * u = A * (A⁻¹ * w) := rfl
      _ = (A * A⁻¹) * w := by rw [← Matrix.mul_assoc]
      _ = (1 : Matrix (Fin r) (Fin r) ℝ) * w := by rw [hA_inv]
      _ = w := by rw [Matrix.one_mul]
  have h_symm : Aᵀ = A := by
    dsimp [A]; rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have h_w_u : (wᵀ * u) 0 0 = (uᵀ * A * u) 0 0 := by
    calc (wᵀ * u) 0 0 = ((A * u)ᵀ * u) 0 0 := by rw [← h_Au]
      _ = (uᵀ * Aᵀ * u) 0 0 := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (uᵀ * A * u) 0 0 := by rw [h_symm]
  have h_u_w : (uᵀ * w) 0 0 = (uᵀ * A * u) 0 0 := by
    calc (uᵀ * w) 0 0 = (uᵀ * (A * u)) 0 0 := by rw [← h_Au]
      _ = (uᵀ * A * u) 0 0 := by rw [← Matrix.mul_assoc]
  have h_target : (wᵀ * A⁻¹ * w) 0 0 = (uᵀ * w) 0 0 := by
    calc (wᵀ * A⁻¹ * w) 0 0 = (wᵀ * (A⁻¹ * w)) 0 0 := by rw [Matrix.mul_assoc]
      _ = (wᵀ * u) 0 0 := rfl
      _ = (uᵀ * w) 0 0 := by rw [h_w_u, h_u_w]
  have h_eigen_u := h_eigen u
  rw [← h_u_w] at h_eigen_u
  have h_cs := inner_sq_le_sqNorm_mul u w
  have h_Nu_nonneg := sqNorm_nonneg u
  have h_Nw_nonneg := sqNorm_nonneg w
  let I := (uᵀ * w) 0 0
  let Nu := sqNorm u
  let Nw := sqNorm w
  have h1 : lambda_min * Nu ≤ I := h_eigen_u
  have hI_nonneg : 0 ≤ I := by
    calc 0 ≤ lambda_min * Nu := mul_nonneg h_pos.le h_Nu_nonneg
      _ ≤ I := h1
  have h_Y : (lambda_min * I) * (lambda_min * I) ≤ (lambda_min * I) * Nw := by
    calc (lambda_min * I) * (lambda_min * I) = lambda_min^2 * I^2 := by ring
      _ ≤ lambda_min^2 * (Nu * Nw) := mul_le_mul_of_nonneg_left h_cs (sq_nonneg lambda_min)
      _ = lambda_min * (lambda_min * Nu) * Nw := by ring
      _ ≤ lambda_min * I * Nw := by
          apply mul_le_mul_of_nonneg_right _ h_Nw_nonneg
          exact mul_le_mul_of_nonneg_left h1 h_pos.le
  have hY_nonneg : 0 ≤ lambda_min * I := mul_nonneg h_pos.le hI_nonneg
  have h_Y_le_Z := le_of_mul_sq_le_mul hY_nonneg h_Nw_nonneg h_Y
  have h_final : I ≤ (1 / lambda_min) * Nw := by
    calc I = (lambda_min * I) / lambda_min := by rw [mul_div_cancel_left₀ I h_pos.ne']
      _ ≤ Nw / lambda_min := div_le_div_of_nonneg_right h_Y_le_Z h_pos.le
      _ = (1 / lambda_min) * Nw := by ring
  rw [h_target]
  exact h_final

/-! ### 3. The Master Geometric Lemma combining Norms and SpectralBounds -/
lemma proj_sqNorm_le (X : Matrix (Fin T) (Fin r) ℝ) (v : Matrix (Fin T) (Fin 1) ℝ)
    (C_X : ℝ) (hX : ∀ i j, |X i j| ≤ C_X)
    (lambda_min : ℝ) (h_pos : 0 < lambda_min)
    (h_inv : IsUnit (Xᵀ * X).det)
    (h_eigen : ∀ u : Matrix (Fin r) (Fin 1) ℝ, lambda_min * sqNorm u ≤ (uᵀ * (Xᵀ * X) * u) 0 0)
    (h_pinv_eq_inv : (Xᵀ * X).pinv = (Xᵀ * X)⁻¹) :
    sqNorm (proj X * v) ≤ (r : ℝ) * (T : ℝ)^2 * C_X^2 * (normInfty v)^2 / lambda_min := by
  unfold proj
  rw [h_pinv_eq_inv]
  have h_assoc_v : X * (Xᵀ * X)⁻¹ * Xᵀ * v = X * ((Xᵀ * X)⁻¹ * (Xᵀ * v)) := by
    simp only [Matrix.mul_assoc]
  rw [h_assoc_v]
  have h_symm : (Xᵀ * X)ᵀ = Xᵀ * X := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have h_inv_symm : ((Xᵀ * X)⁻¹)ᵀ = (Xᵀ * X)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, h_symm]
  have h_expand : (X * ((Xᵀ * X)⁻¹ * (Xᵀ * v)))ᵀ = (Xᵀ * v)ᵀ * (Xᵀ * X)⁻¹ * Xᵀ := by
    calc (X * ((Xᵀ * X)⁻¹ * (Xᵀ * v)))ᵀ
      _ = ((Xᵀ * X)⁻¹ * (Xᵀ * v))ᵀ * Xᵀ := by rw [Matrix.transpose_mul]
      _ = (Xᵀ * v)ᵀ * ((Xᵀ * X)⁻¹)ᵀ * Xᵀ := by rw [Matrix.transpose_mul]
      _ = (Xᵀ * v)ᵀ * (Xᵀ * X)⁻¹ * Xᵀ := by rw [h_inv_symm]
  have h_sq_norm_eq : sqNorm (X * ((Xᵀ * X)⁻¹ * (Xᵀ * v))) =
      ((Xᵀ * v)ᵀ * (Xᵀ * X)⁻¹ * (Xᵀ * v)) 0 0 := by
    unfold sqNorm
    rw [h_expand]
    let A := (Xᵀ * v)ᵀ * (Xᵀ * X)⁻¹
    let B := (Xᵀ * X)⁻¹ * (Xᵀ * v)
    have h_cancel : (A * Xᵀ) * (X * B) = ((Xᵀ * v)ᵀ * (Xᵀ * X)⁻¹ * (Xᵀ * v)) := by
      calc (A * Xᵀ) * (X * B)
        _ = A * (Xᵀ * (X * B)) := by rw [Matrix.mul_assoc]
        _ = A * ((Xᵀ * X) * B) := by rw [← Matrix.mul_assoc Xᵀ X B]
        _ = (A * (Xᵀ * X)) * B := by rw [← Matrix.mul_assoc A (Xᵀ * X) B]
        _ = ((Xᵀ * v)ᵀ * ((Xᵀ * X)⁻¹ * (Xᵀ * X))) * B := by
            have h_A_assoc : A * (Xᵀ * X) = (Xᵀ * v)ᵀ * ((Xᵀ * X)⁻¹ * (Xᵀ * X)) := by
              dsimp [A]
              rw [Matrix.mul_assoc]
            rw [h_A_assoc]
        _ = ((Xᵀ * v)ᵀ * (1 : Matrix (Fin r) (Fin r) ℝ)) * B :=
            by rw [Matrix.nonsing_inv_mul _ h_inv]
        _ = (Xᵀ * v)ᵀ * B := by rw [Matrix.mul_one]
        _ = (Xᵀ * v)ᵀ * ((Xᵀ * X)⁻¹ * (Xᵀ * v)) := rfl
        _ = (Xᵀ * v)ᵀ * (Xᵀ * X)⁻¹ * (Xᵀ * v) := by rw [← Matrix.mul_assoc]
    exact congrArg (fun M => M 0 0) h_cancel
  rw [h_sq_norm_eq]
  have h_qform := qform_inv_le X (Xᵀ * v) lambda_min h_pos h_inv h_eigen
  have h_vec_bound := mulVec_sqNorm_le X v C_X hX
  calc ((Xᵀ * v)ᵀ * (Xᵀ * X)⁻¹ * (Xᵀ * v)) 0 0
    _ ≤ (1 / lambda_min) * sqNorm (Xᵀ * v) := h_qform
    _ ≤ (1 / lambda_min) * ((r : ℝ) * (T : ℝ)^2 * C_X^2 * (normInfty v)^2) :=
        mul_le_mul_of_nonneg_left h_vec_bound (one_div_pos.mpr h_pos).le
    _ = (r : ℝ) * (T : ℝ)^2 * C_X^2 * (normInfty v)^2 / lambda_min := by ring

end Matrix
