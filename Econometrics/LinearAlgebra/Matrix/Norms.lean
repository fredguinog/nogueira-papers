/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# Matrix and Vector Norms

This file defines the squared L² norm and L∞ norm for column-vector matrices
and provides bounds relating inner products to these norms.

## Main definitions

* `Matrix.sqNorm` : squared Euclidean norm `vᵀ v`.
* `Matrix.normInfty` : L∞ norm `max_i |v_i|`.

## Main results

* `Matrix.inner_sq_le_sqNorm_mul` : Cauchy–Schwarz for `sqNorm`.
* `Matrix.sqNorm_nonneg` : `sqNorm` is non-negative.
* `Matrix.mulVec_sqNorm_le` : bound on `‖Xᵀ v‖²` in terms of entrywise
  bounds.
-/

namespace Matrix

/-! ### Squared norm and generic lemmas -/

/-- The squared Euclidean norm of a column vector: `vᵀ v`. -/
def sqNorm {n : ℕ} (v : Matrix (Fin n) (Fin 1) ℝ) : ℝ := (vᵀ * v) 0 0

-- ──────────────────────────────────────────────────────────────────────────
-- Auxiliary: ‖v‖² = v'v ≥ 0 and the Cauchy–Schwarz inequality in matrix form.
-- These are the basic inner-product-space tools used throughout the expansion.
-- ──────────────────────────────────────────────────────────────────────────

lemma inner_eq_sum {T : ℕ} (v w : Matrix (Fin T) (Fin 1) ℝ) :
  (vᵀ * w) 0 0 = ∑ t : Fin T, v t 0 * w t 0 := by
  simp only[Matrix.mul_apply, Matrix.transpose_apply]

lemma sqNorm_eq_sum_sq {n : ℕ}
    (u : Matrix (Fin n) (Fin 1) ℝ) :
    sqNorm u = ∑ i : Fin n, (u i 0) ^ 2 := by
  unfold sqNorm
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  congr 1; ext i; ring

/-- `sqNorm` is non-negative. -/
lemma sqNorm_nonneg {n : ℕ}
    (v : Matrix (Fin n) (Fin 1) ℝ) : 0 ≤ sqNorm v := by
  unfold sqNorm
  have inner_eq_sum : (vᵀ * v) 0 0 =
      ∑ t : Fin n, v t 0 * v t 0 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [inner_eq_sum]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg (v i 0)

/-- Cauchy–Schwarz inequality for `sqNorm`. -/
lemma inner_sq_le_sqNorm_mul {n : ℕ}
    (v w : Matrix (Fin n) (Fin 1) ℝ) :
    ((vᵀ * w) 0 0) ^ 2 ≤ sqNorm v * sqNorm w := by
  have inner_eq_sum :
      ∀ (x y : Matrix (Fin n) (Fin 1) ℝ),
        (xᵀ * y) 0 0 = ∑ t : Fin n, x t 0 * y t 0 := by
    intro x y
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
  unfold sqNorm
  rw [inner_eq_sum v w, inner_eq_sum v v, inner_eq_sum w w]
  have key := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => v i 0) (fun i => w i 0)
  have hf : (∑ i : Fin n, (v i 0) ^ 2) =
      ∑ i : Fin n, v i 0 * v i 0 := by
    congr 1; ext i; ring
  have hg : (∑ i : Fin n, (w i 0) ^ 2) =
      ∑ i : Fin n, w i 0 * w i 0 := by
    congr 1; ext i; ring
  rw [hf, hg] at key; exact key

/-! ### L∞ norm and entrywise bounds -/

section BoundedNorms

variable {T r : ℕ} [NeZero T]

/-- The L∞ norm of a column vector: `max_i |v_i|`. -/
def normInfty (v : Matrix (Fin T) (Fin 1) ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty
    (fun i => |v i 0|)

lemma le_normInfty (v : Matrix (Fin T) (Fin 1) ℝ)
    (t : Fin T) : |v t 0| ≤ normInfty v := by
  unfold normInfty
  exact Finset.le_sup' (fun i => |v i 0|) (Finset.mem_univ t)

/-- Bound on `‖Xᵀ v‖²` in terms of entrywise bounds on `X`. -/
lemma mulVec_sqNorm_le
    (X : Matrix (Fin T) (Fin r) ℝ)
    (v : Matrix (Fin T) (Fin 1) ℝ)
    (C_X : ℝ) (hX : ∀ i j, |X i j| ≤ C_X) :
    sqNorm (Xᵀ * v) ≤
      (r : ℝ) * (T : ℝ) ^ 2 * C_X ^ 2 *
        (normInfty v) ^ 2 := by
  rw [sqNorm_eq_sum_sq]
  have h_elem_bound :
      ∀ k : Fin r,
        ((Xᵀ * v) k 0) ^ 2 ≤
          ((T : ℝ) * C_X * normInfty v) ^ 2 := by
    intro k
    have h_expand : (Xᵀ * v) k 0 =
        ∑ t : Fin T, X t k * v t 0 := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [h_expand]
    have h_abs_le :
        |∑ t : Fin T, X t k * v t 0| ≤
          (T : ℝ) * C_X * normInfty v := by
      calc |∑ t : Fin T, X t k * v t 0|
        _ ≤ ∑ t : Fin T, |X t k * v t 0| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ t : Fin T, |X t k| * |v t 0| := by
            simp_rw [abs_mul]
        _ ≤ ∑ t : Fin T, C_X * normInfty v := by
            apply Finset.sum_le_sum
            intro t _
            apply mul_le_mul
            · exact hX t k
            · exact le_normInfty v t
            · exact abs_nonneg _
            · exact le_trans (abs_nonneg _) (hX t k)
        _ = (Finset.univ.card : ℝ) *
              (C_X * normInfty v) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (T : ℝ) * C_X * normInfty v := by
            rw [Finset.card_univ, Fintype.card_fin]
            ring
    have h_le_and_ge := abs_le.mp h_abs_le
    nlinarith
  calc ∑ k : Fin r, ((Xᵀ * v) k 0) ^ 2
    _ ≤ ∑ k : Fin r,
          ((T : ℝ) * C_X * normInfty v) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        exact h_elem_bound k
    _ = (r : ℝ) *
          ((T : ℝ) * C_X * normInfty v) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
    _ = (r : ℝ) * (T : ℝ) ^ 2 * C_X ^ 2 *
          (normInfty v) ^ 2 := by ring

end BoundedNorms

end Matrix
