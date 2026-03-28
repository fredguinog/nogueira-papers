/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.LinearAlgebra.Matrix.MoorePenrose
import Econometrics.LinearAlgebra.Matrix.Norms

/-!
# Annihilator Projections and Trace Identities

This file defines the orthogonal projector and annihilator (residual maker)
associated with a matrix, and proves their algebraic properties and trace
identities.

## Main definitions

* `Matrix.proj` : the projection matrix `A(AᵀA)⁺Aᵀ`.
* `Matrix.annihilator` : the annihilator `I − proj(A)`.

## Main results

* `Matrix.proj_mul_self` / `Matrix.annihilator_mul_self` : idempotency.
* `Matrix.trace_proj_eq_rank` : `tr(proj A) = rank A`.
* `Matrix.trace_annihilator_eq_codim` : `tr(M_A) = n − rank A`.
-/

namespace Matrix

variable {n m : ℕ}

/-- The projection matrix `A(AᵀA)⁺Aᵀ`. -/
noncomputable def proj (A : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  A * (Aᵀ * A).pinv * Aᵀ

/-- The annihilator (residual maker) `I − proj(A)`. -/
noncomputable def annihilator (A : Matrix (Fin n) (Fin m) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ) - proj A

@[simp]
lemma proj_transpose {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : (proj A)ᵀ = proj A := by
  unfold proj
  have h_inner_symm : (Aᵀ * A)ᵀ = Aᵀ * A :=
      by simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have h_inv_symm : ((Aᵀ * A).pinv)ᵀ = (Aᵀ * A).pinv := by rw [Matrix.pinv_transpose, h_inner_symm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, h_inv_symm, Matrix.mul_assoc]

@[simp]
lemma proj_mul_self {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    proj A * proj A = proj A := by
  unfold proj
  have h_core := Matrix.mul_pinv_mul_transpose_mul_self A
  calc A * (Aᵀ * A).pinv * Aᵀ * (A * (Aᵀ * A).pinv * Aᵀ)
    _ = (A * (Aᵀ * A).pinv * (Aᵀ * A)) * (Aᵀ * A).pinv * Aᵀ := by simp only [Matrix.mul_assoc]
    _ = A * (Aᵀ * A).pinv * Aᵀ := by rw [h_core]

@[simp]
lemma annihilator_transpose {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : (annihilator A)ᵀ =
    annihilator A := by
  unfold annihilator; simp only [Matrix.transpose_sub, Matrix.transpose_one, proj_transpose]

@[simp]
lemma annihilator_mul_self {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    annihilator A * annihilator A = annihilator A := by
  unfold annihilator
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, proj_mul_self A, sub_self,
      sub_zero]

@[simp]
lemma annihilator_mul_proj {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    annihilator A * proj A = 0 := by
  unfold annihilator; rw [Matrix.sub_mul, Matrix.one_mul, proj_mul_self A, sub_self]

lemma sqNorm_annihilator {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (v : Matrix (Fin n) (Fin 1) ℝ) :
    sqNorm (annihilator A * v) = sqNorm v - sqNorm (proj A * v) := by
  unfold sqNorm
  have h_symm := annihilator_transpose A
  have h_idemp := annihilator_mul_self A
  have h_proj_transpose := proj_transpose A
  have h_proj_mul_self := proj_mul_self A
  have eq1 : ((annihilator A * v)ᵀ * (annihilator A * v)) = vᵀ * (annihilator A * v) := by
    rw [Matrix.transpose_mul, h_symm, Matrix.mul_assoc,
        ← Matrix.mul_assoc (annihilator A) (annihilator A) v, h_idemp]
  have eq2 : ((proj A * v)ᵀ * (proj A * v)) = vᵀ * (proj A * v) := by
    rw [Matrix.transpose_mul, h_proj_transpose, Matrix.mul_assoc,
        ← Matrix.mul_assoc (proj A) (proj A) v, h_proj_mul_self]
  have eq3 : vᵀ * (annihilator A * v) = vᵀ * v - vᵀ * (proj A * v) := by
    unfold annihilator; rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
  rw [eq1, eq2, eq3]; rfl

lemma trace_one_fin : Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) = (n : ℝ) := by
  -- Use simp to evaluate the diagonal of the identity matrix
  have h : Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) = ∑ i : Fin n, (1 : ℝ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.one_apply_eq]
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/--
This is the core linear algebra fact: the trace of an orthogonal projector equals its rank.
Proved rigorously using the complete Moore-Penrose API.
-/
lemma trace_proj_eq_rank (A : Matrix (Fin n) (Fin m) ℝ) :
    Matrix.trace (proj A) = (Matrix.rank A : ℝ) := by
  unfold proj
  exact Matrix.trace_mul_pinv_mul_transpose_eq_rank A

/-- Goal: Matrix.trace (annihilator A) = n - Matrix.rank A -/
lemma trace_annihilator_eq_codim (A : Matrix (Fin n) (Fin m) ℝ) :
    Matrix.trace (annihilator A) = (n : ℝ) - (Matrix.rank A : ℝ) := by
  unfold annihilator
  rw [Matrix.trace_sub, trace_one_fin, trace_proj_eq_rank A]

end Matrix
