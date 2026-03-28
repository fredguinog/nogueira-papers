/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# Trace–Norm Identity

This file proves that the squared norm of a matrix-vector product can be
expressed as a trace: `‖Mv‖² = tr(MᵀM · vvᵀ)`.

## Main results

* `Matrix.sqNorm_mul_eq_trace` : the trace–norm identity.
-/

namespace Matrix

/-- The squared norm of a matrix-vector product can be expressed
as a trace: `‖Mv‖² = tr(MᵀM · vvᵀ)`. -/
lemma sqNorm_mul_eq_trace {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (v : Matrix (Fin m) (Fin 1) ℝ) :
    ((M * v)ᵀ * (M * v)) 0 0 = Matrix.trace (Mᵀ * M * (v * vᵀ)) := by
  -- Convert the 1x1 scalar entry into a matrix trace
  have h1 : ((M * v)ᵀ * (M * v)) 0 0 = Matrix.trace ((M * v)ᵀ * (M * v)) := by
    dsimp [Matrix.trace, Matrix.diag]
    rw [Fin.sum_univ_one]
  rw [h1]
  -- Expand the transpose of the product
  rw [Matrix.transpose_mul]
  -- Reassociate: vᵀ * Mᵀ * M * v = vᵀ * (Mᵀ * M * v)
  have h2 : vᵀ * Mᵀ * (M * v) = vᵀ * (Mᵀ * M * v) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h2]
  -- Apply trace cyclicity: trace(A * B) = trace(B * A)
  -- Here A = vᵀ and B = (Mᵀ * M * v)
  rw [Matrix.trace_mul_comm]
  -- Reassociate back: (Mᵀ * M * v) * vᵀ = Mᵀ * M * (v * vᵀ)
  rw [Matrix.mul_assoc]

end Matrix
