/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# Instances for Matrix Types

This file provides `NormedAddCommGroup`, `NormedSpace`, and
`MeasurableSpace` instances for `Matrix m n ℝ` via the underlying
Pi type `m → n → ℝ`. These are needed for Bochner integration,
covariance matrices, and measure-theoretic arguments involving
matrix-valued random variables.

## Implementation notes

`Matrix m n α` is defined as `m → n → α` (a `def`, not `abbrev`),
so Lean's instance search cannot see through it automatically.
We provide the instances explicitly by showing they are inherited
from the Pi type.
-/

namespace Matrix

/-- `NormedAddCommGroup` instance for `Matrix` via the Pi type. -/
instance instNormedAddCommGroup {m n : Type*}
    [Fintype m] [Fintype n] :
    NormedAddCommGroup (Matrix m n ℝ) :=
  show NormedAddCommGroup (m → n → ℝ) by
    infer_instance

/-- `NormedSpace ℝ` instance for `Matrix` via the Pi type. -/
noncomputable instance instNormedSpace
    {m n : Type*} [Fintype m] [Fintype n] :
    NormedSpace ℝ (Matrix m n ℝ) :=
  show NormedSpace ℝ (m → n → ℝ) by infer_instance

/-- `MeasurableSpace` instance for `Matrix` via the Pi type. -/
instance instMeasurableSpace {m n : Type*}
    [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℝ) :=
  show MeasurableSpace (m → n → ℝ) by infer_instance

end Matrix
