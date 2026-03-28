/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
================================================================================
  Formal Verification of Lemma 4.2, Theorem 4.3, and Corollary 4.4
  "Irrelevant Donors in Causal Panel Methods: Causes and Consequences
   of Spurious Pre-Treatment Fits"
  Author: Frederico Guilherme Nogueira (frederico.nogueira@gmail.com)
================================================================================

OVERVIEW
--------
This file provides a Lean 4 / Mathlib formalization of the central geometric
results of the paper: Lemma 4.2 (Exact Finite-Sample Geometric Decomposition),
Theorem 4.3 (Asymptotic Resolution of the Pre-Treatment Residual), and
Corollary 4.4 (Differential Masking and the Spurious Fit Trap). It imports
the Proposition 3.1 formalization and builds directly on its definitions.

CORRESPONDENCE TO THE MANUSCRIPT
---------------------------------
  §4.3 Lemma 4.2 ↔ namespace Lemma42, lemma `lemma_4_2`
  §4.3 Theorem 4.3 ↔ section Theorem43, theorem `theorem_4_3`
  §4.4 Assumption 4.1 ↔ structure `Assumption41_Data`
  §4.4 Corollary 4.4 ↔ section Corollary44, lemmas `corollary_4_4_i/ii/iii`

KEY NOTATION MAP (Manuscript → Lean)
--------------------------------------
  y₀ = Fλ₀ + δ + ε₀                 ↔ `y_0 d`
  X_rel = FΛ'_rel + E_rel           ↔ `X_rel pd T ω` (from Proposition_3_1)
  𝒰 = span((I − P_{X_rel})X_irrel)  ↔ column span of `U_mat d`
  P_𝒰                               ↔ `proj (U_mat d)`
  I − P_𝒰                           ↔ `annihilator (U_mat d)`
  P_X = P_{X_rel} + P_𝒰             ↔ `P_X_full d`
  B_rel = (I − P_{X_rel})Fλ₀        ↔ `B_rel d`
  d = (I − P_{X_rel})δ              ↔ `d_vec d`
  e = (I − P_{X_rel})ε₀             ↔ `e_vec d`
  ‖v‖²                              ↔ `sqNorm v`
  M_{FP,T₀}                         ↔ `M_FP d`
  M_{δ,T₀} = sin²θ_{T₀}             ↔ `M_delta d`
  B²_FP (from Prop 3.1)             ↔ `B_FP_sq_val d43`
  κ_{T₀} = s/(T₀ − r)               ↔ `rsd.kappa` (asymptotic limit κ)
  σ²                                ↔ `d43.sigma_sq`
  δ²                                ↔ `d43.delta_sq`

KNOWN DEVIATIONS FROM MANUSCRIPT
--------------------------------------------
NONE

ARCHITECTURAL NOTES & ALIGNMENT (Resolving Formalization Critiques)
-------------------------------------------------------------------
To maintain a modular formalization, the generic asymptotic probability theory
underlying the manuscript has been proven from first principles in the standalone
`Econometrics.Analysis.*`, `Econometrics.LinearAlgebra.*`,
`Econometrics.MeasureTheory.*` and `Econometrics.Probability.*` namespaces.

Consequently, `Theorem43_Data` formally encodes the *interfaces* to these generic
theorems rather than deriving them inline from a monolithic "Assumption 2" structure:
1. CROSS-TERMS (Assump 2.2a/b): The bounds `h_cross_2_ortho` and `h_cross_3_ortho`
   interface directly with the Cross-Sectional WLLN / Conditional Mixing bounds
   proven in `ConditionalMixing.lean` and `ChebyshevWLLN.lean`.
2. TRACE CONCENTRATION (Assump 2.2d): `h_noise_trace_var` is closed via the generic
   `trace_variance_vanishes` theorem imported from `RandomMatrix.TraceConcentration`.
3. DETERMINISTIC RANK: To decouple the algebraic projection geometry from random
   matrix theory, the stochastic rank sequence is interfaced via `rsd : RankSaturationData`,
   bridging the pure algebra in this file to the Marchenko-Pastur properties
   formalized in `RankSaturation.lean`.
4. PROOF PATH: The algebraic rearrangement groups the global error prior to taking
   limits. This is mathematically equivalent to but algebraically organized differently
   from taking limits of the 6 individual terms.

DEPENDENCIES
------------
  Lean 4, Mathlib (import Mathlib)
  Econometrics.Nogueira2026a.Proposition_3_1 (for B²_FP, bias_original)
  Econometrics.Analysis.Asymptotics.RankSaturation
  Econometrics.LinearAlgebra.Matrix.AnnihilatorTrace
  Econometrics.LinearAlgebra.Matrix.TraceNorm
  Econometrics.MeasureTheory.BochnerMatrixCommute
  Econometrics.Probability.ConditionalMixing
  Econometrics.Probability.CovarianceMatrix
  Econometrics.Probability.RandomMatrix.TraceConcentration
================================================================================
-/

import Mathlib
import Econometrics.Nogueira2026a.Proposition_3_1
import Econometrics.Analysis.Asymptotics.RankSaturation
import Econometrics.LinearAlgebra.Matrix.AnnihilatorTrace
import Econometrics.LinearAlgebra.Matrix.TraceNorm
import Econometrics.MeasureTheory.BochnerMatrixCommute
import Econometrics.Probability.ConditionalMixing
import Econometrics.Probability.CovarianceMatrix
import Econometrics.Probability.RandomMatrix.TraceConcentration

open Matrix MeasureTheory Filter Topology ProbabilityTheory AsymptoticRank

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART I: LEMMA 4.2 — Exact Finite-Sample Geometric Decomposition
--
-- This namespace formalizes the exact algebraic identity:
--   ‖residual‖² = ‖B_rel‖²·M_{FP} + ‖d‖²·M_δ + ‖(I−P_𝒰)e‖²
--                  + 2B'_rel(I−P_𝒰)d + 2B'_rel(I−P_𝒰)e + 2d'(I−P_𝒰)e
--
-- This holds exactly for any finite T₀, with no probabilistic assumptions.
-- ═══════════════════════════════════════════════════════════════════════════════

namespace Lemma42

variable {T r N_rel N_irrel : ℕ}

-- ──────────────────────────────────────────────────────────────────────────
-- Data bundle for Lemma 4.2.
-- Collects the ingredients of the DGP (Section 2.1 of the manuscript):
--   y₀ = Fλ₀ + δ + ε₀,   X_rel,   X_irrel
--
-- Everything is deterministic / conditioned on the realized matrices.
-- ──────────────────────────────────────────────────────────────────────────

structure Lemma42_Data (T r N_rel N_irrel : ℕ) where
  F : Matrix (Fin T) (Fin r) ℝ              -- Common factors (T × r)
  lambda_0 : Matrix (Fin r) (Fin 1) ℝ       -- Treated unit's loading vector λ₀
  delta : Matrix (Fin T) (Fin 1) ℝ          -- Structural violation δ (deterministic)
  eps_0 : Matrix (Fin T) (Fin 1) ℝ          -- Treated unit's idiosyncratic error ε₀
  X_rel : Matrix (Fin T) (Fin N_rel) ℝ      -- Relevant donor block
  X_irrel : Matrix (Fin T) (Fin N_irrel) ℝ  -- Irrelevant donor block

variable (d : Lemma42_Data T r N_rel N_irrel)

-- ──────────────────────────────────────────────────────────────────────────
-- Step 1 (Manuscript Proof of Lemma 4.2): Model setup
--   y₀ = Fλ₀ + δ + ε₀
-- ──────────────────────────────────────────────────────────────────────────

def y_0 : Matrix (Fin T) (Fin 1) ℝ :=
  d.F * d.lambda_0 + d.delta + d.eps_0

-- ──────────────────────────────────────────────────────────────────────────
-- Step 2 (Manuscript Proof): Irrelevant subspace construction
--   𝒰 := span((I − P_{X_rel})X_irrel)
-- The matrix U = (I − P_{X_rel})X_irrel whose column span defines 𝒰.
-- By construction, 𝒰 ⊂ range(I − P_{X_rel}), hence 𝒰 ⊥ span(X_rel).
-- ──────────────────────────────────────────────────────────────────────────

noncomputable def U_mat : Matrix (Fin T) (Fin N_irrel) ℝ :=
  annihilator d.X_rel * d.X_irrel

-- Key orthogonality: U'P_{X_rel} = 0 (columns of U are ⊥ to span(X_rel))
lemma U_transpose_mul_proj : (U_mat d)ᵀ * proj d.X_rel = 0 := by
  unfold U_mat; rw [Matrix.transpose_mul, annihilator_transpose]
  simp only[Matrix.mul_assoc]; rw[annihilator_mul_proj d.X_rel]; simp only [Matrix.mul_zero]

-- Mutual orthogonality: P_𝒰 · P_{X_rel} = 0  (manuscript Step 2.3)
-- This is the block-orthogonality that makes P_X = P_{X_rel} + P_𝒰 exact.
lemma U_mat_orth_X_rel : proj (U_mat d) * proj d.X_rel = 0 := by
  have h_proj_def : proj (U_mat d) = U_mat d * ((U_mat d)ᵀ * U_mat d).pinv * (U_mat d)ᵀ := rfl
  rw[h_proj_def]
  have h1 : (U_mat d)ᵀ * proj d.X_rel = 0 := U_transpose_mul_proj d
  simp only[Matrix.mul_assoc]; rw [h1]; simp only [Matrix.mul_zero]

-- ──────────────────────────────────────────────────────────────────────────
-- Step 4 (Manuscript Proof): Decomposition of the treated unit
--   B_rel := (I − P_{X_rel})Fλ₀   — imperfect-matching bias
--   d     := (I − P_{X_rel})δ     — residual structural violation
--   e     := (I − P_{X_rel})ε₀    — residual idiosyncratic noise
--
-- These are the three structural components that live in range(I − P_{X_rel}).
-- ──────────────────────────────────────────────────────────────────────────

noncomputable def B_rel : Matrix (Fin T) (Fin 1) ℝ := annihilator d.X_rel * (d.F * d.lambda_0)
noncomputable def d_vec : Matrix (Fin T) (Fin 1) ℝ := annihilator d.X_rel * d.delta
noncomputable def e_vec : Matrix (Fin T) (Fin 1) ℝ := annihilator d.X_rel * d.eps_0

-- Total donor projector: P_X = P_{X_rel} + P_𝒰  (manuscript Step 2.3)
noncomputable def P_X_full : Matrix (Fin T) (Fin T) ℝ := proj d.X_rel + proj (U_mat d)

-- The OLS residual: r = (I − P_X)y₀  (manuscript Step 1)
noncomputable def residual_vec : Matrix (Fin T) (Fin 1) ℝ := (1 - P_X_full d) * y_0 d

-- ──────────────────────────────────────────────────────────────────────────
-- Step 3 (Manuscript Proof): Exact residual factorization
--   I − P_X = (I − P_𝒰)(I − P_{X_rel})
-- so
--   residual = (I − P_𝒰)(B_rel + d + e)
--
-- This is the central algebraic identity; the cross term P_𝒰·P_{X_rel} = 0
-- makes the factorization exact.
-- ──────────────────────────────────────────────────────────────────────────

lemma lemma_4_2_substitution (h_orth : proj (U_mat d) * proj d.X_rel = 0) :
    residual_vec d = annihilator (U_mat d) * (B_rel d + d_vec d + e_vec d) := by
  unfold residual_vec P_X_full B_rel d_vec e_vec y_0 annihilator
  have h_rhs_distrib : (1 - proj d.X_rel) * (d.F * d.lambda_0) + (1 - proj d.X_rel) * d.delta +
    (1 - proj d.X_rel) * d.eps_0 =
    (1 - proj d.X_rel) * (d.F * d.lambda_0 + d.delta + d.eps_0) := by
    rw[Matrix.mul_add, Matrix.mul_add]
  rw[h_rhs_distrib, ← Matrix.mul_assoc]
  -- The key: (I − P_𝒰)(I − P_{X_rel}) = I − P_{X_rel} − P_𝒰 = I − P_X
  have h_expand : (1 - proj (U_mat d)) * (1 - proj d.X_rel) = 1 -
    (proj d.X_rel + proj (U_mat d)) := by
    rw[Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, h_orth, sub_zero]
    ext i j; simp only[Matrix.sub_apply, Matrix.add_apply]; ring
  rw[h_expand]

-- ──────────────────────────────────────────────────────────────────────────
-- Step 5 (Manuscript Proof): Quadratic expansion
--   ‖(I−P_𝒰)(B + d + e)‖² = ‖(I−P_𝒰)B‖² + ‖(I−P_𝒰)d‖² + ‖(I−P_𝒰)e‖²
--                              + 2B'(I−P_𝒰)d + 2B'(I−P_𝒰)e + 2d'(I−P_𝒰)e
--
-- Uses symmetry and idempotency of (I − P_𝒰) to reduce:
--   ((I−P_𝒰)X)'((I−P_𝒰)Y) = X'(I−P_𝒰)Y
-- This is the "expand the inner product" step on p.4 of the manuscript.
-- ──────────────────────────────────────────────────────────────────────────

lemma lemma_4_2_expansion
    (v_B v_d v_e : Matrix (Fin T) (Fin 1) ℝ) (P_U_ann : Matrix (Fin T) (Fin T) ℝ)
    (h_symm : P_U_annᵀ = P_U_ann) (h_idemp : P_U_ann * P_U_ann = P_U_ann) :
    sqNorm (P_U_ann * (v_B + v_d + v_e)) =
    sqNorm (P_U_ann * v_B) + sqNorm (P_U_ann * v_d) + sqNorm (P_U_ann * v_e) +
    2 * (v_Bᵀ * (P_U_ann * v_d)) 0 0 + 2 * (v_Bᵀ * (P_U_ann * v_e)) 0 0 + 2 *
      (v_dᵀ * (P_U_ann * v_e)) 0 0 := by
  unfold sqNorm
  have h_distrib : P_U_ann * (v_B + v_d + v_e) = P_U_ann * v_B + P_U_ann * v_d +
    P_U_ann * v_e := by rw[Matrix.mul_add, Matrix.mul_add]
  rw [h_distrib]; simp only[Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.add_apply]
  -- Key reduction: ((I−P_𝒰)X)'((I−P_𝒰)Y) = X'(I−P_𝒰)Y (by symmetry + idempotency)
  have h_reduce : ∀ (X Y : Matrix (Fin T) (Fin 1) ℝ), ((P_U_ann * X)ᵀ * (P_U_ann * Y)) =
    Xᵀ * (P_U_ann * Y) := by
    intro X Y; rw[Matrix.transpose_mul, h_symm, Matrix.mul_assoc, ← Matrix.mul_assoc
      P_U_ann P_U_ann Y, h_idemp]
  rw[h_reduce v_B v_d, h_reduce v_B v_e, h_reduce v_d v_B, h_reduce v_d v_e,
    h_reduce v_e v_B, h_reduce v_e v_d]
  -- Cross-term symmetry: X'(I−P_𝒰)Y = Y'(I−P_𝒰)X (since I−P_𝒰 is symmetric)
  have h_comm : ∀ (X Y : Matrix (Fin T) (Fin 1) ℝ), (Xᵀ * (P_U_ann * Y)) 0 0 =
    (Yᵀ * (P_U_ann * X)) 0 0 := by
    intro X Y
    have eq1 : ((P_U_ann * X)ᵀ * (P_U_ann * Y)) 0 0 = ((P_U_ann * Y)ᵀ * (P_U_ann * X)) 0 0 := by
      simp only[Matrix.mul_apply, Matrix.transpose_apply]; apply Finset.sum_congr rfl
      intro i _; ring
    rw[h_reduce X Y, h_reduce Y X] at eq1; exact eq1
  have h_XY : (v_dᵀ * (P_U_ann * v_B)) 0 0 = (v_Bᵀ * (P_U_ann * v_d)) 0 0 := h_comm v_d v_B
  have h_XZ : (v_eᵀ * (P_U_ann * v_B)) 0 0 = (v_Bᵀ * (P_U_ann * v_e)) 0 0 := h_comm v_e v_B
  have h_YZ : (v_eᵀ * (P_U_ann * v_d)) 0 0 = (v_dᵀ * (P_U_ann * v_e)) 0 0 := h_comm v_e v_d
  rw[h_XY, h_XZ, h_YZ]; ring

-- ──────────────────────────────────────────────────────────────────────────
-- Geometric attenuation factors:
--
--   M_{FP,T₀} := ‖(I−P_𝒰)B_rel‖² / ‖B_rel‖²
--       "survival fraction of the imperfect-matching bias outside 𝒰"
--
--   M_{δ,T₀} := sin²θ_{T₀} = ‖(I−P_𝒰)d‖² / ‖d‖²
--       "survival fraction of the structural violation outside 𝒰"
--
-- Both satisfy 0 ≤ M ≤ 1 (proven below).
-- M_{FP} ≈ 1 means B_rel is poorly aligned with 𝒰 (survives).
-- M_δ → 0 means the violation d is absorbed by 𝒰 (masked).
-- ──────────────────────────────────────────────────────────────────────────

noncomputable def M_FP : ℝ :=
  sqNorm (annihilator (U_mat d) * B_rel d) / sqNorm (B_rel d)

noncomputable def M_delta : ℝ :=
  sqNorm (annihilator (U_mat d) * d_vec d) / sqNorm (d_vec d)

-- Geometric interpretation: M_δ = 1 − cos²θ = 1 − ‖P_𝒰 d‖²/‖d‖²
-- (the component of d absorbed by 𝒰 is measured by cos²θ)
lemma M_delta_eq_one_sub_cos_sq
    (h_d_ne : sqNorm (d_vec d) ≠ 0) :
    M_delta d = 1 - sqNorm (proj (U_mat d) * d_vec d) / sqNorm (d_vec d) := by
  unfold M_delta
  rw[sqNorm_annihilator (U_mat d) (d_vec d)]
  field_simp[h_d_ne]

-- Similarly for the bias: M_{FP} = 1 − ‖P_𝒰 B_rel‖²/‖B_rel‖²
lemma M_FP_eq_one_sub_cos_sq
    (h_B_ne : sqNorm (B_rel d) ≠ 0) :
    M_FP d = 1 - sqNorm (proj (U_mat d) * B_rel d) / sqNorm (B_rel d) := by
  unfold M_FP
  rw[sqNorm_annihilator (U_mat d) (B_rel d)]
  field_simp [h_B_ne]

-- ──────────────────────────────────────────────────────────────────────────
-- LEMMA 4.2 (Exact Finite-Sample Geometric Decomposition)
--
-- The main identity, equation displayed on the manuscript:
--
--   ‖residual‖² = ‖B_rel‖² · M_{FP,T₀}        ← Bias FP Term
--               + ‖d‖² · M_{δ,T₀}             ← Relevance Violation Term
--               + ‖(I−P_𝒰)e‖²                 ← Idiosyncratic Noise Term
--               + 2B'_rel(I−P_𝒰)d             ← Cross Term 1
--               + 2B'_rel(I−P_𝒰)e             ← Cross Term 2
--               + 2d'(I−P_𝒰)e                 ← Cross Term 3
--
-- This is a purely algebraic identity—no probabilistic content.
-- ──────────────────────────────────────────────────────────────────────────

lemma lemma_4_2
    (h_B_ne_zero : sqNorm (B_rel d) ≠ 0)
    (h_d_ne_zero : sqNorm (d_vec d) ≠ 0) :
    sqNorm (residual_vec d) =
    sqNorm (B_rel d) * M_FP d +
    sqNorm (d_vec d) * M_delta d +
    sqNorm (annihilator (U_mat d) * e_vec d) +
    2 * ((B_rel d)ᵀ * (annihilator (U_mat d) * d_vec d)) 0 0 +
    2 * ((B_rel d)ᵀ * (annihilator (U_mat d) * e_vec d)) 0 0 +
    2 * ((d_vec d)ᵀ * (annihilator (U_mat d) * e_vec d)) 0 0 := by
  -- First apply the substitution: residual = (I−P_𝒰)(B_rel + d + e)
  have h_orth := U_mat_orth_X_rel d
  have h_subst := lemma_4_2_substitution d h_orth
  rw[h_subst]
  -- Then apply the quadratic expansion using symmetry + idempotency of (I−P_𝒰)
  have h_symm := annihilator_transpose (U_mat d)
  have h_idemp := annihilator_mul_self (U_mat d)
  have h_exp := lemma_4_2_expansion (B_rel d) (d_vec d) (e_vec d) (annihilator (U_mat d))
    h_symm h_idemp
  rw[h_exp]
  -- Cancel: ‖B‖² · (‖(I−P_𝒰)B‖²/‖B‖²) = ‖(I−P_𝒰)B‖²
  unfold M_FP M_delta
  have h_cancel_B : sqNorm (B_rel d) * (sqNorm (annihilator (U_mat d) * B_rel d) /
    sqNorm (B_rel d)) = sqNorm (annihilator (U_mat d) * B_rel d) := by
      rw[mul_comm, div_mul_cancel₀ _ h_B_ne_zero]
  have h_cancel_d : sqNorm (d_vec d) * (sqNorm (annihilator (U_mat d) * d_vec d) /
    sqNorm (d_vec d)) = sqNorm (annihilator (U_mat d) * d_vec d) := by
      rw[mul_comm, div_mul_cancel₀ _ h_d_ne_zero]
  rw[h_cancel_B, h_cancel_d]

-- Bounds: 0 ≤ M_{FP} ≤ 1 and 0 ≤ M_δ ≤ 1
-- (attenuation factors are proper fractions, as ratios of projected to total norm)
lemma M_FP_nonneg (_h_B_ne : sqNorm (B_rel d) ≠ 0) : 0 ≤ M_FP d := by
  unfold M_FP
  apply div_nonneg (sqNorm_nonneg _) (sqNorm_nonneg _)

lemma M_FP_le_one (h_B_ne : sqNorm (B_rel d) ≠ 0) : M_FP d ≤ 1 := by
  rw[M_FP_eq_one_sub_cos_sq d h_B_ne]
  have h_div_pos : 0 ≤ sqNorm (proj (U_mat d) * B_rel d) / sqNorm (B_rel d) := div_nonneg
    (sqNorm_nonneg _) (sqNorm_nonneg _)
  linarith

lemma M_delta_nonneg (_h_d_ne : sqNorm (d_vec d) ≠ 0) : 0 ≤ M_delta d := by
  unfold M_delta
  apply div_nonneg (sqNorm_nonneg _) (sqNorm_nonneg _)

lemma M_delta_le_one (h_d_ne : sqNorm (d_vec d) ≠ 0) : M_delta d ≤ 1 := by
  rw[M_delta_eq_one_sub_cos_sq d h_d_ne]
  have h_div_pos : 0 ≤ sqNorm (proj (U_mat d) * d_vec d) / sqNorm (d_vec d) :=
    div_nonneg (sqNorm_nonneg _) (sqNorm_nonneg _)
  linarith

end Lemma42

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART II: THEOREM 4.3 — Asymptotic Resolution of the Pre-Treatment Residual
-- (Manuscript §4.3, Theorem 4.3)
--
-- This section takes the exact 6-term identity of Lemma 4.2 and shows that,
-- after dividing by T₀ and taking limits:
--
--   T₀⁻¹‖r‖² →ₚ B²_FP · M_{FP,T₀} + δ² · M_{δ,T₀} + σ²(1 − κ_{T₀}) + oₚ(1)
--
-- The three cross terms vanish by distinct mechanisms:
--   Cross Term 1: via Cauchy–Schwarz + M_δ → 0 (Assumption 4.1(i))
--   Cross Term 2: via cross-sectional orthogonality E[ε₀ₜεᵢₜ] = 0 (Assump 2.2a)
--   Cross Term 3: via the same orthogonality + weak serial dependence (Assump 2.2b)
--
-- The three quadratic terms converge to their probability limits:
--   T₀⁻¹‖B_rel‖² →ₚ B²_FP       (Proposition 3.1)
--   T₀⁻¹‖d‖²     →  δ²          (Cesàro averaging of δ_t²)
--   T₀⁻¹‖(I−P_𝒰)e‖² →ₚ σ²(1−κ)  (trace concentration + rank saturation)
-- ═══════════════════════════════════════════════════════════════════════════════

section Theorem43

open Filter Topology Lemma42

variable {r N_rel N_irrel : ℕ}

-- Bridge: construct a Lemma42_Data bundle from the stochastic DGP at a given (T, ω).
def mk_Lemma42_Data {Ω : Type*} [MeasurableSpace Ω] (pd : Prop31_Data r N_rel Ω)
  (X_irrel : (T : ℕ) → Ω → Matrix (Fin T) (Fin N_irrel) ℝ)
  (delta : (T : ℕ) → Matrix (Fin T) (Fin 1) ℝ)
  (T : ℕ) (ω : Ω) : Lemma42_Data T r N_rel N_irrel :=
  { F := pd.F T ω, lambda_0 := pd.lambda_0, delta := delta T,
    eps_0 := pd.eps_0 T ω, X_rel := X_rel pd T ω, X_irrel := X_irrel T ω }

-- ──────────────────────────────────────────────────────────────────────────
-- Theorem43_Data: Encoding of Assumptions 2.1–2.4 + Assumption 4.1(i)
--
-- This structure bundles all the asymptotic hypotheses needed for Theorem 4.3.
-- Each field maps to a specific manuscript assumption:
--
--   pd                   : Proposition 3.1 data (DGP, Assumptions 2.2–2.3)
--   X_irrel              : Irrelevant donor block (Section 2.1)
--   delta_seq, delta_det : Structural violation δ (deterministic, Section 2.1)
--   h_delta_sq_tendsto   : δ_t² → δ² (violation intensity stabilizes)
--   rsd                  : Rank saturation κ_{T₀} → κ (Assumption 2.1)
--   h_noise_quad_form    : E[‖(I−P_𝒰)e‖²] = σ²·tr(I−P_𝒰) (Assump 2.2d + 2.3)
--   h_noise_trace_var    : Var(T⁻¹‖(I−P_𝒰)e‖²) → 0 (trace concentration)
--   h_cross_2_ortho      : Cross-sectional orthogonality for B'_rel e (Assump 2.2a)
--   h_cross_3_ortho      : Cross-sectional orthogonality for d'e (Assump 2.2a/b)
-- ──────────────────────────────────────────────────────────────────────────

structure Theorem43_Data (r N_rel N_irrel : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  pd : Prop31_Data r N_rel Ω
  h_prob : IsProbabilityMeasure pd.μ
  X_irrel : (T : ℕ) → Ω → Matrix (Fin T) (Fin N_irrel) ℝ

  -- Structural violation δ: a deterministic sequence (Section 2.1)
  delta_seq : ℕ → ℝ
  delta_det : (T : ℕ) → Matrix (Fin T) (Fin 1) ℝ
  h_delta_det_eq : ∀ T t, delta_det T t 0 = delta_seq (t : ℕ)

  -- Non-degeneracy: B_rel and d never vanish (needed for M_FP, M_δ denominators)
  h_B_ne_zero : ∀ T ω, sqNorm (B_rel (mk_Lemma42_Data pd X_irrel delta_det T ω)) ≠ 0
  h_d_ne_zero : ∀ T ω, sqNorm (d_vec (mk_Lemma42_Data pd X_irrel delta_det T ω)) ≠ 0

  -- Assumption 2.3 / 2.2(e): Factors and errors are orthogonal to δ asymptotically
  -- T⁻¹F'δ →ₚ 0  and  T⁻¹E'_rel δ →ₚ 0
  h_lim_Fdelta : MatrixLimitInProb pd.μ
    (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((pd.F T ω)ᵀ * delta_det T)) 0
  h_lim_Edelta : MatrixLimitInProb pd.μ
    (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((pd.E_rel T ω)ᵀ * delta_det T)) 0

  -- Cesàro limit of δ²_t: the violation intensity stabilizes
  -- (δ_t)² → δ² pointwise, from which T⁻¹Σδ²_t → δ² follows by Cesàro averaging
  delta_sq : ℝ
  h_delta_sq_tendsto : Tendsto (fun t : ℕ => (delta_seq t) ^ 2) atTop (nhds delta_sq)

  -- Noise variance σ² (Assumption 2.3)
  sigma_sq : ℝ
  h_sigma_pos : 0 < sigma_sq

  -- Rank saturation: s/(T−r) → κ (Assumption 2.1)
  rsd : RankSaturationData r
  h_rank_eq : ∀ T ω, Matrix.rank (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) = rsd.s T

  -- Noise quadratic form identity: E[‖(I−P_𝒰)e‖²] = σ²·tr(I−P_𝒰)
  -- (Assumption 2.2(d) + 2.3: the noise is isotropic with variance σ²)
  h_noise_quad_form : ∀ T, ∫ ω, sqNorm (annihilator (U_mat
    (mk_Lemma42_Data pd X_irrel delta_det T ω)) * e_vec (mk_Lemma42_Data
      pd X_irrel delta_det T ω)) ∂pd.μ =
      sigma_sq * ∫ ω, Matrix.trace (annihilator (U_mat (mk_Lemma42_Data pd
        X_irrel delta_det T ω))) ∂pd.μ

  -- Trace concentration (Assumption 2.2(d)): Var(T⁻¹‖(I−P_𝒰)e‖²) → 0
  -- Imported from RandomMatrix.TraceConcentration
  h_noise_trace_meas : ∀ (T : ℕ), AEStronglyMeasurable (fun ω =>
      (T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
        e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω)) -
      (T : ℝ)⁻¹ * ∫ ω', sqNorm (annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω')) *
        e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω')) ∂pd.μ) pd.μ
  h_noise_trace_sq_int : ∀ (T : ℕ), Integrable (fun ω =>
      ((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
        e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω)) -
       (T : ℝ)⁻¹ * ∫ ω', sqNorm (annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω')) *
         e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω')) ∂pd.μ) ^ 2) pd.μ
  h_noise_trace_var : Tendsto (fun (T : ℕ) => ∫ ω,
    (((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
      e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω))) -
     ((T : ℝ)⁻¹ * ∫ ω', sqNorm (annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω')) *
       e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω')) ∂pd.μ))^2 ∂pd.μ)
    atTop (nhds 0)

  -- Cross Term 2 orthogonality (Assumption 2.2a): Var(((I−P_𝒰)B_rel)'e) = O(T)
  h_cross_2_ortho : CrossSectionalOrthogonalityBound pd.μ
    (fun (T : ℕ) ω => annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
      B_rel (mk_Lemma42_Data pd X_irrel delta_det T ω))
    (fun (T : ℕ) ω => e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω))
  h_cross_2_meas : ∀ (T : ℕ), AEStronglyMeasurable (fun ω => (T : ℝ)⁻¹ *
    ((annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
      B_rel (mk_Lemma42_Data pd X_irrel delta_det T ω))ᵀ * e_vec
        (mk_Lemma42_Data pd X_irrel delta_det T ω)) 0 0) pd.μ
  h_cross_2_int : ∀ (T : ℕ), Integrable (fun ω => ((T : ℝ)⁻¹ *
    ((annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
      B_rel (mk_Lemma42_Data pd X_irrel delta_det T ω))ᵀ *
        e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω)) 0 0 - 0)^2) pd.μ

  -- Cross Term 3 orthogonality (Assumption 2.2a/b): Var(((I−P_𝒰)d)'e) = O(T)
  h_cross_3_ortho : CrossSectionalOrthogonalityBound pd.μ
    (fun (T : ℕ) ω => annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
      d_vec (mk_Lemma42_Data pd X_irrel delta_det T ω))
    (fun (T : ℕ) ω => e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω))
  h_cross_3_meas : ∀ (T : ℕ), AEStronglyMeasurable (fun ω => (T : ℝ)⁻¹ *
    ((annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
      d_vec (mk_Lemma42_Data pd X_irrel delta_det T ω))ᵀ * e_vec
        (mk_Lemma42_Data pd X_irrel delta_det T ω)) 0 0) pd.μ
  h_cross_3_int : ∀ (T : ℕ), Integrable (fun ω => ((T : ℝ)⁻¹ *
    ((annihilator (U_mat (mk_Lemma42_Data pd X_irrel delta_det T ω)) *
      d_vec (mk_Lemma42_Data pd X_irrel delta_det T ω))ᵀ *
        e_vec (mk_Lemma42_Data pd X_irrel delta_det T ω)) 0 0 - 0)^2) pd.μ

instance {r N_rel N_irrel Ω} [MeasurableSpace Ω] (d : Theorem43_Data r N_rel N_irrel Ω) :
  IsProbabilityMeasure d.pd.μ := d.h_prob

def Theorem43_Data.d_seq {Ω : Type*} [MeasurableSpace Ω] (d : Theorem43_Data r N_rel N_irrel Ω)
  (T : ℕ) (ω : Ω) : Lemma42_Data T r N_rel N_irrel :=
  mk_Lemma42_Data d.pd d.X_irrel d.delta_det T ω

variable {Ω : Type*} [MeasurableSpace Ω] (d43 : Theorem43_Data r N_rel N_irrel Ω)

-- ──────────────────────────────────────────────────────────────────────────
-- Derived: T⁻¹‖δ‖² → δ²  (Cesàro averaging)
--
-- Manuscript p.6: "T₀⁻¹‖δ‖² = T₀⁻¹ Σ δ²_t → δ² by direct Cesàro averaging."
-- The primitive assumption is (δ_t)² → δ² (the violation intensity stabilizes),
-- and the Cesàro convergence follows by Mathlib's `Tendsto.cesaro_smul`.
-- ──────────────────────────────────────────────────────────────────────────

lemma derived_delta_raw_cesaro :
    Tendsto (fun (T : ℕ) => (T : ℝ)⁻¹ * sqNorm (d43.delta_det T)) atTop (nhds d43.delta_sq) := by
  have h_eq : ∀ T, sqNorm (d43.delta_det T) = ∑ t : Fin T, (d43.delta_seq (t : ℕ))^2 := by
    intro T
    unfold sqNorm
    rw [inner_eq_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw[d43.h_delta_det_eq T t]
    ring
  have h_fun_eq : (fun (T : ℕ) => (T : ℝ)⁻¹ * sqNorm (d43.delta_det T)) =
                  (fun (T : ℕ) => (T : ℝ)⁻¹ * ∑ t : Fin T, (d43.delta_seq (t : ℕ))^2) := by
    funext T; rw [h_eq T]
  rw [h_fun_eq]
  -- Derive Cesàro convergence from pointwise convergence via Mathlib's cesaro_smul
  have h_cesaro := d43.h_delta_sq_tendsto.cesaro_smul
  -- Bridge: our form uses (mul, Fin sum), cesaro_smul uses (smul, Finset.range sum)
  apply Filter.Tendsto.congr _ h_cesaro
  intro T
  congr 1; exact (Fin.sum_univ_eq_sum_range (fun i => d43.delta_seq i ^ 2) T).symm

-- ──────────────────────────────────────────────────────────────────────────
-- Bridge: T⁻¹‖B_rel‖² = bias_original (connects to Proposition 3.1)
--
-- This is a definitional unfolding: the Lemma 4.2 quantity B_rel = (I−P_{X_rel})Fλ₀
-- is exactly the bias_original from Proposition 3.1's formalization.
-- ──────────────────────────────────────────────────────────────────────────

lemma bridge_B_rel_bias_original (T : ℕ) (ω : Ω) :
  (T : ℝ)⁻¹ * sqNorm (B_rel (d43.d_seq T ω)) = bias_original d43.pd T ω := by
  unfold sqNorm B_rel annihilator proj Theorem43_Data.d_seq mk_Lemma42_Data
  unfold bias_original B_rel_vec P_Xrel X_rel
  simp only[Matrix.smul_apply, smul_eq_mul]

-- B²_FP from Proposition 3.1: the asymptotic irreducible bias
noncomputable def B_FP_sq_val : ℝ :=
  B_FP_sq_test d43.pd.Sigma_F d43.pd.Omega_rel d43.pd.Lambda_rel d43.pd.lambda_0

-- ──────────────────────────────────────────────────────────────────────────
-- Derived: T⁻¹‖P_{X_rel} δ‖² →ₚ 0
--
-- Manuscript: "T₀⁻¹‖P_{X_rel}δ‖² → 0" by the algebraic identity
--   T⁻¹‖P_X δ‖² = (T⁻¹X'δ)'(T⁻¹X'X)⁻¹(T⁻¹X'δ)
-- Since both T⁻¹F'δ →ₚ 0 and T⁻¹E'_rel δ →ₚ 0, the quadratic form vanishes.
-- ──────────────────────────────────────────────────────────────────────────

lemma delta_proj_zero_derived :
    TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (proj (X_rel d43.pd T ω) *
      d43.delta_det T))
      atTop (fun _ => 0) := by
  have h_Xrel_delta : MatrixLimitInProb d43.pd.μ
      (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * d43.delta_det T))
        (0 : Matrix (Fin N_rel) (Fin 1) ℝ) := by
    -- T⁻¹X'_rel δ = Λ_rel(T⁻¹F'δ) + T⁻¹E'_rel δ → 0 + 0 = 0
    have heq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * d43.delta_det T)) =
        fun (T : ℕ) ω => d43.pd.Lambda_rel * ((T : ℝ)⁻¹ • ((d43.pd.F T ω)ᵀ * d43.delta_det T)) +
                 (T : ℝ)⁻¹ • ((d43.pd.E_rel T ω)ᵀ * d43.delta_det T) := by
      funext T ω
      unfold X_rel
      rw[Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.add_mul, smul_add, Matrix.mul_assoc, ← Matrix.mul_smul]
    rw [heq]
    have h1 := MatrixLimitInProb.mul_left d43.pd.μ d43.pd.Lambda_rel d43.h_lim_Fdelta
    rw[Matrix.mul_zero] at h1
    have h_sum := MatrixLimitInProb.add d43.pd.μ h1 d43.h_lim_Edelta
    rw [add_zero] at h_sum
    exact h_sum
  -- T⁻¹‖P_{X_rel}δ‖² = (T⁻¹X'δ)'(T⁻¹X'X)⁻¹(T⁻¹X'δ)
  have h_alg : ∀ (T : ℕ) ω,
      (T : ℝ)⁻¹ * sqNorm (proj (X_rel d43.pd T ω) * d43.delta_det T) =
      (((T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * d43.delta_det T))ᵀ *
        ((T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * X_rel d43.pd T ω)).pinv *
        ((T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * d43.delta_det T))) 0 0 := by
    intro T ω
    have h_sq_eq : sqNorm (proj (X_rel d43.pd T ω) * d43.delta_det T) =
        ((d43.delta_det T)ᵀ * proj (X_rel d43.pd T ω) * d43.delta_det T) 0 0 := by
      unfold sqNorm
      rw[Matrix.transpose_mul, proj_transpose, Matrix.mul_assoc,
          ← Matrix.mul_assoc (proj (X_rel d43.pd T ω))
            (proj (X_rel d43.pd T ω)) (d43.delta_det T),
          proj_mul_self (X_rel d43.pd T ω), ← Matrix.mul_assoc]
    have h_proj_expand :
        ((d43.delta_det T)ᵀ * proj (X_rel d43.pd T ω) * d43.delta_det T) 0 0 =
        (((X_rel d43.pd T ω)ᵀ * d43.delta_det T)ᵀ *
          ((X_rel d43.pd T ω)ᵀ * X_rel d43.pd T ω).pinv *
          ((X_rel d43.pd T ω)ᵀ * d43.delta_det T)) 0 0 := by
      unfold proj
      simp only[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw[h_sq_eq, h_proj_expand]
    by_cases hT : T = 0
    · subst hT; simp
    · have hT_real : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
      have hT_inv_real : (T : ℝ)⁻¹ ≠ 0 := inv_ne_zero hT_real
      rw[Matrix.pinv_smul ((T : ℝ)⁻¹) hT_inv_real]
      simp only[Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
                 smul_smul, Matrix.smul_apply, smul_eq_mul, inv_inv]
      rw[mul_inv_cancel₀ hT_real, one_mul]
  -- Now compose: 0'·G⁻¹·0 = 0, so the triple product converges to 0
  have h_gram_conv := gram_limit  d43.pd
  have h_gram_inv := MatrixLimitInProb.pinv d43.pd.μ h_gram_conv
    (G_test_det_ne_zero d43.pd)
  have h_transp := MatrixLimitInProb.transpose d43.pd.μ h_Xrel_delta
  have h_triple := MatrixLimitInProb.mul d43.pd.μ
      (MatrixLimitInProb.mul d43.pd.μ h_transp h_gram_inv) h_Xrel_delta
  have h_zero : (0 : Matrix (Fin 1) (Fin 1) ℝ) =
      (0 : Matrix (Fin N_rel) (Fin 1) ℝ)ᵀ * (G_test d43.pd.Sigma_F
        d43.pd.Omega_rel d43.pd.Lambda_rel)⁻¹ * (0 : Matrix (Fin N_rel) (Fin 1) ℝ) := by
    simp only[Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero]
  rw [← h_zero] at h_triple
  have h_entry := h_triple 0 0
  simp only [Matrix.zero_apply] at h_entry
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h_entry ε hε)
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T
    have heq_set : {ω | ε ≤ edist ((T : ℝ)⁻¹ * sqNorm (proj (X_rel d43.pd T ω) *
      d43.delta_det T)) 0} = {ω | ε ≤ edist ((((T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ *
        d43.delta_det T))ᵀ * ((T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * X_rel d43.pd T ω)).pinv *
          ((T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * d43.delta_det T))) 0 0) 0} := by
      ext ω
      have h_val : (T : ℝ)⁻¹ * sqNorm (proj (X_rel d43.pd T ω) * d43.delta_det T) =
          (((T : ℝ)⁻¹ • ((X_rel d43.pd T ω)ᵀ * d43.delta_det T))ᵀ * ((T : ℝ)⁻¹ •
            ((X_rel d43.pd T ω)ᵀ * X_rel d43.pd T ω)).pinv * ((T : ℝ)⁻¹ •
              ((X_rel d43.pd T ω)ᵀ * d43.delta_det T))) 0 0 := h_alg T ω
      simp only[Set.mem_setOf_eq, h_val]
    rw[heq_set]

-- ──────────────────────────────────────────────────────────────────────────
-- Derived: T⁻¹‖d‖² →ₚ δ²
--
-- Manuscript p.6: Two-step argument:
--   Step 1: T⁻¹‖δ‖² → δ² (Cesàro, deterministic)
--   Step 2: T⁻¹‖P_{X_rel}δ‖² →ₚ 0 (projection vanishes)
-- Combined via: T⁻¹‖d‖² = T⁻¹‖δ‖² − T⁻¹‖P_{X_rel}δ‖² →ₚ δ² − 0 = δ²
-- ──────────────────────────────────────────────────────────────────────────

lemma derived_d_vec_lim :
    TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω)))
      atTop (fun _ => d43.delta_sq) := by
  -- Step 1: Decompose ‖d‖² = ‖(I−P_X)δ‖² = ‖δ‖² − ‖P_X δ‖²
  have h_eq : ∀ (T : ℕ) ω, (T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω)) =
      (T : ℝ)⁻¹ * sqNorm (d43.delta_det T) - (T : ℝ)⁻¹ * sqNorm (proj (X_rel d43.pd T ω) *
        d43.delta_det T) := by
    intro T ω
    unfold d_vec
    dsimp [Theorem43_Data.d_seq, mk_Lemma42_Data]
    rw [sqNorm_annihilator (X_rel d43.pd T ω)]
    ring
  -- Step 2: T⁻¹‖δ‖² → δ² (deterministic Cesàro) and T⁻¹‖P_X δ‖² →ₚ 0
  have h_det_prob := deterministic_tendstoInMeasure d43.pd.μ (derived_delta_raw_cesaro d43)
  have h_final_limit := tendstoInMeasure_scalar_add d43.pd.μ h_det_prob
    (tendstoInMeasure_scalar_mul_const d43.pd.μ (-1) (delta_proj_zero_derived d43))
  -- Conclude: δ² + (−1)·0 = δ²
  intro ε hε
  have h_lim := h_final_limit ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T
    have heq_set : {ω | ε ≤ edist ((T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω))) d43.delta_sq} =
                   {ω | ε ≤ edist ((T : ℝ)⁻¹ * sqNorm (d43.delta_det T) + ((T : ℝ)⁻¹ * sqNorm (proj
                     (X_rel d43.pd T ω) * d43.delta_det T)) * -1) (d43.delta_sq + 0 * -1)} := by
      ext ω
      simp only[Set.mem_setOf_eq]
      have h_val : (T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω)) =
        (T : ℝ)⁻¹ * sqNorm (d43.delta_det T) +
        ((T : ℝ)⁻¹ * sqNorm (proj (X_rel d43.pd T ω) * d43.delta_det T)) * -1 := by
        rw[h_eq T ω]; ring
      rw [h_val]
      ring_nf
    rw[heq_set]

-- ──────────────────────────────────────────────────────────────────────────
-- Cross Term 1: 2T⁻¹B'_rel(I−P_𝒰)d →ₚ 0
--
-- Manuscript p.6–7:
--   |T⁻¹B'(I−P_𝒰)d|² ≤ (T⁻¹‖B‖²)(T⁻¹‖d‖²)·M_δ
-- Since T⁻¹‖B‖² →ₚ B²_FP > 0, T⁻¹‖d‖² → δ² > 0, and M_δ →ₚ 0
-- (Assumption 4.1(i)), the product vanishes.
--
-- This is the term that requires the *violation absorption* hypothesis:
-- norm scaling alone gives O_p(1), not o_p(1).
-- ──────────────────────────────────────────────────────────────────────────

lemma cross_term_1_vanishes (d43 : Theorem43_Data r N_rel N_irrel Ω)
    (h_M_delta : TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => M_delta (d43.d_seq T ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * (2 * ((B_rel (d43.d_seq T ω))ᵀ *
      (annihilator (U_mat (d43.d_seq T ω)) * d_vec (d43.d_seq T ω))) 0 0)) atTop (fun _ => 0) := by
  let v := fun (T : ℕ) ω => B_rel (d43.d_seq T ω)
  let w := fun (T : ℕ) ω => annihilator (U_mat (d43.d_seq T ω)) * d_vec (d43.d_seq T ω)
  -- T⁻¹‖v‖² = T⁻¹‖B_rel‖² →ₚ B²_FP (Proposition 3.1)
  have hv : TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (v T ω))
    atTop (fun _ => B_FP_sq_val d43) := by
    have h_bias := (proposition_3_1_i d43.pd).1
    have heq_fun : (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (v T ω)) = (fun (T : ℕ) ω =>
      bias_original d43.pd T ω) := by
      funext T ω
      exact bridge_B_rel_bias_original d43 T ω
    rw[heq_fun]
    exact h_bias
  -- T⁻¹‖w‖² = T⁻¹‖(I−P_𝒰)d‖² = (T⁻¹‖d‖²)·M_δ →ₚ δ²·0 = 0
  have hw : TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (w T ω))
    atTop (fun _ => 0) := by
    have h_d_sq : TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ *
      sqNorm (d_vec (d43.d_seq T ω))) atTop (fun _ => d43.delta_sq) := derived_d_vec_lim d43
    have h_mul := tendstoInMeasure_scalar_mul_varying d43.pd.μ h_d_sq h_M_delta
    have h_rw : d43.delta_sq * 0 = 0 := mul_zero _
    rw[h_rw] at h_mul
    have h_eq : ∀ (T : ℕ) ω, (T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω)) *
      M_delta (d43.d_seq T ω) =
        (T : ℝ)⁻¹ * sqNorm (w T ω) := by
      intro T ω
      dsimp[M_delta, w]
      by_cases hd : sqNorm (d_vec (d43.d_seq T ω)) = 0
      · have h_ne := d43.h_d_ne_zero T ω
        exact absurd hd h_ne
      · rw [mul_assoc]
        congr 1
        rw [mul_comm]
        exact div_mul_cancel₀ _ hd
    have h_fun_eq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω)) *
      M_delta (d43.d_seq T ω)) =
                    (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (w T ω)) := by
      funext T ω; exact h_eq T ω
    rw [h_fun_eq] at h_mul
    exact h_mul
  -- Apply Cauchy–Schwarz: T⁻¹v'w →ₚ 0, then multiply by 2
  have h_cs := tendstoInMeasure_cauchy_schwarz d43.pd.μ v w (B_FP_sq_val d43) hv hw
  have h_double := tendstoInMeasure_mul_const_zero d43.pd.μ h_cs 2
  have heq : (fun (T : ℕ) ω => 2 * ((T : ℝ)⁻¹ * ((v T ω)ᵀ * w T ω) 0 0)) =
             (fun (T : ℕ) ω => (T : ℝ)⁻¹ * (2 * ((v T ω)ᵀ * w T ω) 0 0)) :=
               by funext T ω; ring
  rw [heq] at h_double
  exact h_double

-- ──────────────────────────────────────────────────────────────────────────
-- Cross Terms 2 & 3: L² convergence via cross-sectional orthogonality
--
-- Manuscript p.7: "by the cross-sectional orthogonality E[ε₀ₜεᵢₜ] = 0
-- (Assumption 2.2(a)) and Cauchy–Schwarz"
--
-- The variance bound Var(c'e) ≤ K·T gives E[(T⁻¹c'e)²] ≤ K/T → 0,
-- so T⁻¹c'e →_{L²} 0, hence →ₚ 0.
-- ──────────────────────────────────────────────────────────────────────────

-- Cross Term 2: 2T⁻¹B'_rel(I−P_𝒰)e →ₚ 0  (Assumption 2.2(a))
lemma cross_term_2_vanishes (d43 : Theorem43_Data r N_rel N_irrel Ω) :
    TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * (2 * ((B_rel (d43.d_seq T ω))ᵀ *
      (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω))) 0 0)) atTop (fun _ => 0) := by
  let c := fun (T : ℕ) ω => annihilator (U_mat (d43.d_seq T ω)) * B_rel (d43.d_seq T ω)
  let e := fun (T : ℕ) ω => e_vec (d43.d_seq T ω)
  have h_base := cross_term_vanishes_by_orthogonality c e d43.h_cross_2_ortho
    d43.h_cross_2_meas d43.h_cross_2_int
  -- Rewrite: B'(I−P_𝒰)e = ((I−P_𝒰)B)'e  (using symmetry of I−P_𝒰)
  have heq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ * (2 * ((B_rel (d43.d_seq T ω))ᵀ *
    (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω))) 0 0)) =
             (fun (T : ℕ) ω => 2 * ((T : ℝ)⁻¹ * ((c T ω)ᵀ * e T ω) 0 0)) := by
    funext T ω
    dsimp [c, e, sqNorm]
    have h_symm : (annihilator (U_mat (d43.d_seq T ω)))ᵀ = annihilator (U_mat (d43.d_seq T ω)) :=
      annihilator_transpose _
    have h_inner : (B_rel (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
      e_vec (d43.d_seq T ω)) = (annihilator (U_mat (d43.d_seq T ω)) * B_rel (d43.d_seq T ω))ᵀ *
      e_vec (d43.d_seq T ω) := by
      rw[Matrix.transpose_mul, h_symm, Matrix.mul_assoc]
    rw[h_inner]
    ring
  rw[heq]
  exact tendstoInMeasure_mul_const_zero d43.pd.μ h_base 2

-- Cross Term 3: 2T⁻¹d'(I−P_𝒰)e →ₚ 0  (Assumption 2.2(a)/(b))
lemma cross_term_3_vanishes (d43 : Theorem43_Data r N_rel N_irrel Ω) :
    TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * (2 * ((d_vec (d43.d_seq T ω))ᵀ *
    (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω))) 0 0)) atTop (fun _ => 0) := by
  let c := fun (T : ℕ) ω => annihilator (U_mat (d43.d_seq T ω)) * d_vec (d43.d_seq T ω)
  let e := fun (T : ℕ) ω => e_vec (d43.d_seq T ω)
  have h_base := cross_term_vanishes_by_orthogonality c e d43.h_cross_3_ortho
    d43.h_cross_3_meas d43.h_cross_3_int
  -- Rewrite: d'(I−P_𝒰)e = ((I−P_𝒰)d)'e  (using symmetry of I−P_𝒰)
  have heq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ * (2 * ((d_vec (d43.d_seq T ω))ᵀ *
             (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω))) 0 0)) =
             (fun (T : ℕ) ω => 2 * ((T : ℝ)⁻¹ * ((c T ω)ᵀ * e T ω) 0 0)) := by
    funext T ω
    dsimp [c, e, sqNorm]
    have h_symm : (annihilator (U_mat (d43.d_seq T ω)))ᵀ = annihilator (U_mat (d43.d_seq T ω)) :=
      annihilator_transpose _
    have h_inner : (d_vec (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
                   e_vec (d43.d_seq T ω)) = (annihilator (U_mat (d43.d_seq T ω)) *
                   d_vec (d43.d_seq T ω))ᵀ * e_vec (d43.d_seq T ω) := by
      rw[Matrix.transpose_mul, h_symm, Matrix.mul_assoc]
    rw[h_inner]
    ring
  rw [heq]
  exact tendstoInMeasure_mul_const_zero d43.pd.μ h_base 2

-- ──────────────────────────────────────────────────────────────────────────
-- Noise term: T⁻¹‖(I−P_𝒰)e‖² →ₚ σ²(1 − κ)
--
-- Manuscript p.6: "by the rank condition in Assumption 2.1 together with
-- the uniform eigenvalue bounds on Ω_irrel in Assumption 2.2(a)"
--
-- The proof decomposes into three sub-convergences:
-- (1) Concentration: T⁻¹‖(I−P_𝒰)e‖² ≈ E[T⁻¹‖(I−P_𝒰)e‖²]  (trace conc.)
-- (2) Expectation:   E[T⁻¹‖(I−P_𝒰)e‖²] = σ²·(T−s)/T → σ²(1−κ)
-- (3) Rank limit:    s/(T−r) → κ (Assumption 2.1)
-- ──────────────────────────────────────────────────────────────────────────

lemma derive_h_e_trace (d43 : Theorem43_Data r N_rel N_irrel Ω) :
  TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω =>
    (T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω)) -
    d43.sigma_sq * (1 - (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ))))
  atTop (fun _ => 0) := by
  -- Sub-step (2): E[‖(I−P_𝒰)e‖²] = σ²·tr(I−P_𝒰) = σ²·(T − s)
  have h_exp : ∀ T, ∫ ω, sqNorm (annihilator (U_mat (d43.d_seq T ω)) *
      e_vec (d43.d_seq T ω)) ∂d43.pd.μ = d43.sigma_sq * ∫ ω, Matrix.trace
      (annihilator (U_mat (d43.d_seq T ω))) ∂d43.pd.μ := d43.h_noise_quad_form
  -- tr(I − P_𝒰) = T − s  (codimension of 𝒰)
  have h_trace : ∀ T ω, Matrix.trace (annihilator (U_mat (d43.d_seq T ω))) =
    (T : ℝ) - (d43.rsd.s T : ℝ) := by
    intro T ω; rw[trace_annihilator_eq_codim]
    have hr : Matrix.rank (U_mat (d43.d_seq T ω)) = d43.rsd.s T := d43.h_rank_eq T ω
    rw [hr]
  -- Sub-step: T⁻¹ · E[‖(I−P_𝒰)e‖²] = σ²·(T−s)/T → σ²·(1−κ)
  have h_exp_diff : Tendsto (fun (T : ℕ) => (T : ℝ)⁻¹ * ∫ ω, sqNorm (annihilator
    (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω)) ∂d43.pd.μ - d43.sigma_sq *
    (1 - d43.rsd.kappa)) atTop (nhds 0) := by
    have h_simpl : ∀ (T : ℕ), ((T : ℝ)⁻¹ * ∫ ω, sqNorm (annihilator (U_mat
                  (d43.d_seq T ω)) * e_vec (d43.d_seq T ω)) ∂d43.pd.μ) =
                   d43.sigma_sq * (((T : ℝ) - (d43.rsd.s T : ℝ)) / (T : ℝ)) := by
      intro T; rw [h_exp T]
      have h_int : ∫ ω, Matrix.trace (annihilator (U_mat (d43.d_seq T ω))) ∂d43.pd.μ =
        (T : ℝ) - (d43.rsd.s T : ℝ) := by
        have heq : (fun ω => Matrix.trace (annihilator (U_mat (d43.d_seq T ω)))) = fun _ =>
          (T : ℝ) - (d43.rsd.s T : ℝ) := by
          funext ω; exact h_trace T ω
        rw[heq, integral_const]; simp
      rw [h_int]; ring_nf
    have h_eq : (fun (T : ℕ) => (T : ℝ)⁻¹ * ∫ ω, sqNorm (annihilator (U_mat (d43.d_seq T ω)) *
                e_vec (d43.d_seq T ω)) ∂d43.pd.μ - d43.sigma_sq * (1 - d43.rsd.kappa)) =
                (fun (T : ℕ) => d43.sigma_sq * ((((T : ℝ) - (d43.rsd.s T : ℝ)) /
                (T : ℝ)) - (1 - d43.rsd.kappa))) := by
      funext T; rw [h_simpl T]; ring
    rw [h_eq]
    have h_zero : (0 : ℝ) = d43.sigma_sq * 0 := by ring
    rw [h_zero]
    have h_const : Tendsto (fun (_ : ℕ) => 1 - d43.rsd.kappa) atTop
      (nhds (1 - d43.rsd.kappa)) := tendsto_const_nhds
    have h_sub := Tendsto.sub (tendsto_noise_trace_fraction d43.rsd) h_const
    simp only[sub_self] at h_sub
    exact Tendsto.const_mul d43.sigma_sq h_sub
  -- Sub-step (1): concentration — the random variable concentrates around its mean
  have h_conc : TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω =>
      (T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω)) -
      (T : ℝ)⁻¹ * ∫ ω', sqNorm (annihilator (U_mat (d43.d_seq T ω')) *
        e_vec (d43.d_seq T ω')) ∂d43.pd.μ)
      atTop (fun _ => 0) := by
    exact l2_tendstoInMeasure_zero d43.h_noise_trace_meas
      d43.h_noise_trace_sq_int d43.h_noise_trace_var
  -- Sub-step (3): σ²·(1−κ) vs σ²·(1 − s/(T−r)): bridge the two normalizations
  have h_exp_meas := deterministic_tendstoInMeasure d43.pd.μ h_exp_diff
  have h_kappa_diff : Tendsto (fun T => d43.sigma_sq * (1 - d43.rsd.kappa) -
    d43.sigma_sq * (1 - (d43.rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ)))) atTop (nhds 0) := by
    have h_rank_to_kappa : Tendsto (fun T => (d43.rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ)))
      atTop (nhds d43.rsd.kappa) := d43.rsd.h_kappa_lim
    have h_one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h_y_t : Tendsto (fun T => d43.sigma_sq * (1 - (d43.rsd.s T : ℝ) /
      ((T : ℝ) - (r : ℝ)))) atTop (nhds (d43.sigma_sq * (1 - d43.rsd.kappa))) := by
      exact Tendsto.const_mul d43.sigma_sq (Tendsto.sub h_one h_rank_to_kappa)
    have h_target : Tendsto (fun _ : ℕ => d43.sigma_sq * (1 - d43.rsd.kappa))
      atTop (nhds (d43.sigma_sq * (1 - d43.rsd.kappa))) := tendsto_const_nhds
    have h_sub := Tendsto.sub h_target h_y_t
    simp only [sub_self] at h_sub
    exact h_sub
  have h_kappa_meas := deterministic_tendstoInMeasure d43.pd.μ h_kappa_diff
  -- Combine: (random − mean) + (mean − σ²(1−κ)) + (σ²(1−κ) − σ²(1−s/(T−r)))
  have h_sum1 := tendstoInMeasure_add_zero d43.pd.μ h_conc h_exp_meas
  have h_sum2 := tendstoInMeasure_add_zero d43.pd.μ h_sum1 h_kappa_meas
  -- The three pieces telescope to the desired difference
  intro ε hε
  have h_lim := h_sum2 ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T
    have heq_set : {ω | ε ≤ edist (((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (d43.d_seq T ω)) *
      e_vec (d43.d_seq T ω)) - (T : ℝ)⁻¹ * ∫ (ω' : Ω), sqNorm (annihilator
      (U_mat (d43.d_seq T ω')) * e_vec (d43.d_seq T ω')) ∂d43.pd.μ) + ((T : ℝ)⁻¹ * ∫ (ω' : Ω),
      sqNorm (annihilator (U_mat (d43.d_seq T ω')) * e_vec (d43.d_seq T ω')) ∂d43.pd.μ -
      d43.sigma_sq * (1 - d43.rsd.kappa)) + (d43.sigma_sq * (1 - d43.rsd.kappa) - d43.sigma_sq *
      (1 - (d43.rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ))))) 0} = {ω | ε ≤ edist ((T : ℝ)⁻¹ *
      sqNorm (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω)) - d43.sigma_sq *
      (1 - (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ)))) 0} := by
      ext ω
      simp only[Set.mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero]
      have hr : (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) = (d43.rsd.s T : ℝ) := by
        have h_rank_eq : Matrix.rank (U_mat (d43.d_seq T ω)) = d43.rsd.s T := d43.h_rank_eq T ω
        rw[h_rank_eq]
      rw [hr]
      ring_nf
    rw[heq_set]

-- ══════════════════════════════════════════════════════════════════════════
-- THEOREM 4.3 (Asymptotic Resolution of the Pre-Treatment Residual)
--
-- Manuscript §4.3, Theorem 4.3:
--
--   T⁻¹‖r‖² →ₚ B²_FP · M_{FP,T₀}
--              + δ² · M_{δ,T₀}
--              + σ²(1 − κ_{T₀})
--              + oₚ(1)
--
-- PROOF STRATEGY (differs in organization from the manuscript, same content):
-- The manuscript takes limits of the 6 individual terms. The Lean proof instead:
-- (1) Writes the LHS − RHS using the exact identity of Lemma 4.2
-- (2) Rearranges into 6 terms, each provably oₚ(1):
--     • (T⁻¹‖B‖² − B²_FP) · M_FP          ← oₚ(1) × [0,1]
--     • (T⁻¹‖d‖² − δ²) · M_δ              ← oₚ(1) × [0,1]
--     • noise trace error                 ← trace concentration
--     • cross term 1                      ← Cauchy–Schwarz + M_δ → 0
--     • cross term 2                      ← orthogonality WLLN
--     • cross term 3                      ← orthogonality WLLN
-- (3) Sums the 6 terms via tendstoInMeasure_add_zero.
-- ══════════════════════════════════════════════════════════════════════════

theorem theorem_4_3
    (h_violation_absorption : TendstoInMeasure d43.pd.μ (fun T ω => M_delta (d43.d_seq T ω))
    atTop (fun _ => 0)) :
  TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω =>
    (T : ℝ)⁻¹ * sqNorm (residual_vec (d43.d_seq T ω)) -
    (B_FP_sq_val d43 * M_FP (d43.d_seq T ω) +
     d43.delta_sq * M_delta (d43.d_seq T ω) +
     d43.sigma_sq * (1 - (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ))))
  ) atTop (fun _ => 0) := by
  -- Step 1: Algebraic rearrangement using the exact identity of Lemma 4.2
  -- Express (LHS − RHS) as a sum of 6 vanishing error terms
  have h_alg : ∀ (T : ℕ) ω,
      (T : ℝ)⁻¹ * sqNorm (residual_vec (d43.d_seq T ω)) -
      (B_FP_sq_val d43 * M_FP (d43.d_seq T ω) +
       d43.delta_sq * M_delta (d43.d_seq T ω) +
       d43.sigma_sq * (1 - (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ))))
      =
      -- Error term 1: (T⁻¹‖B‖² − B²_FP) · M_FP
      ((T : ℝ)⁻¹ * sqNorm (B_rel (d43.d_seq T ω)) - B_FP_sq_val d43) * M_FP (d43.d_seq T ω) +
      -- Error term 2: (T⁻¹‖d‖² − δ²) · M_δ
      ((T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω)) - d43.delta_sq) * M_delta (d43.d_seq T ω) +
      -- Error term 3: noise trace concentration error
      ((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω)) -
       d43.sigma_sq * (1 - (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ)))) +
      -- Error term 4: Cross Term 1 (requires M_δ → 0)
      (T : ℝ)⁻¹ * (2 * ((B_rel (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
        d_vec (d43.d_seq T ω))) 0 0) +
      -- Error term 5: Cross Term 2 (orthogonality)
      (T : ℝ)⁻¹ * (2 * ((B_rel (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
        e_vec (d43.d_seq T ω))) 0 0) +
      -- Error term 6: Cross Term 3 (orthogonality)
      (T : ℝ)⁻¹ * (2 * ((d_vec (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
        e_vec (d43.d_seq T ω))) 0 0) := by
    intro T ω
    -- Substitute the exact 6-term expansion from Lemma 4.2
    have h_fs := lemma_4_2 (d43.d_seq T ω) (d43.h_B_ne_zero T ω) (d43.h_d_ne_zero T ω)
    calc (T : ℝ)⁻¹ * sqNorm (residual_vec (d43.d_seq T ω)) - _
      _ = (T : ℝ)⁻¹ * (sqNorm (B_rel (d43.d_seq T ω)) * M_FP (d43.d_seq T ω) +
                       sqNorm (d_vec (d43.d_seq T ω)) * M_delta (d43.d_seq T ω) +
                       sqNorm (annihilator (U_mat (d43.d_seq T ω)) * e_vec (d43.d_seq T ω)) +
                       2 * ((B_rel (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
                         d_vec (d43.d_seq T ω))) 0 0 +
                       2 * ((B_rel (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
                         e_vec (d43.d_seq T ω))) 0 0 +
                       2 * ((d_vec (d43.d_seq T ω))ᵀ * (annihilator (U_mat (d43.d_seq T ω)) *
                         e_vec (d43.d_seq T ω))) 0 0) - _ := by rw[h_fs]
      _ = _ := by ring
  -- Step 2: Show each of the 6 error terms is oₚ(1)
  -- Term 1: (T⁻¹‖B_rel‖² − B²_FP) · M_FP
  -- oₚ(1) × [0,1] = oₚ(1)  since M_FP ∈ [0,1]
  have h_B_diff : TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm
    (B_rel (d43.d_seq T ω)) - B_FP_sq_val d43) atTop (fun _ => 0) := by
    have h_bias := (proposition_3_1_i d43.pd).1
    have heq_fun : (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (B_rel
                   (d43.d_seq T ω)) - B_FP_sq_val d43) =
                   (fun (T : ℕ) ω => bias_original d43.pd T ω -
                   B_FP_sq_test d43.pd.Sigma_F d43.pd.Omega_rel
                   d43.pd.Lambda_rel d43.pd.lambda_0) := by
      funext T ω
      rw [bridge_B_rel_bias_original]
      rfl
    rw[heq_fun]
    intro ε hε
    have h_lim := h_bias ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
    · filter_upwards with T; exact zero_le _
    · filter_upwards with T
      have h_set : {ω | ε ≤ edist (bias_original d43.pd T ω - B_FP_sq_test
                   d43.pd.Sigma_F d43.pd.Omega_rel d43.pd.Lambda_rel d43.pd.lambda_0) 0} =
                   {ω | ε ≤ edist (bias_original d43.pd T ω) (B_FP_sq_test
                   d43.pd.Sigma_F d43.pd.Omega_rel d43.pd.Lambda_rel d43.pd.lambda_0)} := by
        ext ω
        simp only[edist_dist, Real.dist_eq, sub_zero, Set.mem_setOf_eq]
      rw [h_set]
  have h_term1 := tendstoInMeasure_squeeze_le_one d43.pd.μ h_B_diff (fun T ω => by
    rw[abs_of_nonneg (M_FP_nonneg (d43.d_seq T ω) (d43.h_B_ne_zero T ω))]
    exact M_FP_le_one (d43.d_seq T ω) (d43.h_B_ne_zero T ω))
  -- Term 2: (T⁻¹‖d‖² − δ²) · M_δ
  -- oₚ(1) × [0,1] = oₚ(1)  since M_δ ∈ [0,1]
  have h_d_diff : TendstoInMeasure d43.pd.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ *
    sqNorm (d_vec (d43.d_seq T ω)) - d43.delta_sq) atTop (fun _ => 0) := by
    intro ε hε
    have h_lim := derived_d_vec_lim d43 ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
    · filter_upwards with T; exact zero_le _
    · filter_upwards with T
      have heq_set : {ω | ε ≤ edist ((T : ℝ)⁻¹ * sqNorm (d_vec (d43.d_seq T ω))
                     - d43.delta_sq) 0} = {ω | ε ≤ edist ((T : ℝ)⁻¹ * sqNorm
                     (d_vec (d43.d_seq T ω))) d43.delta_sq} := by
        ext ω
        simp only[edist_dist, Real.dist_eq, sub_zero, Set.mem_setOf_eq]
      rw[heq_set]
  have h_term2 := tendstoInMeasure_squeeze_le_one d43.pd.μ h_d_diff (fun T ω => by
    rw[abs_of_nonneg (M_delta_nonneg (d43.d_seq T ω) (d43.h_d_ne_zero T ω))]
    exact M_delta_le_one (d43.d_seq T ω) (d43.h_d_ne_zero T ω))
  -- Step 3: Combine all 6 vanishing terms via repeated addition
  have h_final := tendstoInMeasure_add_zero d43.pd.μ
                    (tendstoInMeasure_add_zero d43.pd.μ
                      (tendstoInMeasure_add_zero d43.pd.μ
                        (tendstoInMeasure_add_zero d43.pd.μ
                          (tendstoInMeasure_add_zero d43.pd.μ h_term1 h_term2)
                          (derive_h_e_trace d43))                            -- Term 3: noise trace
                        (cross_term_1_vanishes d43 h_violation_absorption))  -- Term 4
                      (cross_term_2_vanishes d43))                           -- Term 5
                    (cross_term_3_vanishes d43)                              -- Term 6
  -- Step 4: Unfold d_seq to match h_final's form to h_alg's rearrangement
  have h_eq_fun : (fun (T : ℕ) ω =>
      (T : ℝ)⁻¹ * sqNorm (residual_vec (d43.d_seq T ω)) -
      (B_FP_sq_val d43 * M_FP (d43.d_seq T ω) +
       d43.delta_sq * M_delta (d43.d_seq T ω) +
       d43.sigma_sq * (1 - (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ))))) =
    (fun (T : ℕ) ω =>
      ((T : ℝ)⁻¹ * sqNorm (B_rel (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω)) -
      B_FP_sq_val d43) * M_FP (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω) +
      ((T : ℝ)⁻¹ * sqNorm (d_vec (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω)) -
      d43.delta_sq) * M_delta (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω) +
      ((T : ℝ)⁻¹ * sqNorm (annihilator (U_mat (mk_Lemma42_Data d43.pd d43.X_irrel
      d43.delta_det T ω)) * e_vec (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω)) -
      d43.sigma_sq * (1 - (Matrix.rank (U_mat (mk_Lemma42_Data d43.pd d43.X_irrel
      d43.delta_det T ω)) : ℝ) / ((T : ℝ) - (r : ℝ)))) +
      (T : ℝ)⁻¹ * (2 * ((B_rel (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω))ᵀ *
      (annihilator (U_mat (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω)) *
      d_vec (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω))) 0 0) +
      (T : ℝ)⁻¹ * (2 * ((B_rel (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω))ᵀ *
      (annihilator (U_mat (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω)) *
      e_vec (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω))) 0 0) +
      (T : ℝ)⁻¹ * (2 * ((d_vec (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω))ᵀ *
      (annihilator (U_mat (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω)) *
      e_vec (mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω))) 0 0)) := by
    funext T ω
    have h_unfold : mk_Lemma42_Data d43.pd d43.X_irrel d43.delta_det T ω = d43.d_seq T ω := rfl
    rw [h_unfold, h_alg T ω]
  rw[h_eq_fun]
  exact h_final

end Theorem43

-- ═══════════════════════════════════════════════════════════════════════════════
-- PART III: COROLLARY 4.4 — Differential Masking and the Spurious Fit Trap
-- (Manuscript §4.4, Corollary 4.4)
--
-- Under Assumption 4.1 (geometric alignment of structural violations):
--   (i)   M_δ →ₚ 0                        — the violation is masked
--   (ii)  M_FP ≥ 1 − κ + oₚ(1)            — the bias survives
--   (iii) T⁻¹‖r‖² →ₚ B²_FP·M_FP + σ²(1−κ) — the δ² term has vanished
--
-- "Pre-treatment fit diagnostics based on residual variance are therefore
--  asymptotically uninformative about the magnitude of the structural
--  identification failure."  — Manuscript, Corollary 4.4(iii)
-- ═══════════════════════════════════════════════════════════════════════════════

section Corollary44

open Filter Topology Lemma42

variable {r N_rel N_irrel : ℕ} {Ω : Type*} [MeasurableSpace Ω]

-- ──────────────────────────────────────────────────────────────────────────
-- Assumption 4.1 (Geometric Alignment of Structural Violations)
-- (Manuscript §4.4)
--
-- This is the core economic content: irrelevant donors selectively absorb
-- the structural violation while leaving the matching bias intact.
--
-- (i) Violation absorption: M_δ →ₚ 0
--     "sin²θ → 0: d is asymptotically absorbed by 𝒰"
--
-- (ii) Bias survival: P_𝒰B_rel/‖B_rel‖² ≤ κ + oₚ(1)
--      "B_rel is not preferentially spanned by 𝒰"
--      This gives M_FP = 1 − cos²θ_B ≥ 1 − κ + oₚ(1)
-- ──────────────────────────────────────────────────────────────────────────

/--
Assumption 4.1 (Geometric Alignment of Structural Violations)
Formalizes the differential masking condition: irrelevant donors absorb the structural violation
while the imperfect matching bias remains poorly aligned with the irrelevant subspace.
-/
structure Assumption41_Data {r N_rel N_irrel : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (d43 : Theorem43_Data r N_rel N_irrel Ω) where
  -- Assumption 4.1(i): Violation absorption (M_delta -> 0)
  h_violation_absorption : TendstoInMeasure d43.pd.μ (fun T ω => M_delta (d43.d_seq T ω))
    atTop (fun _ => 0)
  -- Assumption 4.1(ii): Unspanned matching bias (B_rel is not preferentially spanned by U)
  h_U_not_preferential : ∀ᶠ T in Filter.atTop, ∀ ω,
    sqNorm (proj (U_mat (d43.d_seq T ω)) * B_rel (d43.d_seq T ω)) / sqNorm (B_rel (d43.d_seq T ω))
    ≤ (Matrix.rank (U_mat (d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ))

structure Corollary44_Data (r N_rel N_irrel : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  d43 : Theorem43_Data r N_rel N_irrel Ω
  a41 : Assumption41_Data d43
  h_delta_pos : 0 < d43.delta_sq  -- δ² > 0: a genuine structural violation exists

variable (cd44 : Corollary44_Data r N_rel N_irrel Ω)

-- ──────────────────────────────────────────────────────────────────────────
-- Corollary 4.4(i): Violation masking
--   M_{δ,T₀} →ₚ 0
--
-- "The structural violation δ leaves no asymptotic trace in the
--  normalized residual." — Manuscript, Corollary 4.4(i)
--
-- This is a direct restatement of Assumption 4.1(i).
-- ──────────────────────────────────────────────────────────────────────────

lemma corollary_4_4_i :
    TendstoInMeasure cd44.d43.pd.μ (fun (T : ℕ) ω => M_delta (cd44.d43.d_seq T ω))
      atTop (fun _ => 0) :=
  cd44.a41.h_violation_absorption

-- Helper: κ_{T₀} = s/(T−r) →ₚ κ  (deterministic rank saturation)
lemma derived_h_kappa_lim (cd44 : Corollary44_Data r N_rel N_irrel Ω) :
    TendstoInMeasure cd44.d43.pd.μ (fun T ω => (Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) /
      ((T : ℝ) - (r : ℝ))) atTop (fun _ => cd44.d43.rsd.kappa) := by
  have h_det_lim : Tendsto (fun T => (cd44.d43.rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ)))
    atTop (nhds cd44.d43.rsd.kappa) := cd44.d43.rsd.h_kappa_lim
  have h_meas := deterministic_tendstoInMeasure cd44.d43.pd.μ h_det_lim
  have h_fun_eq : (fun T ω => (Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) /
                  ((T : ℝ) - (r : ℝ))) = (fun T ω => (cd44.d43.rsd.s T : ℝ) /
                  ((T : ℝ) - (r : ℝ))) := by
    funext T ω
    have hr : Matrix.rank (U_mat (cd44.d43.d_seq T ω)) = cd44.d43.rsd.s T :=
      cd44.d43.h_rank_eq T ω
    rw [hr]
  rw[h_fun_eq]
  exact h_meas

-- ──────────────────────────────────────────────────────────────────────────
-- Corollary 4.4(ii): Imperfect-matching survival
--   M_{FP,T₀} ≥ 1 − κ + oₚ(1)
--
-- Manuscript p.9–10: "B_rel, being a projection residual already orthogonal
-- to the dominant factor directions, remains poorly aligned with 𝒰 and
-- retains at least the baseline fraction 1 − κ of its energy outside 𝒰."
--
-- Formally: max(0, (1−κ) − M_FP) →ₚ 0, meaning M_FP eventually exceeds 1−κ.
-- ──────────────────────────────────────────────────────────────────────────

lemma corollary_4_4_ii :
    TendstoInMeasure cd44.d43.pd.μ
      (fun (T : ℕ) ω => max 0 ((1 - cd44.d43.rsd.kappa) - M_FP (cd44.d43.d_seq T ω)))
      atTop (fun _ => 0) := by
  -- |κ_{T₀} − κ| →ₚ 0 (deterministic convergence of rank ratio)
  have h_abs_kappa := tendstoInMeasure_abs_sub cd44.d43.pd.μ (derived_h_kappa_lim cd44)
  -- By Assumption 4.1(ii): (1−κ) − M_FP ≤ κ_{T₀} − κ
  -- (since cos²θ_B ≤ κ_{T₀}, we get M_FP = 1 − cos²θ_B ≥ 1 − κ_{T₀})
  have hbound : ∀ᶠ T in atTop, ∀ ω,
      max 0 ((1 - cd44.d43.rsd.kappa) - M_FP (cd44.d43.d_seq T ω)) ≤
      |(Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ)) -
      cd44.d43.rsd.kappa| := by
    filter_upwards[cd44.a41.h_U_not_preferential] with T hT ω
    have h_step : (1 - cd44.d43.rsd.kappa) - M_FP (cd44.d43.d_seq T ω) ≤
        (Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ)) -
        cd44.d43.rsd.kappa := by
      rw[M_FP_eq_one_sub_cos_sq (cd44.d43.d_seq T ω) (cd44.d43.h_B_ne_zero T ω)]
      linarith [hT ω]
    exact max_le (abs_nonneg _) (le_trans h_step (le_abs_self _))
  -- Squeeze: max(0, ...) ≤ |κ_T − κ| →ₚ 0
  exact tendstoInMeasure_eventually_dominated cd44.d43.pd.μ
    (fun T ω => le_max_left 0 _)
    (fun T ω => abs_nonneg _)
    hbound
    h_abs_kappa

-- ──────────────────────────────────────────────────────────────────────────
-- Corollary 4.4(iii): Asymptotic residual — the δ² term has vanished
--
-- Manuscript p.9: "The normalized squared residual satisfies
--   T⁻¹‖r‖² →ₚ B²_FP · M_FP + σ²(1−κ) + oₚ(1)
-- where the δ² term has vanished despite δ² > 0."
--
-- This is the formal statement of the spurious fit trap:
-- the pre-treatment residual contains NO information about the structural
-- violation δ, even though a genuine violation exists (δ² > 0).
-- ──────────────────────────────────────────────────────────────────────────

lemma corollary_4_4_iii :
    TendstoInMeasure cd44.d43.pd.μ (fun (T : ℕ) ω =>
      (T : ℝ)⁻¹ * sqNorm (residual_vec (cd44.d43.d_seq T ω)) -
      (B_FP_sq_val cd44.d43 * M_FP (cd44.d43.d_seq T ω) +
       cd44.d43.sigma_sq * (1 - cd44.d43.rsd.kappa))
    ) atTop (fun _ => 0) := by
  -- Telescope: (LHS − B²M_FP − σ²(1−κ))
  --   = (LHS − B²M_FP − δ²M_δ − σ²(1−κ_T))     ← Theorem 4.3 residual
  --   + δ²M_δ                                  ← vanishes since M_δ →ₚ 0
  --   + σ²(κ − κ_T)                            ← vanishes since κ_T → κ
  have h_alg : ∀ (T : ℕ) ω,
      (T : ℝ)⁻¹ * sqNorm (residual_vec (cd44.d43.d_seq T ω)) -
      (B_FP_sq_val cd44.d43 * M_FP (cd44.d43.d_seq T ω) +
       cd44.d43.sigma_sq * (1 - cd44.d43.rsd.kappa))
      =
      ((T : ℝ)⁻¹ * sqNorm (residual_vec (cd44.d43.d_seq T ω)) -
        (B_FP_sq_val cd44.d43 * M_FP (cd44.d43.d_seq T ω) +
         cd44.d43.delta_sq * M_delta (cd44.d43.d_seq T ω) +
         cd44.d43.sigma_sq * (1 - (Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) /
         ((T : ℝ) - (r : ℝ))))) +
      cd44.d43.delta_sq * M_delta (cd44.d43.d_seq T ω) +
      cd44.d43.sigma_sq * (cd44.d43.rsd.kappa - (Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) /
      ((T : ℝ) - (r : ℝ))) := by
    intro T ω
    ring
  -- Piece 1: Theorem 4.3 residual → 0
  have h_thm43 := theorem_4_3 cd44.d43 cd44.a41.h_violation_absorption
  -- Piece 2: δ²·M_δ → δ²·0 = 0  (M_δ →ₚ 0 by Assumption 4.1(i))
  have h_delta_term := tendstoInMeasure_mul_const_zero cd44.d43.pd.μ
    cd44.a41.h_violation_absorption cd44.d43.delta_sq
  -- Piece 3: σ²(κ − κ_T) → σ²·0 = 0  (κ_T → κ by Assumption 2.1)
  have h_kappa_diff : TendstoInMeasure cd44.d43.pd.μ (fun T ω => cd44.d43.rsd.kappa -
    (Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ))) atTop (fun _ => 0) := by
    intro ε hε
    have h_lim := derived_h_kappa_lim cd44 ε hε
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
    · filter_upwards with T; exact zero_le _
    · filter_upwards with T
      have heq_set : {ω | ε ≤ edist (cd44.d43.rsd.kappa - (Matrix.rank (U_mat
                     (cd44.d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ))) 0} =
                     {ω | ε ≤ edist ((Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) /
                     ((T : ℝ) - (r : ℝ))) cd44.d43.rsd.kappa} := by
        ext ω
        simp only[edist_dist, Real.dist_eq, sub_zero, Set.mem_setOf_eq]
        rw[abs_sub_comm]
      rw [heq_set]
  have h_kappa_term := tendstoInMeasure_mul_const_zero cd44.d43.pd.μ h_kappa_diff cd44.d43.sigma_sq
  -- Sum the three pieces
  have h_final := tendstoInMeasure_add_zero cd44.d43.pd.μ
                    (tendstoInMeasure_add_zero cd44.d43.pd.μ h_thm43 h_delta_term)
                    h_kappa_term
  -- Bridge to the telescoped form via h_alg
  intro ε hε
  have h_lim := h_final ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T
    have heq_set : {ω | ε ≤ edist ((T : ℝ)⁻¹ * sqNorm (residual_vec (cd44.d43.d_seq T ω)) -
                   (B_FP_sq_val cd44.d43 * M_FP (cd44.d43.d_seq T ω) + cd44.d43.sigma_sq *
                   (1 - cd44.d43.rsd.kappa))) 0} = {ω | ε ≤ edist (((T : ℝ)⁻¹ * sqNorm
                   (residual_vec (cd44.d43.d_seq T ω)) - (B_FP_sq_val cd44.d43 * M_FP
                   (cd44.d43.d_seq T ω) + cd44.d43.delta_sq * M_delta (cd44.d43.d_seq T ω) +
                   cd44.d43.sigma_sq * (1 - (Matrix.rank (U_mat (cd44.d43.d_seq T ω)) : ℝ) /
                   ((T : ℝ) - (r : ℝ))))) + cd44.d43.delta_sq * M_delta (cd44.d43.d_seq T ω) +
                   cd44.d43.sigma_sq * (cd44.d43.rsd.kappa - (Matrix.rank (U_mat
                   (cd44.d43.d_seq T ω)) : ℝ) / ((T : ℝ) - (r : ℝ)))) 0} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw[← h_alg T ω]
    rw [heq_set]

end Corollary44
