/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.Probability.ConditionalMixing

/-!
# Quadratic Form Bounds for Mixing Processes

This file provides the algebraic machinery for bounding double sums of the form
`∑ᵢ ∑ⱼ Cᵢⱼ Eᵢⱼ` using AM–GM and row-sum bounds, and constructs a
`CondMixingBound` from uncorrelated block structure.

## Main results

* `doubleSum_mul_le_rowSum_bound` : `|∑∑ C·E| ≤ M · tr(C)`.
* `CondMixingBound.ofUncorrelatedBlocks` : construction from moment conditions.
-/

open MeasureTheory Filter Topology ProbabilityTheory Matrix

namespace ProbabilityTheory

/-! ### 1. Basic AM-GM Inequality -/
lemma abs_mul_le_half_add_sq (x y : ℝ) : |x * y| ≤ (x^2 + y^2) / 2 := by
  have h1 : 0 ≤ (x - y)^2 := sq_nonneg _
  have h2 : 0 ≤ (x + y)^2 := sq_nonneg _
  have h3 : |x * y| = x * y ∨ |x * y| = -(x * y) := abs_choice _
  rcases h3 with h | h
  · rw [h]; linarith
  · rw [h]; linarith

/-! ### 2. Main Algebraic Bound for Quadratic Forms -/
lemma doubleSum_mul_le_rowSum_bound {T : ℕ} (C_mat E_mat : Fin T → Fin T → ℝ)
    (hE_symm : ∀ i j, E_mat i j = E_mat j i)
    (M : ℝ)
    (h_row_sum : ∀ i, ∑ j : Fin T, |E_mat i j| ≤ M)
    (hC_amgm : ∀ i j, |C_mat i j| ≤ (C_mat i i + C_mat j j) / 2)
    (hC_pos : ∀ i, 0 ≤ C_mat i i) :
    |∑ i : Fin T, ∑ j : Fin T, C_mat i j * E_mat i j| ≤ M * ∑ i : Fin T, C_mat i i := by
  have h_abs : |∑ i : Fin T, ∑ j : Fin T, C_mat i j * E_mat i j| ≤
      ∑ i : Fin T, ∑ j : Fin T, |C_mat i j| * |E_mat i j| := by
    calc |∑ i, ∑ j, C_mat i j * E_mat i j|
      _ ≤ ∑ i, |∑ j, C_mat i j * E_mat i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |C_mat i j * E_mat i j| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i, ∑ j, |C_mat i j| * |E_mat i j| := by simp_rw [abs_mul]
  have h_le : (∑ i : Fin T, ∑ j : Fin T, |C_mat i j| * |E_mat i j|) ≤
      ∑ i : Fin T, ∑ j : Fin T, ((C_mat i i + C_mat j j) / 2) * |E_mat i j| := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact mul_le_mul_of_nonneg_right (hC_amgm i j) (abs_nonneg _)
  have h_split : (∑ i : Fin T, ∑ j : Fin T, ((C_mat i i + C_mat j j) / 2) * |E_mat i j|) =
      (1/2 : ℝ) * (∑ i : Fin T, C_mat i i * ∑ j : Fin T, |E_mat i j|) +
      (1/2 : ℝ) * (∑ j : Fin T, C_mat j j * ∑ i : Fin T, |E_mat i j|) := by
    calc (∑ i, ∑ j, ((C_mat i i + C_mat j j) / 2) * |E_mat i j|)
      _ = ∑ i, ∑ j, ((1/2 : ℝ) * C_mat i i * |E_mat i j| + (1/2 : ℝ) * C_mat j j * |E_mat i j|) :=
          by
          apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
      _ =
          (∑ i, ∑ j, (1/2 : ℝ) * C_mat i i * |E_mat i j|) + (∑ i, ∑ j,
              (1/2 : ℝ) * C_mat j j * |E_mat i j|) := by
          have h_add : ∀ i, (∑ j,
              ((1/2 : ℝ) * C_mat i i * |E_mat i j| + (1/2 : ℝ) * C_mat j j * |E_mat i j|)) =
                            (∑ j, (1/2 : ℝ) * C_mat i i * |E_mat i j|) + (∑ j,
                                (1/2 : ℝ) * C_mat j j * |E_mat i j|) := by
            intro i; rw [Finset.sum_add_distrib]
          simp_rw [h_add, Finset.sum_add_distrib]
      _ =
          (1/2 : ℝ) * (∑ i, C_mat i i * ∑ j, |E_mat i j|) + (1/2 : ℝ) * (∑ j, C_mat j j * ∑ i,
              |E_mat i j|) := by
          congr 1
          · simp_rw [mul_assoc, ← Finset.mul_sum]
          · rw [Finset.sum_comm]; simp_rw [mul_assoc, ← Finset.mul_sum]
  have h_bound1 : (∑ i : Fin T, C_mat i i * ∑ j : Fin T, |E_mat i j|) ≤
      ∑ i : Fin T, C_mat i i * M := by
    apply Finset.sum_le_sum; intro i _
    exact mul_le_mul_of_nonneg_left (h_row_sum i) (hC_pos i)
  have h_bound2 : (∑ j : Fin T, C_mat j j * ∑ i : Fin T, |E_mat i j|) ≤
      ∑ j : Fin T, C_mat j j * M := by
    apply Finset.sum_le_sum; intro j _
    have h_col_sum : (∑ i : Fin T, |E_mat i j|) ≤ M := by
      have heq : (∑ i : Fin T, |E_mat i j|) = ∑ i : Fin T, |E_mat j i| := by
        apply Finset.sum_congr rfl; intro i _; rw [hE_symm]
      rw [heq]; exact h_row_sum j
    exact mul_le_mul_of_nonneg_left h_col_sum (hC_pos j)
  calc |∑ i : Fin T, ∑ j : Fin T, C_mat i j * E_mat i j|
    _ ≤ ∑ i : Fin T, ∑ j : Fin T, ((C_mat i i + C_mat j j) / 2) * |E_mat i j| := le_trans h_abs h_le
    _ = (1/2 : ℝ) * (∑ i : Fin T, C_mat i i * ∑ j : Fin T, |E_mat i j|) +
        (1/2 : ℝ) * (∑ j : Fin T, C_mat j j * ∑ i : Fin T, |E_mat i j|) := h_split
    _ ≤ (1/2 : ℝ) * (∑ i : Fin T, C_mat i i * M) +
        (1/2 : ℝ) * (∑ j : Fin T, C_mat j j * M) :=
            add_le_add (mul_le_mul_of_nonneg_left h_bound1 (by norm_num))
                (mul_le_mul_of_nonneg_left h_bound2 (by norm_num))
    _ = M * ∑ i : Fin T, C_mat i i := by
        calc (1/2 : ℝ) * (∑ i : Fin T, C_mat i i * M) + (1/2 : ℝ) * (∑ j : Fin T, C_mat j j * M)
          _ = M * ∑ i : Fin T, C_mat i i := by
              simp_rw [← Finset.sum_mul]; ring

/-! ### 3. Construct the actual CondMixingBound using the uncoupled moments -/
def CondMixingBound.ofUncorrelatedBlocks {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c e : (T : ℕ) → Ω → Matrix (Fin T) (Fin 1) ℝ)
    (M : ℝ) (hM_pos : 0 < M)
    (h_uncorr : ∀ T i j, ∫ ω, c T ω i 0 * c T ω j 0 * (e T ω i 0 * e T ω j 0) ∂μ =
                         (∫ ω, c T ω i 0 * c T ω j 0 ∂μ) * (∫ ω, e T ω i 0 * e T ω j 0 ∂μ))
    (h_e_symm : ∀ T i j, ∫ ω, e T ω i 0 * e T ω j 0 ∂μ = ∫ ω, e T ω j 0 * e T ω i 0 ∂μ)
    (h_row_sum : ∀ T i, ∑ j : Fin T, |∫ ω, e T ω i 0 * e T ω j 0 ∂μ| ≤ M)
    (hc_int : ∀ T i j, Integrable (fun ω => c T ω i 0 * c T ω j 0) μ)
    (he_int : ∀ T i j, Integrable (fun ω => e T ω i 0 * e T ω j 0) μ)
    (hce_int : ∀ T i j, Integrable (fun ω => c T ω i 0 * c T ω j 0 * (e T ω i 0 * e T ω j 0)) μ) :
    CondMixingBound μ c e := by
    refine ⟨M, hM_pos, fun T => ?_⟩
    have h_LHS : ∫ ω, (((c T ω)ᵀ * e T ω) 0 0)^2 ∂μ =
        ∑ i : Fin T, ∑ j : Fin T, ∫ ω, c T ω i 0 * c T ω j 0 * (e T ω i 0 * e T ω j 0) ∂μ := by
      have h_inner_sq : ∀ ω, (((c T ω)ᵀ * e T ω) 0 0)^2 =
          ∑ i : Fin T, ∑ j : Fin T, c T ω i 0 * c T ω j 0 * (e T ω i 0 * e T ω j 0) := by
        intro ω
        have h_inner : ((c T ω)ᵀ * e T ω) 0 0 = ∑ i : Fin T, c T ω i 0 * e T ω i 0 := by
          simp only [Matrix.mul_apply, Matrix.transpose_apply]
        rw [h_inner, sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring
      have h_eq : (fun ω => (((c T ω)ᵀ * e T ω) 0 0)^2) =
          fun ω => ∑ i : Fin T, ∑ j : Fin T, c T ω i 0 * c T ω j 0 * (e T ω i 0 * e T ω j 0) := by
        funext ω; exact h_inner_sq ω
      rw [h_eq, integral_finset_sum]
      · apply Finset.sum_congr rfl; intro i _
        rw [integral_finset_sum]
        · intro j _; exact hce_int T i j
      · intro i _; apply integrable_finset_sum; intro j _; exact hce_int T i j

    have h_LHS_split : (∑ i : Fin T, ∑ j : Fin T, ∫ ω,
        c T ω i 0 * c T ω j 0 * (e T ω i 0 * e T ω j 0) ∂μ) =
        ∑ i : Fin T, ∑ j : Fin T, (∫ ω, c T ω i 0 * c T ω j 0 ∂μ) * (∫ ω,
            e T ω i 0 * e T ω j 0 ∂μ) := by
      apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
      exact h_uncorr T i j

    rw [h_LHS, h_LHS_split]

    let C_mat := fun i j => ∫ ω, c T ω i 0 * c T ω j 0 ∂μ
    let E_mat := fun i j => ∫ ω, e T ω i 0 * e T ω j 0 ∂μ

    have hC_amgm : ∀ i j, |C_mat i j| ≤ (C_mat i i + C_mat j j) / 2 := by
      intro i j
      calc |∫ ω, c T ω i 0 * c T ω j 0 ∂μ|
        _ ≤ ∫ ω, |c T ω i 0 * c T ω j 0| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ ω, ((c T ω i 0)^2 + (c T ω j 0)^2) / 2 ∂μ := by
            apply integral_mono
            · exact (hc_int T i j).abs
            · have h1 : Integrable (fun ω => (c T ω i 0)^2) μ := by
                have heq : (fun ω => (c T ω i 0)^2) = fun ω => c T ω i 0 * c T ω i 0 :=
                    by funext ω; ring
                rw [heq]; exact hc_int T i i
              have h2 : Integrable (fun ω => (c T ω j 0)^2) μ := by
                have heq : (fun ω => (c T ω j 0)^2) = fun ω => c T ω j 0 * c T ω j 0 :=
                    by funext ω; ring
                rw [heq]; exact hc_int T j j
              exact (h1.add h2).div_const 2
            · intro ω
              exact abs_mul_le_half_add_sq _ _
        _ = (∫ ω, (c T ω i 0)^2 ∂μ + ∫ ω, (c T ω j 0)^2 ∂μ) / 2 := by
            have h1 : Integrable (fun ω => (c T ω i 0)^2) μ := by
              have heq : (fun ω => (c T ω i 0)^2) = fun ω => c T ω i 0 * c T ω i 0 :=
                  by funext ω; ring
              rw [heq]; exact hc_int T i i
            have h2 : Integrable (fun ω => (c T ω j 0)^2) μ := by
              have heq : (fun ω => (c T ω j 0)^2) = fun ω => c T ω j 0 * c T ω j 0 :=
                  by funext ω; ring
              rw [heq]; exact hc_int T j j
            rw [integral_div, integral_add h1 h2]
        _ = (C_mat i i + C_mat j j) / 2 := by
            have h1 : ∫ ω, (c T ω i 0)^2 ∂μ = C_mat i i := by
              dsimp [C_mat]
              have heq : (fun ω => (c T ω i 0)^2) = fun ω => c T ω i 0 * c T ω i 0 :=
                  by funext ω; ring
              rw [heq]
            have h2 : ∫ ω, (c T ω j 0)^2 ∂μ = C_mat j j := by
              dsimp [C_mat]
              have heq : (fun ω => (c T ω j 0)^2) = fun ω => c T ω j 0 * c T ω j 0 :=
                  by funext ω; ring
              rw [heq]
            rw [h1, h2]

    have hC_pos : ∀ i, 0 ≤ C_mat i i := by
      intro i
      dsimp [C_mat]
      have heq : (fun ω => c T ω i 0 * c T ω i 0) = fun ω => (c T ω i 0)^2 := by funext ω; ring
      rw [heq]
      exact integral_nonneg (fun ω => sq_nonneg _)

    have h_abs_bound :=
        doubleSum_mul_le_rowSum_bound C_mat E_mat (h_e_symm T) M (h_row_sum T) hC_amgm hC_pos

    have h_RHS : M * ∫ ω, ((c T ω)ᵀ * c T ω) 0 0 ∂μ = M * ∑ i : Fin T, C_mat i i := by
      have h_inner : ∀ ω, ((c T ω)ᵀ * c T ω) 0 0 = ∑ i : Fin T, (c T ω i 0)^2 := by
        intro ω
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
        apply Finset.sum_congr rfl; intro i _
        ring
      have h_eq : (fun ω => ((c T ω)ᵀ * c T ω) 0 0) = fun ω => ∑ i : Fin T, (c T ω i 0)^2 := by
        funext ω; exact h_inner ω
      rw [h_eq, integral_finset_sum]
      · congr 1
        apply Finset.sum_congr rfl; intro i _
        dsimp [C_mat]
        have heq : (fun ω => (c T ω i 0)^2) = fun ω => c T ω i 0 * c T ω i 0 := by funext ω; ring
        rw [heq]
      · intro i _
        have heq : (fun ω => (c T ω i 0)^2) = fun ω => c T ω i 0 * c T ω i 0 := by funext ω; ring
        rw [heq]; exact hc_int T i i

    calc ∑ i : Fin T, ∑ j : Fin T, C_mat i j * E_mat i j
      _ ≤ |∑ i : Fin T, ∑ j : Fin T, C_mat i j * E_mat i j| := le_abs_self _
      _ ≤ M * ∑ i : Fin T, C_mat i i := h_abs_bound
      _ = M * ∫ ω, ((c T ω)ᵀ * c T ω) 0 0 ∂μ := h_RHS.symm

end ProbabilityTheory
