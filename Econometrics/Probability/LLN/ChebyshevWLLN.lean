/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.Probability.LpConvergence
import Econometrics.Probability.Mixing.Asymptotics

/-!
# Chebyshev Weak Law of Large Numbers

This file proves the WLLN for mutually orthogonal sequences with bounded
variances, showing that the sample mean converges to zero in L².

## Main definitions

* `ProbabilityTheory.OrthogonalSequence` : mutual orthogonality in L².

## Main results

* `wlln_orthogonalSequence` : `E[(T⁻¹ Σ Xₜ)²] → 0` under orthogonality.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace ProbabilityTheory

/--
Phase 3.1: Definition of Cross-Sectional Orthogonality.
A sequence of random variables is mutually orthogonal in L2 if their cross-moments are zero.
-/
def OrthogonalSequence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∫ ω, X i ω * X j ω ∂μ = 0

/--
Phase 3.2: Heterogeneous Chebyshev WLLN.
If a sequence is mutually orthogonal with bounded variances, its sample mean converges to 0 in L2.
This proves that the cross-sectional noise perfectly annihilates cross terms without requiring
    mixing.
-/
theorem wlln_orthogonalSequence {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_L2 : ∀ t, MemLp (X t) 2 μ)
    (h_orth : OrthogonalSequence μ X)
    (V : ℝ)
    (h_var : ∀ t, ∫ ω, (X t ω) ^ 2 ∂μ ≤ V) :
    Tendsto (fun (T : ℕ) => ∫ ω, ((T : ℝ)⁻¹ * ∑ t : Fin T, X t.val ω)^2 ∂μ) atTop (nhds 0) := by
  -- 1. Expand the squared sum and annihilate the off-diagonal terms using orthogonality
  have h_sum_bound : ∀ T : ℕ, (∑ s : Fin T, ∑ t : Fin T, ∫ ω, X s.val ω * X t.val ω ∂μ) ≤
      (T : ℝ) * V := by
    intro T
    have h_double_sum : (∑ s : Fin T, ∑ t : Fin T, ∫ ω, X s.val ω * X t.val ω ∂μ) =
                        ∑ s : Fin T, ∫ ω, X s.val ω * X s.val ω ∂μ := by
      apply Finset.sum_congr rfl
      intro s _
      have h_split : (∑ t : Fin T, ∫ ω, X s.val ω * X t.val ω ∂μ) =
                     (∑ t ∈ Finset.univ.filter (fun t => s = t), ∫ ω, X s.val ω * X t.val ω ∂μ) +
                     (∑ t ∈ Finset.univ.filter (fun t => s ≠ t), ∫ ω, X s.val ω * X t.val ω ∂μ) :=
                         by
        exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun t : Fin T => s = t)
          (fun t => ∫ ω, X s.val ω * X t.val ω ∂μ)).symm
      have h_diag : (∑ t ∈ Finset.univ.filter (fun t => s = t), ∫ ω, X s.val ω * X t.val ω ∂μ) =
                    ∫ ω, X s.val ω * X s.val ω ∂μ := by
        have h_eq : Finset.univ.filter (fun t => s = t) = {s} := by
          ext t; simp [eq_comm]
        rw [h_eq, Finset.sum_singleton]
      have h_off : (∑ t ∈ Finset.univ.filter (fun t => s ≠ t), ∫ ω, X s.val ω * X t.val ω ∂μ) =
          0 := by
        apply Finset.sum_eq_zero
        intro t ht
        rw [Finset.mem_filter] at ht
        have h_neq : s.val ≠ t.val := fun h => ht.2 (Fin.ext h)
        exact h_orth s.val t.val h_neq
      rw [h_split, h_diag, h_off, add_zero]
    rw [h_double_sum]
    -- 2. Bound the remaining diagonal (variance) terms
    calc ∑ s : Fin T, ∫ ω, X s.val ω * X s.val ω ∂μ
      _ = ∑ s : Fin T, ∫ ω, (X s.val ω)^2 ∂μ := by
          apply Finset.sum_congr rfl
          intro s _
          congr 1; ext ω; ring
      _ ≤ ∑ s : Fin T, V := Finset.sum_le_sum (fun s _ => h_var s.val)
      _ = (T : ℝ) * V := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- 3. Evaluate the asymptotic limit: T * V / T^2 = V / T -> 0
  have h_lim : Tendsto (fun (T : ℕ) => (T : ℝ)⁻¹^2 * ((T : ℝ) * V)) atTop (nhds 0) := by
    have h_eq : (fun (T : ℕ) => (T : ℝ)⁻¹^2 * ((T : ℝ) * V)) =ᶠ[atTop] (fun T => V * (T : ℝ)⁻¹) :=
        by
      filter_upwards [eventually_ne_atTop 0] with T hT
      have hT_real : (T : ℝ) ≠ 0 := by exact_mod_cast hT
      calc (T : ℝ)⁻¹^2 * ((T : ℝ) * V)
        _ = ((T : ℝ)⁻¹ * (T : ℝ)⁻¹) * (T : ℝ) * V := by ring
        _ = (T : ℝ)⁻¹ * ((T : ℝ)⁻¹ * (T : ℝ)) * V := by ring
        _ = (T : ℝ)⁻¹ * 1 * V := by rw [inv_mul_cancel₀ hT_real]
        _ = V * (T : ℝ)⁻¹ := by ring
    have h_zero : Tendsto (fun T : ℕ => V * (T : ℝ)⁻¹) atTop (nhds 0) := by
      have h := Tendsto.const_mul V (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
      simp only [mul_zero] at h
      exact h
    exact Tendsto.congr' h_eq.symm h_zero
  -- 4. Apply Squeeze Theorem using our variance expansion lemma from Asymptotics.lean
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_lim
  · filter_upwards with T; apply integral_nonneg; intro ω; exact sq_nonneg _
  · filter_upwards with T
    rw [ProbabilityTheory.variance_expansion μ X T h_L2]
    have h_pos : 0 ≤ (T : ℝ)⁻¹^2 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left (h_sum_bound T) h_pos

end ProbabilityTheory
