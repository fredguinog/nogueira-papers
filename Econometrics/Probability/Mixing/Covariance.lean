/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Econometrics.Probability.Mixing.Alpha

/-!
# Analytic Inequalities for α-Mixing Processes

This file collects the analytic lemmas that underlie Davidson's covariance inequality
(Theorem 14.1 in *Stochastic Limit Theory*). The main result is
`ProbabilityTheory.cov_bound_alphaMixing`, which bounds the covariance of two bounded
measurable functions by four times the appropriate α-mixing coefficient.

## Main results

* `ProbabilityTheory.integrable_of_bounded_one` : a measurable function bounded in
  absolute value by `1` is integrable against any finite measure.
* `ProbabilityTheory.alphaMixingValues_bddAbove` : `alphaMixingValues μ S1 S2` is
  bounded above by `1` when `μ` is a probability measure.
* `ProbabilityTheory.cov_bound_indicator` : for measurable indicator events the
  mixing coefficient upper-bounds `|μ(A ∩ B) − μ(A)μ(B)|`.
* `ProbabilityTheory.cov_affineReduction` : the affine change of variables
  `f = 2f₀ − 1` pulls a factor of `4` out of the covariance.
* `ProbabilityTheory.cov_bound_alphaMixing` : **Davidson Theorem 14.1** — for
  functions bounded by `1`, `|Cov(f, g)| ≤ 4 α`.

## References

* Davidson, J. (1994). *Stochastic Limit Theory*, Theorem 14.1. Oxford University Press.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]

/-! ### Basic integrability infrastructure -/

/-- A measurable function whose absolute value is everywhere at most `1` is integrable
against any finite measure. -/
lemma integrable_of_bounded_one (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf_meas : Measurable f) (h_bound : ∀ ω, |f ω| ≤ 1) :
    Integrable f μ := by
  have h_int_const : Integrable (fun _ => (1 : ℝ)) μ := integrable_const 1
  apply h_int_const.mono hf_meas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  have h : ‖f ω‖ = |f ω| := rfl
  rw [h]
  have h1 : ‖(1 : ℝ)‖ = 1 := by norm_num
  rw [h1]
  exact h_bound ω

/-! ### Mixing coefficient upper bounds -/

/-- In a probability space, `alphaMixingValues μ S1 S2` is bounded above by `1`,
since all probabilities lie in `[0, 1]`. -/
lemma alphaMixingValues_bddAbove (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S1 S2 : Set (Set Ω)) :
    BddAbove (alphaMixingValues μ S1 S2) := by
  use 1
  rintro x ⟨A, B, -, -, rfl⟩
  have hA : (μ A).toReal ≤ 1 := by
    have h1 : μ A ≤ μ Set.univ := measure_mono (Set.subset_univ A)
    rw [measure_univ] at h1
    have h2 : (μ A).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h1
    rw [ENNReal.toReal_one] at h2; exact h2
  have hB : (μ B).toReal ≤ 1 := by
    have h1 : μ B ≤ μ Set.univ := measure_mono (Set.subset_univ B)
    rw [measure_univ] at h1
    have h2 : (μ B).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h1
    rw [ENNReal.toReal_one] at h2; exact h2
  have hAB : (μ (A ∩ B)).toReal ≤ 1 := by
    have h1 : μ (A ∩ B) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [measure_univ] at h1
    have h2 : (μ (A ∩ B)).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top h1
    rw [ENNReal.toReal_one] at h2; exact h2
  have hA_pos  : 0 ≤ (μ A).toReal      := ENNReal.toReal_nonneg
  have hB_pos  : 0 ≤ (μ B).toReal      := ENNReal.toReal_nonneg
  have hAB_pos : 0 ≤ (μ (A ∩ B)).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> nlinarith

/-- For any two events `A ∈ S1` and `B ∈ S2`, the absolute difference between their
joint and product probabilities is at most the α-mixing coefficient. -/
lemma cov_bound_indicator (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S1 S2 : Set (Set Ω)) {A B : Set Ω}
    (hA : A ∈ S1) (hB : B ∈ S2) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ alphaMixingCoeff μ S1 S2 := by
  unfold alphaMixingCoeff alphaMixingValues
  apply le_csSup
  · exact alphaMixingValues_bddAbove μ S1 S2
  · simp only [Set.mem_setOf_eq]
    exact ⟨A, B, hA, hB, rfl⟩

/-! ### Affine reduction of the covariance -/

/-- **Affine reduction lemma.** If `f = 2f₀ − 1` and `g = 2g₀ − 1`, then
`Cov(f, g) = 4 · Cov(f₀, g₀)`.

This allows the covariance bound for functions in `[-1, 1]` to be reduced to the
easier case of functions in `[0, 1]`. -/
lemma cov_affineReduction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f₀ g₀ : Ω → ℝ)
    (hf_int : Integrable f₀ μ)
    (hg_int : Integrable g₀ μ)
    (hfg_int : Integrable (fun ω => f₀ ω * g₀ ω) μ) :
    (∫ ω, (2 * f₀ ω - 1) * (2 * g₀ ω - 1) ∂μ) -
    (∫ ω, (2 * f₀ ω - 1) ∂μ) * (∫ ω, (2 * g₀ ω - 1) ∂μ) =
    4 * (∫ ω, f₀ ω * g₀ ω ∂μ - (∫ ω, f₀ ω ∂μ) * (∫ ω, g₀ ω ∂μ)) := by
  have h_fg_expand :
      (fun ω => (2 * f₀ ω - 1) * (2 * g₀ ω - 1)) =
      (fun ω => 4 * (f₀ ω * g₀ ω) - 2 * f₀ ω - 2 * g₀ ω + 1) := by ext ω; ring
  rw [h_fg_expand]
  have h2f  : Integrable (fun ω => 2 * f₀ ω) μ              := hf_int.const_mul 2
  have h2g  : Integrable (fun ω => 2 * g₀ ω) μ              := hg_int.const_mul 2
  have h4fg : Integrable (fun ω => 4 * (f₀ ω * g₀ ω)) μ    := hfg_int.const_mul 4
  have h1   : Integrable (fun ω => (1 : ℝ)) μ               := integrable_const 1
  have h_int_f : ∫ ω, (2 * f₀ ω - 1) ∂μ = 2 * (∫ ω, f₀ ω ∂μ) - 1 := by
    rw [integral_sub h2f h1, integral_const_mul, integral_const]; simp
  have h_int_g : ∫ ω, (2 * g₀ ω - 1) ∂μ = 2 * (∫ ω, g₀ ω ∂μ) - 1 := by
    rw [integral_sub h2g h1, integral_const_mul, integral_const]; simp
  have h_int_fg :
      ∫ ω, 4 * (f₀ ω * g₀ ω) - 2 * f₀ ω - 2 * g₀ ω + 1 ∂μ =
      4 * (∫ ω, f₀ ω * g₀ ω ∂μ) - 2 * (∫ ω, f₀ ω ∂μ) - 2 * (∫ ω, g₀ ω ∂μ) + 1 := by
    have hA : Integrable (fun ω => 4 * (f₀ ω * g₀ ω) - 2 * f₀ ω) μ           := h4fg.sub h2f
    have hB : Integrable (fun ω => 4 * (f₀ ω * g₀ ω) - 2 * f₀ ω - 2 * g₀ ω) μ := hA.sub h2g
    rw [integral_add hB h1, integral_sub hA h2g, integral_sub h4fg h2f,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
    simp
  rw [h_int_f, h_int_g, h_int_fg]; ring

end ProbabilityTheory
