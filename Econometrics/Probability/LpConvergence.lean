/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# L² Convergence Implies Convergence in Measure

This file proves the Chebyshev/Markov-type implication: if
`E[(fₙ − a)²] → 0` then `fₙ → a` in measure.

## Main results

* `l2_tendstoInMeasure` : L² convergence implies convergence
  in measure.
* `l2_tendstoInMeasure_zero` : specialization to `a = 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace MeasureTheory

/-- **L² convergence implies convergence in measure**
(Chebyshev/Markov). -/
lemma l2_tendstoInMeasure {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ} {a : ℝ}
    (hf : ∀ T, AEStronglyMeasurable (f T) μ)
    (hint : ∀ T,
      Integrable (fun ω => (f T ω - a) ^ 2) μ)
    (h : Tendsto
      (fun T => ∫ ω, (f T ω - a) ^ 2 ∂μ)
      atTop (nhds 0)) :
    TendstoInMeasure μ f atTop (fun _ => a) := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · have hempty : ∀ T,
        {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T ω) a} = ∅ :=
      fun T => Set.eq_empty_of_forall_notMem
        (fun ω hω =>
          (edist_lt_top (f T ω) a).not_ge hω)
    have h_eq : (fun (T : ℕ) =>
        μ {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T ω) a}) = fun _ => 0 := by
      funext T; rw [hempty, measure_empty]
    rw [h_eq]; exact tendsto_const_nhds
  have hε_real : 0 < ε.toReal :=
    ENNReal.toReal_pos hε.ne' hε_top
  have hε2_pos : 0 < ε.toReal ^ 2 :=
    pow_pos hε_real 2
  have hS : ∀ T,
      μ {ω : Ω | ε ≤ edist (f T ω) a} ≤
        ENNReal.ofReal (∫ ω, (f T ω - a) ^ 2 ∂μ) /
        ENNReal.ofReal (ε.toReal ^ 2) := by
    intro T
    have hset_sub :
        {ω : Ω | ε ≤ edist (f T ω) a} ⊆
        {ω : Ω | ENNReal.ofReal (ε.toReal ^ 2) ≤
          ENNReal.ofReal ((f T ω - a) ^ 2)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      apply ENNReal.ofReal_le_ofReal
      have h_eps : ε = ENNReal.ofReal ε.toReal :=
        (ENNReal.ofReal_toReal hε_top).symm
      rw [h_eps, edist_dist, Real.dist_eq] at hω
      have habs : ε.toReal ≤ |f T ω - a| :=
        (ENNReal.ofReal_le_ofReal_iff
          (abs_nonneg _)).mp hω
      nlinarith [sq_abs (f T ω - a),
        sq_nonneg (ε.toReal)]
    have haemeas : AEMeasurable
        (fun ω => ENNReal.ofReal
          ((f T ω - a) ^ 2)) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (((hf T).sub
          aestronglyMeasurable_const
          ).aemeasurable.pow_const 2)
    calc μ {ω | ε ≤ edist (f T ω) a}
        ≤ μ {ω | ENNReal.ofReal (ε.toReal ^ 2) ≤
            ENNReal.ofReal ((f T ω - a) ^ 2)} :=
          measure_mono hset_sub
      _ ≤ (∫⁻ ω, ENNReal.ofReal
            ((f T ω - a) ^ 2) ∂μ) /
          ENNReal.ofReal (ε.toReal ^ 2) :=
          meas_ge_le_lintegral_div haemeas
            (ENNReal.ofReal_pos.mpr hε2_pos).ne'
            ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal
            (∫ ω, (f T ω - a) ^ 2 ∂μ) /
          ENNReal.ofReal (ε.toReal ^ 2) := by
          congr 1
          exact (ofReal_integral_eq_lintegral_ofReal
            (hint T)
            (ae_of_all μ (fun ω =>
              sq_nonneg (f T ω - a)))).symm
  have hbound : Tendsto (fun T =>
      ENNReal.ofReal (∫ ω, (f T ω - a) ^ 2 ∂μ) /
      ENNReal.ofReal (ε.toReal ^ 2))
      atTop (𝓝 0) := by
    have h_eq : (fun T =>
        ENNReal.ofReal
          (∫ ω, (f T ω - a) ^ 2 ∂μ) /
        ENNReal.ofReal (ε.toReal ^ 2)) =
        (fun T =>
          ENNReal.ofReal
            (∫ ω, (f T ω - a) ^ 2 ∂μ) *
          (ENNReal.ofReal
            (ε.toReal ^ 2))⁻¹) := rfl
    rw [h_eq]
    have h_zero : (0 : ENNReal) =
        ENNReal.ofReal 0 *
        (ENNReal.ofReal (ε.toReal ^ 2))⁻¹ := by
      simp
    rw [h_zero]
    have hc_ne_top :
        (ENNReal.ofReal
          (ε.toReal ^ 2))⁻¹ ≠ ⊤ := by
      rw [ENNReal.inv_ne_top]
      exact (ENNReal.ofReal_pos.mpr hε2_pos).ne'
    have h_cont : Continuous (fun x : ENNReal =>
        x * (ENNReal.ofReal
          (ε.toReal ^ 2))⁻¹) :=
      ENNReal.continuous_mul_const hc_ne_top
    exact h_cont.continuousAt.tendsto.comp
      ((ENNReal.continuous_ofReal.tendsto 0).comp
        h)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T; exact hS T

/-- **L² convergence to zero implies convergence in measure to
zero.** Corollary of `l2_tendstoInMeasure` with `a = 0`. -/
lemma l2_tendstoInMeasure_zero {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ T, AEStronglyMeasurable (X T) μ)
    (hXsq : ∀ T,
      Integrable (fun ω => X T ω ^ 2) μ)
    (h_var : Tendsto
      (fun T => ∫ ω, X T ω ^ 2 ∂μ)
      atTop (nhds 0)) :
    TendstoInMeasure μ X atTop (fun _ => 0) :=
  l2_tendstoInMeasure μ hX
    (fun T => by simpa using hXsq T)
    (by simpa using h_var)

end MeasureTheory
