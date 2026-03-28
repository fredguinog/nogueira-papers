/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Econometrics.Probability.Mixing.Covariance

/-!
# Asymptotic Theory for α-Mixing Processes

This file carries out the asymptotic argument that leads to the Law of Large Numbers
for α-mixing processes. It has two conceptual parts.

**Part I – Layer-cake approximation.** We approximate a bounded measurable function
`f : Ω → [0, 1]` by the step function `layerSum f N` defined via indicator sets of
the form `{ω | i/N ≤ f(ω)}`. This gives an approximation error of `1/N` and allows
the covariance of `f` and `g` to be controlled by the α-mixing coefficient directly
from the indicator-event bound `cov_bound_indicator`.

**Part II – Law of Large Numbers.** Under covariance stationarity and summability of
the autocovariance function, the sample mean converges to zero in L² as `T → ∞`.

## Main definitions

* `ProbabilityTheory.layerSet f i N` : the upper-level set `{ω | i/N ≤ f(ω)}`.
* `ProbabilityTheory.layerSum f N` : the step-function approximation of `f` at
  resolution `N`.
* `ProbabilityTheory.IsCovarianceStationary μ X` : covariance depends only on lag.
* `ProbabilityTheory.autocovariance μ X h` : the autocovariance function at lag `h`.

## Main results

* `ProbabilityTheory.layerSum_bound` : `0 ≤ f − layerSum f N ≤ 1/N` pointwise.
* `ProbabilityTheory.cov_bound_nonneg_le_one` : the covariance bound for
  functions in `[0, 1]`, as an intermediate step toward `cov_bound_alphaMixing`.
* `ProbabilityTheory.cov_bound_alphaMixing` : **Davidson Theorem 14.1** — for
  functions bounded by `1`, `|Cov(f, g)| ≤ 4 α`.
* `ProbabilityTheory.lln_alphaMixing` : **LLN** — if `X` is covariance-stationary,
  square-integrable, and has summable autocovariance, then
  `∫ ‖T⁻¹ Σ Xₜ‖² dμ → 0`.

## References

* Davidson, J. (1994). *Stochastic Limit Theory*, Theorems 14.1, 19.11.
  Oxford University Press.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]

/-! ### Layer-cake step-function approximation -/

/-- The `i`-th upper-level set of `f` at resolution `N`:
`layerSet f i N = {ω | i/N ≤ f(ω)}`. -/
def layerSet (f : Ω → ℝ) (i N : ℕ) : Set Ω :=
  {ω | (i : ℝ) / (N : ℝ) ≤ f ω}

/-- The step-function approximation of `f : Ω → [0,1]` at resolution `N`,
defined by `layerSum f N ω = N⁻¹ · ∑_{i=1}^{N} 𝟙_{layerSet f i N}(ω)`. -/
noncomputable def layerSum (f : Ω → ℝ) (N : ℕ) : Ω → ℝ :=
  fun ω => (N : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 N, (layerSet f i N).indicator (fun _ => (1 : ℝ)) ω

/-- `layerSum f N` is measurable whenever `f` is measurable. -/
-- omit [mE : MeasurableSpace E] in
lemma layerSum_measurable {m : MeasurableSpace Ω} (N : ℕ) (f : Ω → ℝ)
    (hf_meas : @Measurable Ω ℝ m inferInstance f) :
    @Measurable Ω ℝ m inferInstance (layerSum f N) := by
  unfold layerSum layerSet
  letI := m
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Measurable.indicator
  · exact measurable_const
  · exact measurableSet_le measurable_const hf_meas

/-- **Layer-cake approximation error bound.** For `f : Ω → [0, 1]` and `N ≥ 1`,
the step-function approximation satisfies `0 ≤ f(ω) − layerSum f N ω ≤ 1/N`
pointwise. -/
-- omit [mE : MeasurableSpace E] in
lemma layerSum_bound (f : Ω → ℝ) (N : ℕ) (hN : 0 < N)
    (hf_pos : ∀ ω, 0 ≤ f ω) (hf_le_one : ∀ ω, f ω ≤ 1) (ω : Ω) :
    0 ≤ f ω - layerSum f N ω ∧ f ω - layerSum f N ω ≤ (N : ℝ)⁻¹ := by
  unfold layerSum layerSet Set.indicator
  dsimp
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hfw_pos : 0 ≤ f ω := hf_pos ω
  let k := ⌊f ω * N⌋₊
  have hk_le_Nx : (k : ℝ) ≤ f ω * N := Nat.floor_le (by positivity)
  have hNx_lt_k1 : f ω * N < (k : ℝ) + 1 := Nat.lt_floor_add_one (f ω * N)
  have hk_le_N_real : (k : ℝ) ≤ N := by
    have h1 : f ω ≤ 1 := hf_le_one ω
    have h2 : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hN_pos
    calc (k : ℝ) ≤ f ω * N := hk_le_Nx
    _ ≤ 1 * (N : ℝ) := by nlinarith
    _ = N := one_mul _
  have hk_le_N : k ≤ N := Nat.cast_le.mp hk_le_N_real
  have h_sum_eq_k : (∑ i ∈ Finset.Icc 1 N, if (i : ℝ) / (N : ℝ) ≤
      f ω then (1 : ℝ) else 0) = (k : ℝ) := by
    have h_iff : ∀ i : ℕ, (i : ℝ) / N ≤ f ω ↔ i ≤ k := by
      intro i
      rw [div_le_iff₀ hN_pos]
      constructor
      · intro h_le
        by_contra! h_gt
        have h1 : (k : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h_gt
        have h2 : f ω * N < (i : ℝ) := lt_of_lt_of_le hNx_lt_k1 h1
        linarith
      · intro h_le
        have hi : (i : ℝ) ≤ k := Nat.cast_le.mpr h_le
        linarith
    have h_sum_eq : (∑ i ∈ Finset.Icc 1 N, if (i : ℝ) / N ≤ f ω then (1 : ℝ) else 0) =
                    (∑ i ∈ Finset.Icc 1 N, if i ≤ k then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [h_iff i]
    rw [h_sum_eq, Finset.sum_ite]
    have h_filter : (Finset.Icc 1 N).filter (fun i => i ≤ k) = Finset.Icc 1 k := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, hk⟩; exact ⟨h1, hk⟩
      · rintro ⟨h1, hk⟩; exact ⟨⟨h1, le_trans hk hk_le_N⟩, hk⟩
    have h_true : (∑ i ∈ (Finset.Icc 1 N).filter (fun i => i ≤ k), (1 : ℝ)) = (k : ℝ) := by
      rw [h_filter, Finset.sum_const]
      have h_card : (Finset.Icc 1 k).card = k := by rw [Nat.card_Icc]; omega
      simp [h_card]
    have h_false : (∑ i ∈ (Finset.Icc 1 N).filter (fun i => ¬(i ≤ k)), (0 : ℝ)) = 0 :=
        Finset.sum_const_zero
    rw [h_true, h_false]
    linarith
  rw [h_sum_eq_k]
  have h_goal_eq : (0 ≤ f ω - (N : ℝ)⁻¹ * (k : ℝ) ∧ f ω - (N : ℝ)⁻¹ * (k : ℝ) ≤ (N : ℝ)⁻¹) ↔
                   (0 ≤ f ω - (k : ℝ) / N ∧ f ω - (k : ℝ) / N ≤ 1 / N) := by
    have h1 : (N : ℝ)⁻¹ * (k : ℝ) = (k : ℝ) / N := by ring
    have h2 : (N : ℝ)⁻¹ = 1 / (N : ℝ) := by ring
    rw [h1, h2]
  rw [h_goal_eq]
  constructor
  · have h_lower : (k : ℝ) / N ≤ f ω := (div_le_iff₀ hN_pos).mpr hk_le_Nx
    linarith
  · have h_upper : f ω ≤ (k : ℝ) / N + 1 / N := by
      rw [← add_div]
      apply (le_div_iff₀ hN_pos).mpr
      linarith[hNx_lt_k1]
    linarith

/-! ### Covariance of step functions -/

/-- The covariance of the step-function approximations is bounded by the α-mixing
coefficient. This is the discrete layer-cake version of the indicator bound. -/
lemma cov_layerSum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) (s t N : ℕ) (hN : 0 < N) (f g : Ω → ℝ)
    (hf_meas : @Measurable Ω ℝ (pastSigmaAlgebra X s) inferInstance f)
    (hg_meas : @Measurable Ω ℝ (futureSigmaAlgebra X t) inferInstance g) :
    |∫ ω, layerSum f N ω * layerSum g N ω ∂μ -
     (∫ ω, layerSum f N ω ∂μ) * (∫ ω, layerSum g N ω ∂μ)| ≤
    alphaMixingCoeff μ (pastSigmaAlgebra X s).MeasurableSet' (futureSigmaAlgebra X
        t).MeasurableSet' := by
  let A i := layerSet f i N
  let B j := layerSet g j N
  let S1 : Set (Set Ω) := (pastSigmaAlgebra X s).MeasurableSet'
  let S2 : Set (Set Ω) := (futureSigmaAlgebra X t).MeasurableSet'
  let α_val := alphaMixingCoeff μ S1 S2
  have hA_meas : ∀ i, A i ∈ S1 := fun i => measurableSet_le measurable_const hf_meas
  have hB_meas : ∀ j, B j ∈ S2 := fun j => measurableSet_le measurable_const hg_meas
  have hA_meas_global : ∀ i, MeasurableSet (A i) := fun i => past_le_global X hX s (A i) (hA_meas i)
  have hB_meas_global : ∀ j, MeasurableSet (B j) :=
      fun j => future_le_global X hX t (B j) (hB_meas j)
  have h_int_indA : ∀ i, ∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ (A i)).toReal := by
    intro i; simp [integral_indicator_const, Measure.real, hA_meas_global i]
  have h_int_indB : ∀ j, ∫ ω, (B j).indicator (fun _ => (1 : ℝ)) ω ∂μ = (μ (B j)).toReal := by
    intro j; simp [Measure.real, integral_indicator_const, hB_meas_global j]
  have h_int_indAB : ∀ i j, ∫ ω, (A i ∩ B j).indicator (fun _ => (1 : ℝ)) ω ∂μ =
      (μ (A i ∩ B j)).toReal := by
    intro i j; simp [Measure.real, integral_indicator_const,
        (hA_meas_global i).inter (hB_meas_global j)]
  have h_integrableA : ∀ i, Integrable (fun ω => (A i).indicator (fun _ => (1 : ℝ)) ω) μ := by
    intro i; apply integrable_of_bounded_one μ _ (Measurable.indicator measurable_const
        (hA_meas_global i))
    intro ω; by_cases h : ω ∈ A i <;> simp [Set.indicator, h]
  have h_integrableB : ∀ j, Integrable (fun ω => (B j).indicator (fun _ => (1 : ℝ)) ω) μ := by
    intro j; apply integrable_of_bounded_one μ _ (Measurable.indicator measurable_const
        (hB_meas_global j))
    intro ω; by_cases h : ω ∈ B j <;> simp [Set.indicator, h]
  have h_integrableAB : ∀ i j,
      Integrable (fun ω => (A i ∩ B j).indicator (fun _ => (1 : ℝ)) ω) μ := by
    intro i j; apply integrable_of_bounded_one μ _ (Measurable.indicator measurable_const
        ((hA_meas_global i).inter (hB_meas_global j)))
    intro ω; by_cases hA : ω ∈ A i <;> by_cases hB : ω ∈ B j <;> simp [Set.indicator, hA, hB]
  have h_int_f : ∫ ω, layerSum f N ω ∂μ = (N:ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 N, (μ (A i)).toReal := by
    dsimp [layerSum]; rw [integral_const_mul, integral_finset_sum _ (fun i _ => h_integrableA i)]
    congr 1; apply Finset.sum_congr rfl; intro i _; exact h_int_indA i
  have h_int_g : ∫ ω, layerSum g N ω ∂μ = (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, (μ (B j)).toReal := by
    dsimp [layerSum]; rw [integral_const_mul, integral_finset_sum _ (fun j _ => h_integrableB j)]
    congr 1; apply Finset.sum_congr rfl; intro j _; exact h_int_indB j
  have h_int_fg : ∫ ω, layerSum f N ω * layerSum g N ω ∂μ =
    (N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (μ (A i ∩ B j)).toReal := by
    have h_prod : (fun ω => layerSum f N ω * layerSum g N ω) =
      fun ω => (N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
          (A i ∩ B j).indicator (fun _ => (1 : ℝ)) ω := by
      ext ω; dsimp [layerSum]
      have eq1 : ((N:ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 N, (A i).indicator (fun _ => (1 : ℝ)) ω) *
                 ((N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, (B j).indicator (fun _ => (1 : ℝ)) ω) =
                 (N:ℝ)⁻¹^2 * ((∑ i ∈ Finset.Icc 1 N, (A i).indicator (fun _ => (1 : ℝ)) ω) *
                              (∑ j ∈ Finset.Icc 1 N, (B j).indicator (fun _ => (1 : ℝ)) ω)) :=
                                  by ring
      rw [eq1, Finset.sum_mul]
      congr 1; apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]
      congr 1; ext j
      by_cases hA : ω ∈ A i <;> by_cases hB : ω ∈ B j <;> simp [Set.indicator, hA, hB]
    rw [h_prod, integral_const_mul]
    congr 1; rw [integral_finset_sum]
    · apply Finset.sum_congr rfl; intro i _; rw [integral_finset_sum]
      · apply Finset.sum_congr rfl; intro j _; exact h_int_indAB i j
      · intro j _; exact h_integrableAB i j
    · intro i _; apply integrable_finset_sum; intro j _; exact h_integrableAB i j
  rw [h_int_f, h_int_g, h_int_fg]
  have h_algebra :
    ((N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, (μ (A i ∩ B j)).toReal) -
    ((N:ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 N, (μ (A i)).toReal) * ((N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N,
        (μ (B j)).toReal) =
    (N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        ((μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal) := by
    have h_prod : ((N:ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 N,
        (μ (A i)).toReal) * ((N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N, (μ (B j)).toReal) =
                  (N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
                      (μ (A i)).toReal * (μ (B j)).toReal := by
      calc ((N:ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 N, (μ (A i)).toReal) * ((N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 N,
          (μ (B j)).toReal)
        _ =
            (N:ℝ)⁻¹^2 * ((∑ i ∈ Finset.Icc 1 N, (μ (A i)).toReal) * (∑ j ∈ Finset.Icc 1 N,
                (μ (B j)).toReal)) := by ring
        _ =
            (N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ((μ (A i)).toReal * ∑ j ∈ Finset.Icc 1 N,
                (μ (B j)).toReal) := by rw [Finset.sum_mul]
        _ =
            (N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
                (μ (A i)).toReal * (μ (B j)).toReal := by simp_rw [Finset.mul_sum]
    rw [h_prod, ← mul_sub]
    congr 1; rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
  rw [h_algebra]
  have h_abs_sum : |∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      ((μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal)| ≤
                   ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
                       |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal| := by
    calc |∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
        ((μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal)|
      _ ≤
          ∑ i ∈ Finset.Icc 1 N, |∑ j ∈ Finset.Icc 1 N,
              ((μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal)| :=
                  Finset.abs_sum_le_sum_abs _ _
      _ ≤
          ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
              |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal| := by
        apply Finset.sum_le_sum; intro i _
        exact Finset.abs_sum_le_sum_abs _ _
  have h_bound_elements : ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal| ≤
                          ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, α_val := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    exact cov_bound_indicator μ S1 S2 (hA_meas i) (hB_meas j)
  have h_sum_alpha : (∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, α_val) = (N:ℝ)^2 * α_val := by
    have h_inner : (∑ j ∈ Finset.Icc 1 N, α_val) = (N:ℝ) * α_val := by
      rw [Finset.sum_const, Nat.card_Icc]
      have h1 : N + 1 - 1 = N := by omega
      rw [h1, nsmul_eq_mul]
    simp_rw [h_inner]
    rw [Finset.sum_const, Nat.card_Icc]
    have h1 : N + 1 - 1 = N := by omega
    rw [h1, nsmul_eq_mul]
    ring
  calc |(N:ℝ)⁻¹^2 * ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      ((μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal)|
    _ =
        (N:ℝ)⁻¹^2 * |∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
            ((μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal)| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤
        (N:ℝ)⁻¹^2 * (∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
            |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|) :=
                mul_le_mul_of_nonneg_left h_abs_sum (by positivity)
    _ ≤ (N:ℝ)⁻¹^2 * (∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N, α_val) :=
        mul_le_mul_of_nonneg_left h_bound_elements (by positivity)
    _ = (N:ℝ)⁻¹^2 * ((N:ℝ)^2 * α_val) := by rw [h_sum_alpha]
    _ = ((N:ℝ)⁻¹^2 * (N:ℝ)^2) * α_val := by rw [mul_assoc]
    _ = 1 * α_val := by
      congr 1
      have hn_real : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
      have h_inv : (N:ℝ)⁻¹ * (N:ℝ) = 1 := inv_mul_cancel₀ hn_real
      calc (N:ℝ)⁻¹^2 * (N:ℝ)^2 = ((N:ℝ)⁻¹ * (N:ℝ))^2 := by ring
      _ = (1:ℝ)^2 := by rw [h_inv]
      _ = 1 := by ring
    _ = α_val := one_mul _

/-! ### Approximation error for covariances -/

/-- The difference between the covariance of `f, g` and the covariance of their
step-function approximations `fN, gN` is at most `4/N`. -/
lemma cov_approxError (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g fN gN : Ω → ℝ) (N : ℝ) (hN : 0 < N)
    (hf_bound : ∀ ω, 0 ≤ f ω ∧ f ω ≤ 1)
    (hgN_bound : ∀ ω, 0 ≤ gN ω ∧ gN ω ≤ 1)
    (hf_diff : ∀ ω, 0 ≤ f ω - fN ω ∧ f ω - fN ω ≤ N⁻¹)
    (hg_diff : ∀ ω, 0 ≤ g ω - gN ω ∧ g ω - gN ω ≤ N⁻¹)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hfN_int : Integrable fN μ) (hgN_int : Integrable gN μ)
    (hfg_int : Integrable (fun ω => f ω * g ω) μ)
    (hfNgN_int : Integrable (fun ω => fN ω * gN ω) μ) :
    |(∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)) -
      (∫ ω, fN ω * gN ω ∂μ - (∫ ω, fN ω ∂μ) * (∫ ω, gN ω ∂μ))| ≤
    4 / N := by
  let Ifg := ∫ ω, f ω * g ω ∂μ
  let IfNgN := ∫ ω, fN ω * gN ω ∂μ
  let If := ∫ ω, f ω ∂μ
  let Ig := ∫ ω, g ω ∂μ
  let IfN := ∫ ω, fN ω ∂μ
  let IgN := ∫ ω, gN ω ∂μ
  have h_diff_expand : (Ifg - If * Ig) - (IfNgN - IfN * IgN) =
      (Ifg - IfNgN) - (If * Ig - IfN * IgN) := by ring
  rw [h_diff_expand]
  have h_fg_eq : ∀ ω, f ω * g ω - fN ω * gN ω = f ω * (g ω - gN ω) + gN ω * (f ω - fN ω) :=
      by intro ω; ring
  have h_fg_pos : ∀ ω, 0 ≤ f ω * g ω - fN ω * gN ω := by
    intro ω; rw [h_fg_eq ω]
    have h1 : 0 ≤ f ω * (g ω - gN ω) := mul_nonneg (hf_bound ω).1 (hg_diff ω).1
    have h2 : 0 ≤ gN ω * (f ω - fN ω) := mul_nonneg (hgN_bound ω).1 (hf_diff ω).1
    positivity
  have h_fg_le : ∀ ω, f ω * g ω - fN ω * gN ω ≤ 2 / N := by
    intro ω; rw [h_fg_eq ω]
    have h1 : f ω * (g ω - gN ω) ≤ 1 * N⁻¹ :=
        mul_le_mul (hf_bound ω).2 (hg_diff ω).2 (hg_diff ω).1 zero_le_one
    have h2 : gN ω * (f ω - fN ω) ≤ 1 * N⁻¹ :=
        mul_le_mul (hgN_bound ω).2 (hf_diff ω).2 (hf_diff ω).1 zero_le_one
    have h3 : 1 * N⁻¹ + 1 * N⁻¹ = 2 / N := by ring
    linarith
  have h_Ifg_sub : ∫ ω, f ω * g ω - fN ω * gN ω ∂μ = Ifg - IfNgN := integral_sub hfg_int hfNgN_int
  have h_Ifg_pos : 0 ≤ Ifg - IfNgN := by rw [← h_Ifg_sub]; exact integral_nonneg h_fg_pos
  have h_Ifg_le : Ifg - IfNgN ≤ 2 / N := by
    rw [← h_Ifg_sub]
    have h_mono := integral_mono (hfg_int.sub hfNgN_int) (integrable_const (2 / N)) h_fg_le
    have h_const : ∫ ω, (2 / N : ℝ) ∂μ = 2 / N := by rw [integral_const]; simp
    rw [h_const] at h_mono
    exact h_mono
  have h_If_sub : ∫ ω, f ω - fN ω ∂μ = If - IfN := integral_sub hf_int hfN_int
  have h_If_pos : 0 ≤ If - IfN := by rw [← h_If_sub]; exact integral_nonneg (fun ω => (hf_diff ω).1)
  have h_If_le : If - IfN ≤ 1 / N := by
    rw [← h_If_sub]
    have h_mono :=
        integral_mono (hf_int.sub hfN_int) (integrable_const N⁻¹) (fun ω => (hf_diff ω).2)
    have h_const : ∫ ω, (N⁻¹ : ℝ) ∂μ = 1 / N := by rw [integral_const]; simp
    rw [h_const] at h_mono
    exact h_mono
  have h_Ig_sub : ∫ ω, g ω - gN ω ∂μ = Ig - IgN := integral_sub hg_int hgN_int
  have h_Ig_pos : 0 ≤ Ig - IgN := by rw [← h_Ig_sub]; exact integral_nonneg (fun ω => (hg_diff ω).1)
  have h_Ig_le : Ig - IgN ≤ 1 / N := by
    rw [← h_Ig_sub]
    have h_mono :=
        integral_mono (hg_int.sub hgN_int) (integrable_const N⁻¹) (fun ω => (hg_diff ω).2)
    have h_const : ∫ ω, (N⁻¹ : ℝ) ∂μ = 1 / N := by rw [integral_const]; simp
    rw [h_const] at h_mono
    exact h_mono
  have h_If_le1 : If ≤ 1 := by
    have h_mono := integral_mono hf_int (integrable_const 1) (fun ω => (hf_bound ω).2)
    have h_const : ∫ ω, (1 : ℝ) ∂μ = 1 := by rw [integral_const]; simp
    rw [h_const] at h_mono
    exact h_mono
  have h_IgN_le1 : IgN ≤ 1 := by
    have h_mono := integral_mono hgN_int (integrable_const 1) (fun ω => (hgN_bound ω).2)
    have h_const : ∫ ω, (1 : ℝ) ∂μ = 1 := by rw [integral_const]; simp
    rw [h_const] at h_mono
    exact h_mono
  have h_IfIg_eq : If * Ig - IfN * IgN = If * (Ig - IgN) + IgN * (If - IfN) := by ring
  have h_IfIg_pos : 0 ≤ If * Ig - IfN * IgN := by
    rw [h_IfIg_eq]
    have hIf_pos : 0 ≤ If := integral_nonneg (fun ω => (hf_bound ω).1)
    have hIgN_pos : 0 ≤ IgN := integral_nonneg (fun ω => (hgN_bound ω).1)
    have h1 : 0 ≤ If * (Ig - IgN) := mul_nonneg hIf_pos h_Ig_pos
    have h2 : 0 ≤ IgN * (If - IfN) := mul_nonneg hIgN_pos h_If_pos
    positivity
  have h_IfIg_le : If * Ig - IfN * IgN ≤ 2 / N := by
    rw [h_IfIg_eq]
    have hIf_pos : 0 ≤ If := integral_nonneg (fun ω => (hf_bound ω).1)
    have hIgN_pos : 0 ≤ IgN := integral_nonneg (fun ω => (hgN_bound ω).1)
    have h1 : If * (Ig - IgN) ≤ 1 * (1 / N) := mul_le_mul h_If_le1 h_Ig_le h_Ig_pos zero_le_one
    have h2 : IgN * (If - IfN) ≤ 1 * (1 / N) := mul_le_mul h_IgN_le1 h_If_le h_If_pos zero_le_one
    have h3 : 1 * (1 / N) + 1 * (1 / N) = 2 / N := by ring
    linarith
  have h_split : 4 / N = 2 / N + 2 / N := by ring
  have h_pos_2N : 0 ≤ 2 / N := by positivity
  rw [abs_le, h_split]
  constructor
  · linarith
  · linarith

/-! ### Covariance bound for [0,1]-valued functions -/

/-- The covariance bound `|Cov(f₀, g₀)| ≤ α` for functions `f₀, g₀ ∈ [0, 1]`.
This is the intermediate step toward `cov_bound_alphaMixing`, proved by approximating
`f₀` and `g₀` with layer-cake step functions and combining `cov_layerSum` with
`cov_approxError`. -/
lemma cov_bound_nonneg_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) (s t : ℕ) (f₀ g₀ : Ω → ℝ)
    (hf_pos : ∀ ω, 0 ≤ f₀ ω) (hf_le_one : ∀ ω, f₀ ω ≤ 1)
    (hg_pos : ∀ ω, 0 ≤ g₀ ω) (hg_le_one : ∀ ω, g₀ ω ≤ 1)
    (hf_meas : @Measurable Ω ℝ (pastSigmaAlgebra X s) inferInstance f₀)
    (hg_meas : @Measurable Ω ℝ (futureSigmaAlgebra X t) inferInstance g₀) :
    |∫ ω, f₀ ω * g₀ ω ∂μ - (∫ ω, f₀ ω ∂μ) * (∫ ω, g₀ ω ∂μ)| ≤
    alphaMixingCoeff μ (pastSigmaAlgebra X s).MeasurableSet' (futureSigmaAlgebra X
        t).MeasurableSet' := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have h4_eps : 0 < 4 / ε := div_pos (by norm_num) hε
  obtain ⟨N, hN_bound⟩ := exists_nat_gt (4 / ε)
  have hN_pos_real : (0 : ℝ) < N := lt_trans h4_eps hN_bound
  have hN_pos : 0 < N := by exact Nat.cast_pos.mp hN_pos_real
  let fN := layerSum f₀ N
  let gN := layerSum g₀ N
  have hf_bound : ∀ ω, 0 ≤ f₀ ω ∧ f₀ ω ≤ 1 := fun ω => ⟨hf_pos ω, hf_le_one ω⟩
  have hf_diff : ∀ ω, 0 ≤ f₀ ω - fN ω ∧ f₀ ω - fN ω ≤ (N:ℝ)⁻¹ :=
      layerSum_bound f₀ N hN_pos hf_pos hf_le_one
  have hg_diff : ∀ ω, 0 ≤ g₀ ω - gN ω ∧ g₀ ω - gN ω ≤ (N:ℝ)⁻¹ :=
      layerSum_bound g₀ N hN_pos hg_pos hg_le_one
  have hfN_bound : ∀ ω, 0 ≤ fN ω ∧ fN ω ≤ 1 := by
    intro ω; have hd := hf_diff ω; have hb := hf_bound ω
    constructor
    · dsimp [fN, layerSum, Set.indicator]; apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg; intro i _; split_ifs <;> positivity
    · linarith
  have hgN_bound : ∀ ω, 0 ≤ gN ω ∧ gN ω ≤ 1 := by
    intro ω; have hd := hg_diff ω; have hb : 0 ≤ g₀ ω ∧ g₀ ω ≤ 1 := ⟨hg_pos ω, hg_le_one ω⟩
    constructor
    · dsimp [gN, layerSum, Set.indicator]; apply mul_nonneg (by positivity)
      apply Finset.sum_nonneg; intro i _; split_ifs <;> positivity
    · linarith
  have hf_meas_global : Measurable f₀ := Measurable.mono hf_meas (past_le_global X hX s) le_rfl
  have hg_meas_global : Measurable g₀ := Measurable.mono hg_meas (future_le_global X hX t) le_rfl
  have hf_bound_abs : ∀ ω, |f₀ ω| ≤ 1 :=
      by intro ω; have h := hf_bound ω; rw [abs_le]; constructor <;> linarith
  have hg_bound_abs : ∀ ω, |g₀ ω| ≤ 1 :=
      by intro ω; have h1 := hg_pos ω; have h2 := hg_le_one ω; rw [abs_le]; constructor <;> linarith
  have hf_int : Integrable f₀ μ := integrable_of_bounded_one μ f₀ hf_meas_global hf_bound_abs
  have hg_int : Integrable g₀ μ := integrable_of_bounded_one μ g₀ hg_meas_global hg_bound_abs
  have hfN_meas_sub : @Measurable Ω ℝ (pastSigmaAlgebra X s) inferInstance fN :=
      layerSum_measurable N f₀ hf_meas
  have hgN_meas_sub : @Measurable Ω ℝ (futureSigmaAlgebra X t) inferInstance gN :=
      layerSum_measurable N g₀ hg_meas
  have hfN_meas_global : Measurable fN :=
      Measurable.mono hfN_meas_sub (past_le_global X hX s) le_rfl
  have hgN_meas_global : Measurable gN :=
      Measurable.mono hgN_meas_sub (future_le_global X hX t) le_rfl
  have hfN_bound_abs : ∀ ω, |fN ω| ≤ 1 :=
      by intro ω; have h := hfN_bound ω; rw [abs_le]; constructor <;> linarith
  have hgN_bound_abs : ∀ ω, |gN ω| ≤ 1 :=
      by intro ω; have h := hgN_bound ω; rw [abs_le]; constructor <;> linarith
  have hfN_int : Integrable fN μ := integrable_of_bounded_one μ fN hfN_meas_global hfN_bound_abs
  have hgN_int : Integrable gN μ := integrable_of_bounded_one μ gN hgN_meas_global hgN_bound_abs
  have hfg_meas_global : Measurable (fun ω => f₀ ω * g₀ ω) :=
      Measurable.mul hf_meas_global hg_meas_global
  have hfNgN_meas_global : Measurable (fun ω => fN ω * gN ω) :=
      Measurable.mul hfN_meas_global hgN_meas_global
  have hfg_bound : ∀ ω, |f₀ ω * g₀ ω| ≤ 1 :=
      by intro ω; have h1 :=
          hf_bound ω; have h2 :=
              hg_pos ω; have h3 := hg_le_one ω; rw [abs_le]; constructor <;> nlinarith
  have hfNgN_bound : ∀ ω, |fN ω * gN ω| ≤ 1 :=
      by intro ω; have h1 :=
          hfN_bound ω; have h2 := hgN_bound ω; rw [abs_le]; constructor <;> nlinarith
  have hfg_int : Integrable (fun ω => f₀ ω * g₀ ω) μ :=
      integrable_of_bounded_one μ _ hfg_meas_global hfg_bound
  have hfNgN_int : Integrable (fun ω => fN ω * gN ω) μ :=
      integrable_of_bounded_one μ _ hfNgN_meas_global hfNgN_bound
  have h_approx := cov_approxError μ f₀ g₀ fN gN (N:ℝ) hN_pos_real
    hf_bound hgN_bound hf_diff hg_diff
    hf_int hg_int hfN_int hgN_int hfg_int hfNgN_int
  have h_layer_cov := cov_layerSum μ X hX s t N hN_pos f₀ g₀ hf_meas hg_meas
  have h_eps_N : 4 / (N : ℝ) < ε := by
    have h1 : 4 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN_bound
    rw [mul_comm] at h1
    exact (div_lt_iff₀ hN_pos_real).mpr h1
  have h_approx_unfold := abs_le.mp h_approx
  have h_layer_cov_unfold := abs_le.mp h_layer_cov
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-! ### Main covariance bound -/

/-- **Davidson's covariance inequality (Theorem 14.1).**

For any probability measure `μ` on an α-mixing process `X` and any two functions
`f`, `g` bounded by `1`, the absolute covariance satisfies
`|Cov(f, g)| ≤ 4 · α(s, t)`,
where `α(s, t)` is the mixing coefficient between the past up to `s` and the future
from `t`.

The proof proceeds by:
1. Shifting `f, g ∈ [-1, 1]` to `f₀, g₀ ∈ [0, 1]` via `f = 2f₀ − 1`
   (`cov_affineReduction`).
2. Approximating `f₀, g₀` by layer-cake step functions at resolution `N`
   (`cov_bound_nonneg_le_one`).
3. Bounding the step-function covariance directly by `α` via indicator events.
-/
theorem cov_bound_alphaMixing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (hX : ∀ n, Measurable (X n)) (s t : ℕ) (f g : Ω → ℝ)
    (hf : ∀ ω, |f ω| ≤ 1) (hg : ∀ ω, |g ω| ≤ 1)
    (hf_meas : @Measurable Ω ℝ (pastSigmaAlgebra X s) inferInstance f)
    (hg_meas : @Measurable Ω ℝ (futureSigmaAlgebra X t) inferInstance g) :
    |∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)| ≤
    4 * alphaMixingCoeff μ (pastSigmaAlgebra X s).MeasurableSet'
                           (futureSigmaAlgebra X t).MeasurableSet' := by
  let f₀ : Ω → ℝ := fun ω => (f ω + 1) / 2
  let g₀ : Ω → ℝ := fun ω => (g ω + 1) / 2
  have hf₀_pos    : ∀ ω, 0 ≤ f₀ ω    := by intro ω; simp [f₀]; linarith [(abs_le.mp (hf ω)).1]
  have hf₀_le_one : ∀ ω, f₀ ω ≤ 1   := by intro ω; simp [f₀]; linarith [(abs_le.mp (hf ω)).2]
  have hg₀_pos    : ∀ ω, 0 ≤ g₀ ω    := by intro ω; simp [g₀]; linarith [(abs_le.mp (hg ω)).1]
  have hg₀_le_one : ∀ ω, g₀ ω ≤ 1   := by intro ω; simp [g₀]; linarith [(abs_le.mp (hg ω)).2]
  have hf_meas_global : Measurable f :=
    Measurable.mono hf_meas (past_le_global X hX s) le_rfl
  have hg_meas_global : Measurable g :=
    Measurable.mono hg_meas (future_le_global X hX t) le_rfl
  have hf_int  : Integrable f μ :=
    integrable_of_bounded_one μ f hf_meas_global hf
  have hg_int  : Integrable g μ :=
    integrable_of_bounded_one μ g hg_meas_global hg
  have hfg_int : Integrable (fun ω => f ω * g ω) μ := by
    apply integrable_of_bounded_one μ _ (hf_meas_global.mul hg_meas_global)
    intro ω; rw [abs_le]; constructor <;> nlinarith [hf ω, hg ω,
      abs_le.mp (hf ω), abs_le.mp (hg ω)]
  have hf₀_int : Integrable f₀ μ :=
    (hf_int.add (integrable_const 1)).div_const 2
  have hg₀_int : Integrable g₀ μ :=
    (hg_int.add (integrable_const 1)).div_const 2
  have hfg₀_int : Integrable (fun ω => f₀ ω * g₀ ω) μ := by
    have h_eq : (fun ω => f₀ ω * g₀ ω) =
        fun ω => (f ω * g ω + f ω + g ω + 1) / 4 := by ext ω; simp [f₀, g₀]; ring
    rw [h_eq]
    exact (((hfg_int.add hf_int).add hg_int).add (integrable_const 1)).div_const 4
  have hf₀_meas : @Measurable Ω ℝ (pastSigmaAlgebra X s) inferInstance f₀ := by
    letI := pastSigmaAlgebra X s
    exact (hf_meas.add measurable_const).div_const 2
  have hg₀_meas : @Measurable Ω ℝ (futureSigmaAlgebra X t) inferInstance g₀ := by
    letI := futureSigmaAlgebra X t
    exact (hg_meas.add measurable_const).div_const 2
  have h_reduction := cov_affineReduction μ f₀ g₀ hf₀_int hg₀_int hfg₀_int
  have hf_eval : ∀ ω, 2 * f₀ ω - 1 = f ω := by intro ω; simp [f₀]; ring
  have hg_eval : ∀ ω, 2 * g₀ ω - 1 = g ω := by intro ω; simp [g₀]; ring
  simp_rw [hf_eval, hg_eval] at h_reduction
  rw [h_reduction, abs_mul, abs_of_pos (by positivity)]
  have h_pos_bound := cov_bound_nonneg_le_one μ X hX s t f₀ g₀
    hf₀_pos hf₀_le_one hg₀_pos hg₀_le_one hf₀_meas hg₀_meas
  linarith

/-! ### Stationarity and autocovariance -/

/-- A process is **covariance-stationary** if the cross-moment `E[X_t X_{t+h}]` depends
only on the lag `h` and not on the base time `t`. -/
def IsCovarianceStationary (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ t h : ℕ, ∫ ω, X t ω * X (t + h) ω ∂μ = ∫ ω, X 0 ω * X h ω ∂μ

/-- The autocovariance function of a real-valued process at lag `h`. -/
noncomputable def autocovariance (μ : Measure Ω) (X : ℕ → Ω → ℝ) (h : ℕ) : ℝ :=
  ∫ ω, X 0 ω * X h ω ∂μ

/-! ### Variance of the partial sum -/

/-- **Variance expansion.** For an L²-process,
`∫ (T⁻¹ ∑_t X_t)² dμ = T⁻² ∑_s ∑_t ∫ X_s X_t dμ`. -/
lemma variance_expansion (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (T : ℕ) (h_L2 : ∀ t, MemLp (X t) 2 μ) :
    ∫ ω, ((T : ℝ)⁻¹ * ∑ t : Fin T, X t.val ω)^2 ∂μ =
    (T : ℝ)⁻¹^2 * ∑ s : Fin T, ∑ t : Fin T, ∫ ω, X s.val ω * X t.val ω ∂μ := by
  have h_expand : (fun ω => ((T : ℝ)⁻¹ * ∑ t : Fin T, X t.val ω)^2) =
                  fun ω => (T : ℝ)⁻¹^2 * ∑ s : Fin T, ∑ t : Fin T, X s.val ω * X t.val ω := by
    ext ω
    have h_sum_sq : (∑ t : Fin T, X t.val ω)^2 = ∑ s : Fin T, ∑ t : Fin T, X s.val ω * X t.val ω :=
        by
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
    calc ((T : ℝ)⁻¹ * ∑ t : Fin T, X t.val ω)^2
      _ = ((T : ℝ)⁻¹)^2 * (∑ t : Fin T, X t.val ω)^2 := by ring
      _ = (T : ℝ)⁻¹^2 * ∑ s : Fin T, ∑ t : Fin T, X s.val ω * X t.val ω := by rw [h_sum_sq]
  rw [h_expand]
  rw [integral_const_mul]
  congr 1
  have h_int_st : ∀ s t : Fin T, Integrable (fun ω => X s.val ω * X t.val ω) μ := by
    intro s t
    exact MeasureTheory.MemLp.integrable_mul (h_L2 s.val) (h_L2 t.val)
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [integral_finset_sum]
    · intro t _
      exact h_int_st s t
  · intro s _
    apply integrable_finset_sum
    intro t _
    exact h_int_st s t

/-- Under covariance stationarity, each cross-moment is bounded by the absolute
autocovariance at the appropriate lag. -/
lemma stationarity_crossTerms (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (T : ℕ) (h_stat : IsCovarianceStationary μ X) (s t : Fin T) :
    ∫ ω, X s.val ω * X t.val ω ∂μ ≤ |autocovariance μ X (if s.val ≤
        t.val then t.val - s.val else s.val - t.val)| := by
  unfold autocovariance
  split_ifs with h
  · have h_eq : (fun ω => X s.val ω * X t.val ω) =
      fun ω => X s.val ω * X (s.val + (t.val - s.val)) ω := by
      ext ω; congr 2; omega
    rw [h_eq, h_stat s.val (t.val - s.val)]
    exact le_abs_self _
  · have h_eq : (fun ω => X s.val ω * X t.val ω) =
      fun ω => X t.val ω * X (t.val + (s.val - t.val)) ω := by
      ext ω; rw [mul_comm]; congr 2; omega
    rw [h_eq, h_stat t.val (s.val - t.val)]
    exact le_abs_self _

/-- **Double-sum bound.** For any non-negative summable function `f : ℕ → ℝ`,
`∑_s ∑_t f(|s - t|) ≤ T · (2 · ∑_h f(h))`. -/
lemma doubleSum_autocovariance_bound (T : ℕ) (f : ℕ → ℝ) (hf_pos : ∀ h, 0 ≤
    f h) (h_sum : Summable f) :
    (∑ s : Fin T, ∑ t : Fin T, f (if s.val ≤ t.val then t.val - s.val else s.val - t.val)) ≤
    (T : ℝ) * (2 * ∑' h, f h) := by
  have h_inner : ∀ s : Fin T, (∑ t : Fin T, f (if s.val ≤
      t.val then t.val - s.val else s.val - t.val)) ≤ 2 * ∑' h, f h := by
    intro s
    let S1 := (Finset.univ : Finset (Fin T)).filter (fun t => s.val ≤ t.val)
    let S2 := (Finset.univ : Finset (Fin T)).filter (fun t => ¬(s.val ≤ t.val))
    have h_sum_split : (∑ t : Fin T, f (if s.val ≤ t.val then t.val - s.val else s.val - t.val)) =
        (∑ t ∈ S1, f (t.val - s.val)) + (∑ t ∈ S2, f (s.val - t.val)) := by
      have H : (∑ t : Fin T, f (if s.val ≤ t.val then t.val - s.val else s.val - t.val)) =
               ∑ t : Fin T, (if s.val ≤ t.val then f (t.val - s.val) else f (s.val - t.val)) := by
        apply Finset.sum_congr rfl
        intro t _
        split_ifs <;> rfl
      rw [H, Finset.sum_ite]
    rw [h_sum_split]
    have h_inj1 : ∀ x ∈ S1, ∀ y ∈ S1, x.val - s.val = y.val - s.val → x = y := by
      intro x hx y hy heq
      rw [Finset.mem_filter] at hx hy
      have hval : x.val = y.val := by omega
      exact Fin.ext hval
    have h_sum1 : ∑ t ∈ S1, f (t.val - s.val) = ∑ h ∈ S1.image (fun t => t.val - s.val), f h := by
      exact Eq.symm (Finset.sum_image h_inj1)
    have h_bound1 : ∑ t ∈ S1, f (t.val - s.val) ≤ ∑' h, f h := by
      rw [h_sum1]
      exact Summable.sum_le_tsum (S1.image (fun t => t.val - s.val)) (fun _ _ => hf_pos _) h_sum
    have h_inj2 : ∀ x ∈ S2, ∀ y ∈ S2, s.val - x.val = s.val - y.val → x = y := by
      intro x hx y hy heq
      rw [Finset.mem_filter] at hx hy
      have hval : x.val = y.val := by omega
      exact Fin.ext hval
    have h_sum2 : ∑ t ∈ S2, f (s.val - t.val) = ∑ h ∈ S2.image (fun t => s.val - t.val), f h := by
      exact Eq.symm (Finset.sum_image h_inj2)
    have h_bound2 : ∑ t ∈ S2, f (s.val - t.val) ≤ ∑' h, f h := by
      rw [h_sum2]
      exact Summable.sum_le_tsum (S2.image (fun t => s.val - t.val)) (fun _ _ => hf_pos _) h_sum
    linarith
  have h_outer : (∑ s : Fin T, ∑ t : Fin T, f (if s.val ≤
      t.val then t.val - s.val else s.val - t.val)) ≤
                 ∑ s : Fin T, (2 * ∑' h, f h) := by
    apply Finset.sum_le_sum
    intro s _
    exact h_inner s
  have h_outer_eq : (∑ s : Fin T, (2 * ∑' h, f h)) = (T : ℝ) * (2 * ∑' h, f h) := by
    rw [Finset.sum_const]
    have h_card : (Finset.univ : Finset (Fin T)).card = T := by simp
    rw [h_card, nsmul_eq_mul]
  linarith

/-- **Variance bound under mixing.** The variance of the sample mean satisfies
`∫ (T⁻¹ ∑_t X_t)² dμ ≤ T⁻¹ · (2 · ∑_h |γ(h)|)`. -/
lemma partialSum_variance_mixing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (T : ℕ) (hT : 0 < (T : ℝ))
    (h_stat : IsCovarianceStationary μ X)
    (h_L2 : ∀ t, MemLp (X t) 2 μ)
    (h_sum : Summable (fun h => |autocovariance μ X h|)) :
    ∫ ω, ((T : ℝ)⁻¹ * ∑ t : Fin T, X t.val ω)^2 ∂μ ≤
    (T : ℝ)⁻¹ * (2 * ∑' h, |autocovariance μ X h|) := by
  rw [variance_expansion μ X T h_L2]
  have h_bound_cross : ∑ s : Fin T, ∑ t : Fin T, ∫ ω, X s.val ω * X t.val ω ∂μ ≤
      ∑ s : Fin T, ∑ t : Fin T, |autocovariance μ X (if s.val ≤
          t.val then t.val - s.val else s.val - t.val)| := by
    apply Finset.sum_le_sum; intro s _
    apply Finset.sum_le_sum; intro t _
    exact stationarity_crossTerms μ X T h_stat s t
  let f := fun h => |autocovariance μ X h|
  have hf_pos : ∀ h, 0 ≤ f h := fun h => abs_nonneg _
  have h_combo := doubleSum_autocovariance_bound T f hf_pos h_sum
  calc (T : ℝ)⁻¹^2 * ∑ s : Fin T, ∑ t : Fin T, ∫ ω, X s.val ω * X t.val ω ∂μ
    _ ≤ (T : ℝ)⁻¹^2 * ∑ s : Fin T, ∑ t : Fin T, f (if s.val ≤
        t.val then t.val - s.val else s.val - t.val) :=
            mul_le_mul_of_nonneg_left h_bound_cross (by positivity)
    _ ≤ (T : ℝ)⁻¹^2 * ((T : ℝ) * (2 * ∑' h, f h)) :=
        mul_le_mul_of_nonneg_left h_combo (by positivity)
    _ = ((T : ℝ)⁻¹^2 * (T : ℝ)) * (2 * ∑' h, f h) := by rw [mul_assoc]
    _ = (T : ℝ)⁻¹ * (2 * ∑' h, f h) := by
      congr 1
      have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT
      calc (T : ℝ)⁻¹^2 * (T : ℝ) = (T : ℝ)⁻¹ * (T : ℝ)⁻¹ * (T : ℝ) := by ring
      _ = (T : ℝ)⁻¹ * ((T : ℝ)⁻¹ * (T : ℝ)) := by rw [mul_assoc]
      _ = (T : ℝ)⁻¹ * 1 := by rw [inv_mul_cancel₀ hT_ne]
      _ = (T : ℝ)⁻¹ := mul_one _

/-! ### Law of Large Numbers -/

/-- **Law of Large Numbers for α-mixing processes.**

If `X` is covariance-stationary, square-integrable, and has an absolutely summable
autocovariance function, then the sample mean converges to zero in mean square:
`∫ (T⁻¹ ∑_{t<T} X_t)² dμ → 0` as `T → ∞`.

This is the core asymptotic result used to annihilate the spurious cross-terms in
causal panel methods with irrelevant donors. -/
theorem lln_alphaMixing (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_stat : IsCovarianceStationary μ X)
    (h_L2 : ∀ t, MemLp (X t) 2 μ)
    (h_sum : Summable (fun h => |autocovariance μ X h|)) :
    Tendsto (fun (T : ℕ) => ∫ ω, ((T : ℝ)⁻¹ * ∑ t : Fin T, X t.val ω)^2 ∂μ) atTop (nhds 0) := by
  let C := 2 * ∑' h, |autocovariance μ X h|
  have h_upper_lim : Tendsto (fun (T : ℕ) => (T : ℝ)⁻¹ * C) atTop (nhds 0) := by
    have h_eq : (fun (T : ℕ) => (T : ℝ)⁻¹ * C) = (fun (T : ℕ) => C * (T : ℝ)⁻¹) := by ext T; ring
    rw [h_eq]
    have h_zero : (0 : ℝ) = C * 0 := by ring
    rw [h_zero]
    exact Tendsto.const_mul C (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper_lim
  · apply Filter.Eventually.of_forall
    intro T
    apply integral_nonneg
    intro ω
    exact sq_nonneg _
  · have h_eventual_pos : ∀ᶠ (T : ℕ) in atTop, 0 < (T : ℝ) := by
      have h1 : ∀ᶠ (T : ℕ) in atTop, 1 ≤ T := Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩
      filter_upwards [h1] with T hT
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
    filter_upwards [h_eventual_pos] with T hT
    exact partialSum_variance_mixing μ X T hT h_stat h_L2 h_sum

end ProbabilityTheory
