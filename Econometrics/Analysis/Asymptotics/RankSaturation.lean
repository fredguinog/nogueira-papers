/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# Rank Saturation and Asymptotic Fraction Limits

This file defines a structure encoding the hypothesis that the rank of a
growing matrix saturates at a given fraction, and derives the corresponding
noise-trace fraction limit used in asymptotic OLS theory.

## Main definitions

* `AsymptoticRank.RankSaturationData` : encodes `s(T)/(T − r) → κ`.

## Main results

* `AsymptoticRank.RankSaturationData.kappa_nonneg` /
  `AsymptoticRank.RankSaturationData.kappa_le_one` :
  the saturation fraction lies in `[0, 1]`.
* `AsymptoticRank.tendsto_noise_trace_fraction` :
  `(T − s(T))/T → 1 − κ`.
-/

open Filter Topology

namespace AsymptoticRank

/-- The Rank Growth Hypothesis Structure.
Encodes the probabilistic rank growth result (e.g., from Marchenko–Pastur).
This postulates that the relevant rank fraction converges to `κ`. -/
structure RankSaturationData (r : ℕ) where
  s : ℕ → ℕ
  kappa : ℝ
  h_s_le : ∀ T, r < T → (s T : ℝ) ≤ (T : ℝ) - (r : ℝ)
  h_kappa_lim :
    Tendsto (fun (T : ℕ) => (s T : ℝ) / ((T : ℝ) - (r : ℝ)))
      atTop (nhds kappa)

/-- Any subspace saturation fraction limit must be non-negative. -/
lemma RankSaturationData.kappa_nonneg {r : ℕ}
    (rsd : RankSaturationData r) : 0 ≤ rsd.kappa := by
  apply ge_of_tendsto rsd.h_kappa_lim
  filter_upwards [eventually_gt_atTop r] with T hT
  have h_sub_pos : 0 < (T : ℝ) - (r : ℝ) :=
    sub_pos.mpr (by exact_mod_cast hT)
  exact div_nonneg (Nat.cast_nonneg _) h_sub_pos.le

/-- Any subspace saturation fraction limit cannot exceed 1. -/
lemma RankSaturationData.kappa_le_one {r : ℕ}
    (rsd : RankSaturationData r) : rsd.kappa ≤ 1 := by
  apply le_of_tendsto rsd.h_kappa_lim
  filter_upwards [eventually_gt_atTop r] with T hT
  have h_sub_pos : 0 < (T : ℝ) - (r : ℝ) :=
    sub_pos.mpr (by exact_mod_cast hT)
  exact (div_le_one₀ h_sub_pos).mpr (rsd.h_s_le T hT)

/-- `(T - r) / T` converges to `1`. -/
lemma tendsto_sub_div_self (r : ℕ) :
    Tendsto (fun (T : ℕ) => ((T : ℝ) - (r : ℝ)) / (T : ℝ))
      atTop (nhds 1) := by
  have h_eq :
      (fun (T : ℕ) => ((T : ℝ) - (r : ℝ)) / (T : ℝ)) =ᶠ[atTop]
        (fun T => 1 - (r : ℝ) * (T : ℝ)⁻¹) := by
    filter_upwards [eventually_ne_atTop 0] with T hT
    have hT_real : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    calc ((T : ℝ) - (r : ℝ)) / (T : ℝ)
      _ = (T : ℝ) / (T : ℝ) - (r : ℝ) / (T : ℝ) := sub_div _ _ _
      _ = 1 - (r : ℝ) / (T : ℝ) := by rw [div_self hT_real]
      _ = 1 - (r : ℝ) * (T : ℝ)⁻¹ := by rw [div_eq_mul_inv]
  have h_inv : Tendsto (fun (T : ℕ) => (T : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h_zero :
      Tendsto (fun (T : ℕ) => (r : ℝ) * (T : ℝ)⁻¹)
        atTop (nhds 0) := by
    have := Tendsto.const_mul (r : ℝ) h_inv
    simp only [mul_zero] at this
    exact this
  have h_const :
      Tendsto (fun (_ : ℕ) => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h_one := Tendsto.sub h_const h_zero
  simp only [sub_zero] at h_one
  exact Tendsto.congr' h_eq.symm h_one

/-- Given `s(T)/(T-r) → κ`, we have `(T - s(T))/T → 1 - κ`.
This provides the exact scaling factor for the noise trace limit. -/
lemma tendsto_noise_trace_fraction {r : ℕ}
    (rsd : RankSaturationData r) :
    Tendsto (fun (T : ℕ) => ((T : ℝ) - (rsd.s T : ℝ)) / (T : ℝ))
      atTop (nhds (1 - rsd.kappa)) := by
  -- Step 1: Prove s(T)/T → κ
  have h_s_div_T :
      Tendsto (fun (T : ℕ) => (rsd.s T : ℝ) / (T : ℝ))
        atTop (nhds rsd.kappa) := by
    have h_eq2 :
        (fun (T : ℕ) => (rsd.s T : ℝ) / (T : ℝ)) =ᶠ[atTop]
          (fun T => ((rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ))) *
            (((T : ℝ) - (r : ℝ)) / (T : ℝ))) := by
      filter_upwards [eventually_gt_atTop r] with T hT
      have h_sub : (T : ℝ) - (r : ℝ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt hT))
      have h1 :
          ((rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ))) *
            ((T : ℝ) - (r : ℝ)) = (rsd.s T : ℝ) :=
        div_mul_cancel₀ _ h_sub
      calc (rsd.s T : ℝ) / (T : ℝ)
        _ = (((rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ))) *
              ((T : ℝ) - (r : ℝ))) / (T : ℝ) := by rw [h1]
        _ = ((rsd.s T : ℝ) / ((T : ℝ) - (r : ℝ))) *
              (((T : ℝ) - (r : ℝ)) / (T : ℝ)) := by
            rw [mul_div_assoc]
    have h_lim :=
      Tendsto.mul rsd.h_kappa_lim (tendsto_sub_div_self r)
    rw [mul_one] at h_lim
    exact Tendsto.congr' h_eq2.symm h_lim
  -- Step 2: (T - s(T))/T = 1 - s(T)/T → 1 - κ
  have h_eq :
      (fun (T : ℕ) => ((T : ℝ) - (rsd.s T : ℝ)) / (T : ℝ))
        =ᶠ[atTop]
      (fun T => 1 - (rsd.s T : ℝ) / (T : ℝ)) := by
    filter_upwards [eventually_ne_atTop 0] with T hT
    have hT_real : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    calc ((T : ℝ) - (rsd.s T : ℝ)) / (T : ℝ)
      _ = (T : ℝ) / (T : ℝ) - (rsd.s T : ℝ) / (T : ℝ) :=
          sub_div _ _ _
      _ = 1 - (rsd.s T : ℝ) / (T : ℝ) := by
          rw [div_self hT_real]
  have h_const :
      Tendsto (fun (_ : ℕ) => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have h_final := Tendsto.sub h_const h_s_div_T
  exact Tendsto.congr' h_eq.symm h_final

end AsymptoticRank
