/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.LinearAlgebra.Matrix.Norms

/-!
# Algebra of Convergence in Measure

This file develops the basic algebra of scalar convergence in measure:
addition, multiplication by constants, constant sequences, finite sums,
products of convergent sequences, and generic squeeze/domination lemmas
used in asymptotic probability theory.

## Main results

### Core algebra
* `tendstoInMeasure_scalar_add` : sums converge in measure.
* `tendstoInMeasure_scalar_mul_const` : multiplication by a constant.
* `tendstoInMeasure_const_scalar_mul` : left-multiplication by a constant.
* `tendstoInMeasure_const` : constant sequences converge trivially.
* `tendstoInMeasure_scalar_sum` : finite sums converge in measure.
* `tendstoInMeasure_cross_term` : products of oₚ(1) terms.
* `tendstoInMeasure_scalar_mul_varying` : products of convergent
  sequences.

### Generic tools
* `tendstoInMeasure_add_zero` : sum of oₚ(1) terms is oₚ(1).
* `tendstoInMeasure_mul_const_zero` : constant × oₚ(1) is oₚ(1).
* `tendstoInMeasure_squeeze_le_one` : oₚ(1) × [bounded by 1] = oₚ(1).
* `tendstoInMeasure_squeeze_sq` : if f² ≤ g →ₚ 0 then f →ₚ 0.
* `tendstoInMeasure_abs_sub` : f →ₚ L implies |f − L| →ₚ 0.
* `tendstoInMeasure_eventually_dominated` : monotone squeeze.
* `tendstoInMeasure_cauchy_schwarz` : Cauchy–Schwarz for convergence
  in probability.
* `deterministic_tendstoInMeasure` : deterministic limits lift to
  convergence in probability.
-/

open MeasureTheory Filter Topology Matrix

namespace MeasureTheory

/-! ### ENNReal distance helper -/

/-- The extended distance of scaled reals factors through `|c|`. -/
lemma edist_mul_right_ennreal (x y c : ℝ) :
    edist (x * c) (y * c) =
      ENNReal.ofReal |c| * edist x y := by
  simp only [edist_dist, Real.dist_eq]
  rw [show x * c - y * c = (x - y) * c by ring]
  rw [abs_mul]
  rw [show |x - y| * |c| = |c| * |x - y| by ring]
  rw [ENNReal.ofReal_mul (abs_nonneg c)]

/-! ### Addition -/

/-- Sums of convergent-in-measure sequences converge in measure. -/
lemma tendstoInMeasure_scalar_add {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => a))
    (hg : TendstoInMeasure μ g atTop (fun _ => b)) :
    TendstoInMeasure μ (fun T ω => f T ω + g T ω)
      atTop (fun _ => a + b) := by
  intro ε hε
  have hε2 : (0 : ENNReal) < ε / 2 :=
    ENNReal.half_pos hε.ne'
  have hS : ∀ T,
      {ω : Ω | ε ≤ edist (f T ω + g T ω) (a + b)} ⊆
        {ω : Ω | ε / 2 ≤ edist (f T ω) a} ∪
        {ω : Ω | ε / 2 ≤ edist (g T ω) b} := by
    intro T ω hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    have hf' := h.1
    have hg' := h.2
    have htri :
        edist (f T ω + g T ω) (a + b) ≤
          edist (f T ω) a + edist (g T ω) b :=
      calc edist (f T ω + g T ω) (a + b)
          ≤ edist (f T ω + g T ω) (a + g T ω) +
            edist (a + g T ω) (a + b) :=
            edist_triangle _ _ _
        _ = edist (f T ω) a + edist (g T ω) b := by
            rw [edist_add_right, edist_add_left]
    have hlt :
        edist (f T ω) a + edist (g T ω) b < ε :=
      calc edist (f T ω) a + edist (g T ω) b
          < ε / 2 + ε / 2 :=
            ENNReal.add_lt_add hf' hg'
        _ = ε := ENNReal.add_halves ε
    exact absurd (lt_of_le_of_lt htri hlt)
      (not_lt.mpr (Set.mem_setOf.mp hω))
  have hbound : ∀ T,
      μ {ω : Ω | ε ≤ edist (f T ω + g T ω) (a + b)} ≤
        μ {ω : Ω | ε / 2 ≤ edist (f T ω) a} +
        μ {ω : Ω | ε / 2 ≤ edist (g T ω) b} :=
    fun T => (measure_mono (hS T)).trans
      (measure_union_le _ _)
  have hsum : Tendsto (fun T =>
      μ {ω : Ω | ε / 2 ≤ edist (f T ω) a} +
      μ {ω : Ω | ε / 2 ≤ edist (g T ω) b})
      atTop (𝓝 0) := by
    have h := (hf (ε / 2) hε2).add (hg (ε / 2) hε2)
    simp only [add_zero] at h
    exact h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T; exact hbound T

/-! ### Scalar multiplication -/

/-- Right-multiplication by a constant preserves convergence in
measure. -/
lemma tendstoInMeasure_scalar_mul_const {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ)
    {f : ℕ → Ω → ℝ} {L : ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => L)) :
    TendstoInMeasure μ (fun T ω => f T ω * c)
      atTop (fun _ => L * c) := by
  rcases eq_or_ne c 0 with rfl | hc
  · intro ε hε
    have hempty : ∀ T,
        {ω : Ω | ε ≤ edist (f T ω * (0 : ℝ))
          (L * (0 : ℝ))} = ∅ := by
      intro T; ext ω
      simp only [mul_zero, edist_self, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    simp_rw [hempty, measure_empty]
    exact tendsto_const_nhds
  · have hcpos : (0 : ENNReal) < ENNReal.ofReal |c| :=
      ENNReal.ofReal_pos.mpr (abs_pos.mpr hc)
    intro ε hε
    have hc_ne : ENNReal.ofReal |c| ≠ 0 := hcpos.ne'
    have hc_top : ENNReal.ofReal |c| ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hε' : (0 : ENNReal) < ε / ENNReal.ofReal |c| :=
      ENNReal.div_pos hε.ne' hc_top
    have hS : ∀ T,
        {ω : Ω | ε ≤ edist (f T ω * c) (L * c)} ⊆
        {ω : Ω | ε / ENNReal.ofReal |c| ≤
          edist (f T ω) L} := by
      intro T ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [edist_mul_right_ennreal] at hω
      rw [ENNReal.div_le_iff_le_mul (Or.inl hc_ne)
        (Or.inl hc_top), mul_comm]
      exact hω
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds
      (hf (ε / ENNReal.ofReal |c|) hε')
    · filter_upwards with T; exact zero_le _
    · filter_upwards with T; exact measure_mono (hS T)

/-- Left-multiplication by a constant preserves convergence in
measure. -/
lemma tendstoInMeasure_const_scalar_mul {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ)
    {f : ℕ → Ω → ℝ} {L : ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => L)) :
    TendstoInMeasure μ (fun T ω => c * f T ω)
      atTop (fun _ => c * L) := by
  have heq : (fun T ω => c * f T ω) =
      (fun T ω => f T ω * c) := by funext T ω; ring
  have hLeq : (fun (_ : Ω) => c * L) =
      (fun _ => L * c) := by funext; ring
  rw [heq, hLeq]
  exact tendstoInMeasure_scalar_mul_const μ c hf

/-! ### Constant sequences -/

/-- A constant sequence converges in measure to its value. -/
lemma tendstoInMeasure_const {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ) :
    TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => c)
      atTop (fun _ => c) := by
  intro ε hε
  have hempty : {ω : Ω | ε ≤ edist c c} = ∅ := by
    ext ω
    simp only [edist_self, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  have h_eq : (fun (T : ℕ) =>
      μ {ω : Ω | ε ≤ edist c c}) = fun _ => 0 := by
    funext T; rw [hempty, measure_empty]
  rw [h_eq]
  exact tendsto_const_nhds

/-! ### Finite sums -/

/-- Finite sums of convergent-in-measure sequences converge in
measure. -/
lemma tendstoInMeasure_scalar_sum {ι : Type*}
    [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι)
    (f : ι → ℕ → Ω → ℝ) (g : ι → ℝ)
    (h : ∀ k ∈ s, TendstoInMeasure μ (f k) atTop
      (fun _ => g k)) :
    TendstoInMeasure μ (fun T ω => ∑ k ∈ s, f k T ω)
      atTop (fun _ => ∑ k ∈ s, g k) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro ε hε
    dsimp only
    have hempty :
        {ω : Ω | ε ≤ edist (0 : ℝ) 0} = ∅ := by
      ext ω
      simp only [edist_self, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      exact hε
    have h_eq : (fun (T : ℕ) =>
        μ {ω : Ω | ε ≤ edist (0 : ℝ) 0}) =
        fun _ => 0 := by
      funext T; rw [hempty, measure_empty]
    rw [h_eq]; exact tendsto_const_nhds
  | @insert a s' ha ih =>
    simp only [Finset.sum_insert ha]
    apply tendstoInMeasure_scalar_add
    · exact h a (Finset.mem_insert_self a s')
    · exact ih (fun k hk =>
        h k (Finset.mem_insert_of_mem hk))

/-! ### Products of convergent sequences -/

/-- The product of two oₚ(1) sequences is oₚ(1). -/
lemma tendstoInMeasure_cross_term {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0))
    (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun T ω => f T ω * g T ω)
      atTop (fun _ => 0) := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · have hempty : ∀ T,
        {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T ω * g T ω) 0} = ∅ :=
      fun T => Set.eq_empty_of_forall_notMem
        (fun ω hω => (edist_lt_top _ _).not_ge hω)
    have h_eq : (fun (T : ℕ) =>
        μ {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T ω * g T ω) 0}) =
        fun _ => 0 := by
      funext T; rw [hempty, measure_empty]
    rw [h_eq]; exact tendsto_const_nhds
  have hε_real : 0 < ε.toReal :=
    ENNReal.toReal_pos hε.ne' hε_top
  have hsqrt_pos : 0 < Real.sqrt ε.toReal :=
    Real.sqrt_pos_of_pos hε_real
  set δ := ENNReal.ofReal (Real.sqrt ε.toReal)
    with hδ_def
  have hδ_pos : 0 < δ :=
    ENNReal.ofReal_pos.mpr hsqrt_pos
  have hS : ∀ T,
      {ω : Ω | ε ≤ edist (f T ω * g T ω) 0} ⊆
        {ω : Ω | δ ≤ edist (f T ω) 0} ∪
        {ω : Ω | δ ≤ edist (g T ω) 0} := by
    intro T ω hω
    simp only [edist_dist, Real.dist_eq, sub_zero,
      Set.mem_union, Set.mem_setOf_eq] at *
    by_contra hlt; push_neg at hlt
    obtain ⟨hf_lt, hg_lt⟩ := hlt
    have hfabs : |f T ω| < Real.sqrt ε.toReal := by
      rwa [hδ_def,
        ENNReal.ofReal_lt_ofReal_iff hsqrt_pos]
        at hf_lt
    have hgabs : |g T ω| < Real.sqrt ε.toReal := by
      rwa [hδ_def,
        ENNReal.ofReal_lt_ofReal_iff hsqrt_pos]
        at hg_lt
    have hprod : |f T ω * g T ω| < ε.toReal := by
      rw [abs_mul]
      calc |f T ω| * |g T ω|
          < Real.sqrt ε.toReal *
            Real.sqrt ε.toReal :=
            mul_lt_mul'' hfabs hgabs
              (abs_nonneg _) (abs_nonneg _)
        _ = ε.toReal :=
            Real.mul_self_sqrt hε_real.le
    have hlt_ε :
        ENNReal.ofReal |f T ω * g T ω| < ε := by
      calc ENNReal.ofReal |f T ω * g T ω|
          < ENNReal.ofReal ε.toReal :=
            (ENNReal.ofReal_lt_ofReal_iff
              hε_real).mpr hprod
        _ = ε := ENNReal.ofReal_toReal hε_top
    exact absurd hω (not_le.mpr hlt_ε)
  have hbound : ∀ T,
      μ {ω : Ω | ε ≤ edist (f T ω * g T ω) 0} ≤
        μ {ω : Ω | δ ≤ edist (f T ω) 0} +
        μ {ω : Ω | δ ≤ edist (g T ω) 0} :=
    fun T => (measure_mono (hS T)).trans
      (measure_union_le _ _)
  have hsum : Tendsto (fun T =>
      μ {ω : Ω | δ ≤ edist (f T ω) 0} +
      μ {ω : Ω | δ ≤ edist (g T ω) 0})
      atTop (𝓝 0) := by
    have h := (hf δ hδ_pos).add (hg δ hδ_pos)
    simp only [add_zero] at h; exact h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T; exact hbound T

/-- Products of convergent-in-measure sequences converge in
measure. -/
lemma tendstoInMeasure_scalar_mul_varying {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ} {a b : ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => a))
    (hg : TendstoInMeasure μ g atTop (fun _ => b)) :
    TendstoInMeasure μ (fun T ω => f T ω * g T ω)
      atTop (fun _ => a * b) := by
  have hf0 : TendstoInMeasure μ
      (fun T ω => f T ω - a) atTop (fun _ => 0) := by
    have heq1 : (fun T ω => f T ω - a) =
        (fun T ω => f T ω + (-a)) := by
      funext T ω; ring
    have heq2 : (fun (_ : Ω) => (0 : ℝ)) =
        fun _ => a + (-a) := by funext; ring
    rw [heq1, heq2]
    apply tendstoInMeasure_scalar_add μ hf
    have hca : TendstoInMeasure μ
        (fun (_ : ℕ) (_ : Ω) => -a) atTop
        (fun _ => -a) :=
      tendstoInMeasure_const μ (-a)
    have := tendstoInMeasure_scalar_mul_const μ 1 hca
    simp only [mul_one] at this
    exact this
  have hg0 : TendstoInMeasure μ
      (fun T ω => g T ω - b) atTop (fun _ => 0) := by
    have heq1 : (fun T ω => g T ω - b) =
        (fun T ω => g T ω + (-b)) := by
      funext T ω; ring
    have heq2 : (fun (_ : Ω) => (0 : ℝ)) =
        fun _ => b + (-b) := by funext; ring
    rw [heq1, heq2]
    apply tendstoInMeasure_scalar_add μ hg
    have hcb : TendstoInMeasure μ
        (fun (_ : ℕ) (_ : Ω) => -b) atTop
        (fun _ => -b) :=
      tendstoInMeasure_const μ (-b)
    have := tendstoInMeasure_scalar_mul_const μ 1 hcb
    simp only [mul_one] at this
    exact this
  have hcross :=
    tendstoInMeasure_cross_term μ hf0 hg0
  have hterm1 : TendstoInMeasure μ
      (fun T ω => a * (g T ω - b)) atTop
      (fun _ => 0) := by
    have h :=
      tendstoInMeasure_const_scalar_mul μ a hg0
    simp only [mul_zero] at h; exact h
  have hterm2 : TendstoInMeasure μ
      (fun T ω => b * (f T ω - a)) atTop
      (fun _ => 0) := by
    have h :=
      tendstoInMeasure_const_scalar_mul μ b hf0
    simp only [mul_zero] at h; exact h
  have hinner : TendstoInMeasure μ
      (fun T ω => a * (g T ω - b) +
        b * (f T ω - a)) atTop (fun _ => 0) := by
    have h :=
      tendstoInMeasure_scalar_add μ hterm1 hterm2
    simp only [add_zero] at h; exact h
  have houter : TendstoInMeasure μ
      (fun T ω => a * (g T ω - b) +
        b * (f T ω - a) +
        (f T ω - a) * (g T ω - b))
      atTop (fun _ => 0) := by
    have h :=
      tendstoInMeasure_scalar_add μ hinner hcross
    simp only [add_zero] at h; exact h
  have hconst : TendstoInMeasure μ
      (fun (_ : ℕ) (_ : Ω) => a * b) atTop
      (fun _ => a * b) :=
    tendstoInMeasure_const μ (a * b)
  have hfinal :=
    tendstoInMeasure_scalar_add μ hconst houter
  simp only [add_zero] at hfinal
  have heq : (fun T ω => f T ω * g T ω) =
      (fun T ω => a * b +
        (a * (g T ω - b) + b * (f T ω - a) +
          (f T ω - a) * (g T ω - b))) := by
    funext T ω; ring
  rw [heq]
  exact hfinal

/-! ### Sum of oₚ(1) terms -/

/-- The sum of two oₚ(1) sequences is oₚ(1). -/
lemma tendstoInMeasure_add_zero {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0))
    (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun T ω => f T ω + g T ω)
      atTop (fun _ => 0) := by
  have h := tendstoInMeasure_scalar_add μ hf hg
  simp only [add_zero] at h; exact h

/-! ### Constant times oₚ(1) -/

/-- A constant times an oₚ(1) sequence is oₚ(1). -/
lemma tendstoInMeasure_mul_const_zero {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0))
    (c : ℝ) :
    TendstoInMeasure μ (fun (T : ℕ) ω => c * f T ω)
      atTop (fun _ => 0) := by
  have h :=
    tendstoInMeasure_const_scalar_mul μ c hf
  simp only [mul_zero] at h; exact h

/-! ### Squeeze lemmas -/

/-- oₚ(1) times a sequence bounded by 1 is oₚ(1). -/
lemma tendstoInMeasure_squeeze_le_one {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ}
    (hf : TendstoInMeasure μ f atTop (fun _ => 0))
    (hg_bound : ∀ T ω, |g T ω| ≤ 1) :
    TendstoInMeasure μ (fun T ω => f T ω * g T ω)
      atTop (fun _ => 0) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (hf ε hε)
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T
    apply measure_mono
    intro ω hω
    simp only [edist_dist, Real.dist_eq, sub_zero,
      Set.mem_setOf_eq] at hω ⊢
    have h_abs : |f T ω * g T ω| ≤ |f T ω| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (hg_bound T ω)
    exact le_trans hω
      (ENNReal.ofReal_le_ofReal h_abs)

/-- If `f² ≤ g` and `g →ₚ 0`, then `f →ₚ 0`. -/
lemma tendstoInMeasure_squeeze_sq {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ}
    (hg : TendstoInMeasure μ g atTop (fun _ => 0))
    (h_bound : ∀ T ω, (f T ω) ^ 2 ≤ g T ω) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | htop
  · have hempty : ∀ T,
        {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T ω) 0} = ∅ :=
      fun T => Set.eq_empty_of_forall_notMem
        (fun ω hw =>
          (edist_lt_top _ _).not_ge hw)
    have heq : (fun T =>
        μ {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T ω) 0}) = fun _ => 0 := by
      funext T; rw [hempty T, measure_empty]
    rw [heq]; exact tendsto_const_nhds
  have hε_pos : 0 < ε.toReal :=
    ENNReal.toReal_pos hε.ne' htop
  have hε_sq_pos : 0 < ε.toReal ^ 2 :=
    pow_pos hε_pos 2
  have hε_sq_enn :
      (0 : ENNReal) < ENNReal.ofReal (ε.toReal ^ 2) :=
    ENNReal.ofReal_pos.mpr hε_sq_pos
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (hg (ENNReal.ofReal (ε.toReal ^ 2)) hε_sq_enn)
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq, edist_dist,
      Real.dist_eq, sub_zero] at hω ⊢
    have h1 : ε.toReal ≤ |f T ω| := by
      have h_rw : ε = ENNReal.ofReal ε.toReal :=
        (ENNReal.ofReal_toReal htop).symm
      rw [h_rw] at hω
      exact (ENNReal.ofReal_le_ofReal_iff
        (abs_nonneg _)).mp hω
    have h2 : ε.toReal ^ 2 ≤ |f T ω| ^ 2 := by
      calc ε.toReal ^ 2
          = ε.toReal * ε.toReal := by ring
        _ ≤ |f T ω| * |f T ω| :=
            mul_le_mul h1 h1 hε_pos.le
              (abs_nonneg _)
        _ = |f T ω| ^ 2 := by ring
    have h3 : |f T ω| ^ 2 = (f T ω) ^ 2 :=
      sq_abs (f T ω)
    rw [h3] at h2
    have h4 : ε.toReal ^ 2 ≤ g T ω :=
      le_trans h2 (h_bound T ω)
    have h5 : ε.toReal ^ 2 ≤ |g T ω| :=
      le_trans h4 (le_abs_self _)
    exact (ENNReal.ofReal_le_ofReal_iff
      (abs_nonneg _)).mpr h5

/-! ### Absolute-value and domination helpers -/

/-- If `f →ₚ L` then `|f − L| →ₚ 0`. -/
lemma tendstoInMeasure_abs_sub {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → Ω → ℝ} {L : ℝ}
    (hf : TendstoInMeasure μ f atTop
      (fun _ => L)) :
    TendstoInMeasure μ
      (fun T ω => |f T ω - L|)
      atTop (fun _ => 0) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (hf ε hε)
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq, edist_dist,
      Real.dist_eq, sub_zero, abs_abs] at *
    exact hω

/-- Monotone squeeze for convergence in measure: if `0 ≤ f ≤ g`
eventually and `g →ₚ 0`, then `f →ₚ 0`. -/
lemma tendstoInMeasure_eventually_dominated
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : ℕ → Ω → ℝ}
    (hf_nn : ∀ T ω, 0 ≤ f T ω)
    (hg_nn : ∀ T ω, 0 ≤ g T ω)
    (hbound : ∀ᶠ T in atTop, ∀ ω, f T ω ≤ g T ω)
    (hg : TendstoInMeasure μ g atTop
      (fun _ => 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    Filter.eventually_atTop.mp hbound
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (hg ε hε)
  · filter_upwards with T; exact zero_le _
  · filter_upwards [Filter.eventually_ge_atTop T₀]
      with T hT
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq, edist_dist,
      Real.dist_eq, sub_zero] at hω ⊢
    rw [abs_of_nonneg (hf_nn T ω)] at hω
    rw [abs_of_nonneg (hg_nn T ω)]
    exact le_trans hω
      (ENNReal.ofReal_le_ofReal (hT₀ T hT ω))

/-! ### Cauchy–Schwarz for convergence in probability -/

/-- If `T⁻¹‖v‖² →ₚ L` and `T⁻¹‖w‖² →ₚ 0`, then
`T⁻¹ v'w →ₚ 0`. -/
lemma tendstoInMeasure_cauchy_schwarz
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (v w : ∀ T, Ω → Matrix (Fin T) (Fin 1) ℝ)
    (L_v : ℝ)
    (hv : TendstoInMeasure μ
      (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (v T ω))
      atTop (fun _ => L_v))
    (hw : TendstoInMeasure μ
      (fun (T : ℕ) ω => (T : ℝ)⁻¹ * sqNorm (w T ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun (T : ℕ) ω => (T : ℝ)⁻¹ *
        ((v T ω)ᵀ * w T ω) 0 0)
      atTop (fun _ => 0) := by
  have hg : TendstoInMeasure μ
      (fun (T : ℕ) ω =>
        ((T : ℝ)⁻¹ * sqNorm (v T ω)) *
        ((T : ℝ)⁻¹ * sqNorm (w T ω)))
      atTop (fun _ => L_v * 0) :=
    tendstoInMeasure_scalar_mul_varying μ hv hw
  have hg_zero : TendstoInMeasure μ
      (fun (T : ℕ) ω =>
        ((T : ℝ)⁻¹ * sqNorm (v T ω)) *
        ((T : ℝ)⁻¹ * sqNorm (w T ω)))
      atTop (fun _ => 0) := by
    have h_rw : L_v * 0 = 0 := mul_zero L_v
    rw [h_rw] at hg; exact hg
  apply tendstoInMeasure_squeeze_sq μ hg_zero
  intro T ω
  have h_cs :=
    inner_sq_le_sqNorm_mul (v T ω) (w T ω)
  calc ((T : ℝ)⁻¹ *
      ((v T ω)ᵀ * w T ω) 0 0) ^ 2
    _ = (T : ℝ)⁻¹ ^ 2 *
        (((v T ω)ᵀ * w T ω) 0 0) ^ 2 := by ring
    _ ≤ (T : ℝ)⁻¹ ^ 2 *
        (sqNorm (v T ω) * sqNorm (w T ω)) :=
        mul_le_mul_of_nonneg_left h_cs
          (sq_nonneg _)
    _ = ((T : ℝ)⁻¹ * sqNorm (v T ω)) *
        ((T : ℝ)⁻¹ * sqNorm (w T ω)) := by ring

/-! ### Deterministic convergence -/

/-- A deterministic limit lifts to convergence in probability. -/
lemma deterministic_tendstoInMeasure {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {f : ℕ → ℝ} {L : ℝ}
    (h : Tendsto f atTop (nhds L)) :
    TendstoInMeasure μ (fun T _ => f T) atTop
      (fun _ => L) := by
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | htop
  · have hempty : ∀ T,
        {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T) L} = ∅ :=
      fun T => Set.eq_empty_of_forall_notMem
        (fun ω hw =>
          (edist_lt_top _ _).not_ge hw)
    have heq : (fun T =>
        μ {ω : Ω | (⊤ : ENNReal) ≤
          edist (f T) L}) = fun _ => 0 := by
      funext T; rw [hempty, measure_empty]
    rw [heq]; exact tendsto_const_nhds
  · have h_pos : 0 < ε.toReal :=
      ENNReal.toReal_pos hε.ne' htop
    have h_eventual :
        ∀ᶠ T in atTop, dist (f T) L < ε.toReal :=
      Metric.tendsto_nhds.mp h ε.toReal h_pos
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds tendsto_const_nhds
    · filter_upwards with T; exact zero_le _
    · filter_upwards [h_eventual] with T hT
      have hempty :
          {ω : Ω | ε ≤ edist (f T) L} = ∅ := by
        ext ω
        simp only [Set.mem_empty_iff_false,
          iff_false, Set.mem_setOf_eq, not_le]
        rw [edist_dist]
        have heq_eps :
            ENNReal.ofReal ε.toReal = ε :=
          ENNReal.ofReal_toReal htop
        rw [← heq_eps]
        exact (ENNReal.ofReal_lt_ofReal_iff
          h_pos).mpr hT
      rw [hempty, measure_empty]

end MeasureTheory
