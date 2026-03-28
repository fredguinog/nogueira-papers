/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.Probability.ConvergenceInMeasure
import Econometrics.LinearAlgebra.Matrix.MoorePenrose

/-!
# Matrix-Valued Convergence in Probability

This file defines entrywise convergence in probability for
matrix-valued random variables and establishes an algebra of limits:
addition, subtraction, multiplication, transposition, inversion,
Moore–Penrose pseudoinversion, and eventual-equality transfer.

## Main definitions

* `MatrixLimitInProb` : entrywise convergence in measure for matrix
  sequences.

## Main results

* `MatrixLimitInProb.add` / `.sub` : sums and differences converge.
* `MatrixLimitInProb.mul` / `.mul_left` / `.mul_right` : products
  converge.
* `MatrixLimitInProb.transpose` : transposes converge.
* `MatrixLimitInProb.inv` : inverses converge when the limit is
  nonsingular.
* `MatrixLimitInProb.pinv` : pseudoinverses converge when the limit
  is nonsingular.
* `MatrixLimitInProb.congr` : convergence transfers across eventually
  equal sequences.
-/

open Matrix MeasureTheory Filter Topology ProbabilityTheory

namespace ProbabilityTheory

/-- Entrywise convergence in measure for matrix-valued random
variables. -/
def MatrixLimitInProb {n m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ)
    (L : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ i j, TendstoInMeasure μ
    (fun T ω => A T ω i j) atTop (fun _ => L i j)

/-! ### Constant sequences -/

/-- A constant matrix sequence converges in probability to its
value. -/
lemma MatrixLimitInProb.const {n m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    (C : Matrix (Fin n) (Fin m) ℝ) :
    MatrixLimitInProb μ (fun _ _ => C) C := by
  intro i j ε hε
  have hempty :
      {ω : Ω | ε ≤ edist (C i j) (C i j)} = ∅ := by
    ext ω
    simp only [edist_self, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_le]
    exact hε
  have h_eq : (fun (T : ℕ) =>
      μ {ω : Ω | ε ≤ edist (C i j) (C i j)}) =
      fun _ => 0 := by
    funext T; rw [hempty, measure_empty]
  rw [h_eq]
  exact tendsto_const_nhds

/-! ### Addition and subtraction -/

/-- Sums of convergent matrix sequences converge entrywise. -/
lemma MatrixLimitInProb.add {n m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {A B : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ}
    {L_A L_B : Matrix (Fin n) (Fin m) ℝ}
    (hA : MatrixLimitInProb μ A L_A)
    (hB : MatrixLimitInProb μ B L_B) :
    MatrixLimitInProb μ
      (fun T ω => A T ω + B T ω) (L_A + L_B) := by
  intro i j ε hε
  have heq : ∀ T ω,
      (A T ω + B T ω) i j =
        A T ω i j + B T ω i j :=
    fun T ω => rfl
  simp_rw [heq, Matrix.add_apply]
  exact tendstoInMeasure_scalar_add μ
    (hA i j) (hB i j) ε hε

/-- Differences of convergent matrix sequences converge
entrywise. -/
lemma MatrixLimitInProb.sub {n m : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {A B : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ}
    {L_A L_B : Matrix (Fin n) (Fin m) ℝ}
    (hA : MatrixLimitInProb μ A L_A)
    (hB : MatrixLimitInProb μ B L_B) :
    MatrixLimitInProb μ
      (fun T ω => A T ω - B T ω)
      (L_A - L_B) := by
  intro i j ε hε
  have hε2 : (0 : ENNReal) < ε / 2 :=
    ENNReal.half_pos hε.ne'
  have hS : ∀ T,
      {ω : Ω | ε ≤ edist
        ((A T ω - B T ω) i j)
        ((L_A - L_B) i j)} ⊆
      {ω : Ω | ε / 2 ≤
        edist (A T ω i j) (L_A i j)} ∪
      {ω : Ω | ε / 2 ≤
        edist (B T ω i j) (L_B i j)} := by
    intro T ω hω
    simp only [Matrix.sub_apply] at hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_contra hc; push_neg at hc
    have htri :
        edist (A T ω i j - B T ω i j)
          (L_A i j - L_B i j) ≤
        edist (A T ω i j) (L_A i j) +
          edist (B T ω i j) (L_B i j) :=
      calc edist (A T ω i j - B T ω i j)
            (L_A i j - L_B i j)
          ≤ edist (A T ω i j - B T ω i j)
              (L_A i j - B T ω i j) +
            edist (L_A i j - B T ω i j)
              (L_A i j - L_B i j) :=
            edist_triangle _ _ _
        _ = edist (A T ω i j) (L_A i j) +
            edist (B T ω i j) (L_B i j) := by
            rw [edist_sub_right, edist_sub_left]
    have hlt :
        edist (A T ω i j) (L_A i j) +
          edist (B T ω i j) (L_B i j) < ε :=
      calc edist (A T ω i j) (L_A i j) +
            edist (B T ω i j) (L_B i j)
          < ε / 2 + ε / 2 :=
            ENNReal.add_lt_add hc.1 hc.2
        _ = ε := ENNReal.add_halves ε
    exact absurd (lt_of_le_of_lt htri hlt)
      (not_lt.mpr (Set.mem_setOf.mp hω))
  have hbound : ∀ T,
      μ {ω : Ω | ε ≤ edist
        ((A T ω - B T ω) i j)
        ((L_A - L_B) i j)} ≤
      μ {ω : Ω | ε / 2 ≤
        edist (A T ω i j) (L_A i j)} +
      μ {ω : Ω | ε / 2 ≤
        edist (B T ω i j) (L_B i j)} :=
    fun T => (measure_mono (hS T)).trans
      (measure_union_le _ _)
  have hsum : Tendsto (fun T =>
      μ {ω : Ω | ε / 2 ≤
        edist (A T ω i j) (L_A i j)} +
      μ {ω : Ω | ε / 2 ≤
        edist (B T ω i j) (L_B i j)})
      atTop (𝓝 0) := by
    have hh :=
      (hA i j (ε / 2) hε2).add
        (hB i j (ε / 2) hε2)
    simp only [add_zero] at hh; exact hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T; exact hbound T

/-! ### Multiplication -/

/-- Right-multiplication by a fixed matrix preserves convergence
in probability. -/
lemma MatrixLimitInProb.mul_right {n m p : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ}
    {L_A : Matrix (Fin n) (Fin m) ℝ}
    (C : Matrix (Fin m) (Fin p) ℝ)
    (hA : MatrixLimitInProb μ A L_A) :
    MatrixLimitInProb μ
      (fun T ω => A T ω * C) (L_A * C) := by
  intro i j ε hε
  have heq : ∀ T ω,
      (A T ω * C) i j =
        ∑ k : Fin m, A T ω i k * C k j := by
    intros; simp [Matrix.mul_apply]
  have hLeq : (L_A * C) i j =
      ∑ k : Fin m, L_A i k * C k j := by
    simp [Matrix.mul_apply]
  simp_rw [heq, hLeq]
  exact tendstoInMeasure_scalar_sum μ Finset.univ
    (fun k T ω => A T ω i k * C k j)
    (fun k => L_A i k * C k j)
    (fun k _ =>
      tendstoInMeasure_scalar_mul_const μ
        (C k j) (hA i k))
    ε hε

/-- Left-multiplication by a fixed matrix preserves convergence
in probability. -/
lemma MatrixLimitInProb.mul_left {n m p : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (C : Matrix (Fin n) (Fin m) ℝ)
    {B : ℕ → Ω → Matrix (Fin m) (Fin p) ℝ}
    {L_B : Matrix (Fin m) (Fin p) ℝ}
    (hB : MatrixLimitInProb μ B L_B) :
    MatrixLimitInProb μ
      (fun T ω => C * B T ω) (C * L_B) := by
  intro i j ε hε
  have heq : ∀ T ω,
      (C * B T ω) i j =
        ∑ k : Fin m, C i k * B T ω k j := by
    intros; simp [Matrix.mul_apply]
  have hLeq : (C * L_B) i j =
      ∑ k : Fin m, C i k * L_B k j := by
    simp [Matrix.mul_apply]
  simp_rw [heq, hLeq]
  exact tendstoInMeasure_scalar_sum μ Finset.univ
    (fun k T ω => C i k * B T ω k j)
    (fun k => C i k * L_B k j)
    (fun k _ =>
      tendstoInMeasure_const_scalar_mul μ
        (C i k) (hB k j))
    ε hε

/-- Products of convergent matrix sequences converge
entrywise. -/
lemma MatrixLimitInProb.mul {n m p : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ}
    {B : ℕ → Ω → Matrix (Fin m) (Fin p) ℝ}
    {L_A : Matrix (Fin n) (Fin m) ℝ}
    {L_B : Matrix (Fin m) (Fin p) ℝ}
    (hA : MatrixLimitInProb μ A L_A)
    (hB : MatrixLimitInProb μ B L_B) :
    MatrixLimitInProb μ
      (fun T ω => A T ω * B T ω)
      (L_A * L_B) := by
  intro i j ε hε
  have heq : ∀ T ω,
      (A T ω * B T ω) i j =
        ∑ k : Fin m, A T ω i k * B T ω k j := by
    intros; simp [Matrix.mul_apply]
  have hLeq : (L_A * L_B) i j =
      ∑ k : Fin m, L_A i k * L_B k j := by
    simp [Matrix.mul_apply]
  simp_rw [heq, hLeq]
  exact tendstoInMeasure_scalar_sum μ Finset.univ
    (fun k T ω => A T ω i k * B T ω k j)
    (fun k => L_A i k * L_B k j)
    (fun k _ =>
      tendstoInMeasure_scalar_mul_varying μ
        (hA i k) (hB k j))
    ε hε

/-! ### Transposition -/

/-- Transposes of convergent matrix sequences converge. -/
lemma MatrixLimitInProb.transpose {n m : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ}
    {L : Matrix (Fin n) (Fin m) ℝ}
    (hA : MatrixLimitInProb μ A L) :
    MatrixLimitInProb μ
      (fun T ω => (A T ω)ᵀ) Lᵀ := by
  intro i j ε hε
  have heq : ∀ T ω,
      (A T ω)ᵀ i j = A T ω j i := fun T ω => rfl
  simp_rw [heq, Matrix.transpose_apply]
  exact hA j i ε hε

/-! ### Union bound helper -/

/-- The measure of the union of entrywise deviation events tends
to zero. -/
lemma MatrixLimitInProb.iUnion_tendsto {n m : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ}
    {L : Matrix (Fin n) (Fin m) ℝ}
    (hA : MatrixLimitInProb μ A L)
    (δ : ENNReal) (hδ : 0 < δ) :
    Tendsto (fun T =>
      μ (⋃ k : Fin n, ⋃ l : Fin m,
        {ω : Ω | δ ≤ edist (A T ω k l) (L k l)}))
      atTop (𝓝 0) := by
  have hbound : ∀ T,
      μ (⋃ k : Fin n, ⋃ l : Fin m,
        {ω : Ω | δ ≤
          edist (A T ω k l) (L k l)}) ≤
      ∑ k : Fin n, ∑ l : Fin m,
        μ {ω : Ω | δ ≤
          edist (A T ω k l) (L k l)} := by
    intro T
    calc μ (⋃ k : Fin n, ⋃ l : Fin m,
          {ω : Ω | δ ≤
            edist (A T ω k l) (L k l)})
        ≤ ∑' k : Fin n,
            μ (⋃ l : Fin m,
              {ω : Ω | δ ≤
                edist (A T ω k l) (L k l)}) :=
          measure_iUnion_le _
      _ = ∑ k : Fin n,
            μ (⋃ l : Fin m,
              {ω : Ω | δ ≤
                edist (A T ω k l) (L k l)}) :=
          tsum_fintype _
      _ ≤ ∑ k : Fin n, ∑' l : Fin m,
            μ {ω : Ω | δ ≤
              edist (A T ω k l) (L k l)} :=
          Finset.sum_le_sum
            (fun k _ => measure_iUnion_le _)
      _ = ∑ k : Fin n, ∑ l : Fin m,
            μ {ω : Ω | δ ≤
              edist (A T ω k l) (L k l)} := by
          simp_rw [tsum_fintype]
  have hsum : Tendsto (fun T =>
      ∑ k : Fin n, ∑ l : Fin m,
        μ {ω : Ω | δ ≤
          edist (A T ω k l) (L k l)})
      atTop (𝓝 0) := by
    simp_rw [← Finset.sum_product']
    have h0 : (0 : ENNReal) =
        ∑ _p : Fin n × Fin m, (0 : ENNReal) := by
      simp
    rw [h0]
    apply tendsto_finset_sum
    intro ⟨k, l⟩ _
    exact hA k l δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T; exact hbound T

/-! ### Inversion -/

/-- Inverses of convergent matrix sequences converge when the
limit is nonsingular. -/
lemma MatrixLimitInProb.inv {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ}
    {L : Matrix (Fin n) (Fin n) ℝ}
    (hA : MatrixLimitInProb μ A L)
    (hL : L.det ≠ 0) :
    MatrixLimitInProb μ
      (fun T ω => (A T ω)⁻¹) L⁻¹ := by
  have hcont_ij : ∀ i j : Fin n,
      ContinuousAt
        (fun M : Matrix (Fin n) (Fin n) ℝ =>
          M⁻¹ i j) L := by
    intro i j
    have hfun :
        (fun M : Matrix (Fin n) (Fin n) ℝ =>
          M⁻¹ i j) =
        fun M => M.det⁻¹ * M.adjugate i j := by
      funext M
      simp [Matrix.inv_def, Ring.inverse_eq_inv,
        Matrix.smul_apply, smul_eq_mul]
    rw [hfun]
    exact ContinuousAt.mul
      ((continuousAt_inv₀ hL).comp (by fun_prop))
      (by fun_prop)
  intro i j ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · have hempty : ∀ T : ℕ,
        {ω : Ω | (⊤ : ENNReal) ≤
          edist ((A T ω)⁻¹ i j) (L⁻¹ i j)} =
        ∅ :=
      fun T => Set.eq_empty_of_forall_notMem
        (fun ω h => (edist_lt_top _ _).not_ge h)
    have h_eq : (fun (T : ℕ) =>
        μ {ω : Ω | (⊤ : ENNReal) ≤
          edist ((A T ω)⁻¹ i j) (L⁻¹ i j)}) =
        fun _ => 0 := by
      funext T; rw [hempty, measure_empty]
    rw [h_eq]; exact tendsto_const_nhds
  have hε_pos : 0 < ε.toReal :=
    ENNReal.toReal_pos hε.ne' hε_top
  have hpre_mem :
      (fun M : Matrix (Fin n) (Fin n) ℝ =>
        M⁻¹ i j) ⁻¹'
      Metric.ball (L⁻¹ i j) ε.toReal ∈ nhds L :=
    (hcont_ij i j) (Metric.ball_mem_nhds _ hε_pos)
  let _inst :
      PseudoMetricSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs
      (PseudoMetricSpace (Fin n → Fin n → ℝ))
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ :
      ∃ δ > 0, Metric.ball L δ ⊆ _ := by
    apply Metric.mem_nhds_iff.mp
    exact hpre_mem
  set δ := ENNReal.ofReal (δ₀ / 2)
  have hδ_pos : 0 < δ :=
    ENNReal.ofReal_pos.mpr (by linarith)
  have hS : ∀ T,
      {ω : Ω | ε ≤
        edist ((A T ω)⁻¹ i j) (L⁻¹ i j)} ⊆
      ⋃ k : Fin n, ⋃ l : Fin n,
        {ω : Ω | δ ≤
          edist (A T ω k l) (L k l)} := by
    intro T ω hω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    by_contra hlt; push_neg at hlt
    have hkl : ∀ k l,
        dist (A T ω k l) (L k l) < δ₀ := by
      intro k l
      have hkl_enn :
          edist (A T ω k l) (L k l) < δ :=
        hlt k l
      rw [edist_dist] at hkl_enn
      have := (ENNReal.ofReal_lt_ofReal_iff
        (by positivity : 0 < δ₀ / 2)).mp
        hkl_enn
      linarith
    have hdist : dist (A T ω) L < δ₀ := by
      rw [dist_pi_lt_iff hδ₀_pos]
      intro k
      rw [dist_pi_lt_iff hδ₀_pos]
      intro l
      exact hkl k l
    have hmem : A T ω ∈ Metric.ball L δ₀ :=
      Metric.mem_ball.mpr hdist
    have hconc := hδ₀_sub hmem
    simp only [Set.mem_preimage,
      Metric.mem_ball] at hconc
    have hlt_ε :
        edist ((A T ω)⁻¹ i j) (L⁻¹ i j) < ε := by
      rw [edist_dist,
        ← ENNReal.ofReal_toReal hε_top]
      exact (ENNReal.ofReal_lt_ofReal_iff
        hε_pos).mpr hconc
    exact absurd hlt_ε (not_lt.mpr hω)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (MatrixLimitInProb.iUnion_tendsto μ hA δ
      hδ_pos)
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T;
      exact measure_mono (hS T)

/-! ### Moore–Penrose pseudoinversion -/

/-- Pseudoinverses of convergent matrix sequences converge when
the limit is nonsingular. -/
lemma MatrixLimitInProb.pinv {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω)
    {A : ℕ → Ω → Matrix (Fin n) (Fin n) ℝ}
    {L : Matrix (Fin n) (Fin n) ℝ}
    (hA : MatrixLimitInProb μ A L)
    (hL : L.det ≠ 0) :
    MatrixLimitInProb μ
      (fun T ω => (A T ω).pinv) L⁻¹ := by
  have h_inv := MatrixLimitInProb.inv μ hA hL
  have h_isOpen :
      IsOpen {M : Matrix (Fin n) (Fin n) ℝ |
        M.det ≠ 0} :=
    isOpen_ne_fun
      (Continuous.matrix_det continuous_id)
      continuous_const
  have hpre_mem :
      {M : Matrix (Fin n) (Fin n) ℝ |
        M.det ≠ 0} ∈ nhds L :=
    IsOpen.mem_nhds h_isOpen hL
  intro i j ε hε
  rcases eq_or_ne ε ⊤ with rfl | hε_top
  · have hempty : ∀ T : ℕ,
        {ω : Ω | (⊤ : ENNReal) ≤
          edist ((A T ω).pinv i j)
            (L⁻¹ i j)} = ∅ :=
      fun T => Set.eq_empty_of_forall_notMem
        (fun ω h => (edist_lt_top _ _).not_ge h)
    have h_eq : (fun (T : ℕ) =>
        μ {ω : Ω | (⊤ : ENNReal) ≤
          edist ((A T ω).pinv i j)
            (L⁻¹ i j)}) = fun _ => 0 := by
      funext T; rw [hempty T, measure_empty]
    rw [h_eq]; exact tendsto_const_nhds
  let _inst :
      PseudoMetricSpace (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs
      (PseudoMetricSpace (Fin n → Fin n → ℝ))
  obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ :
      ∃ δ > 0, Metric.ball L δ ⊆
        {M : Matrix (Fin n) (Fin n) ℝ |
          M.det ≠ 0} :=
    Metric.mem_nhds_iff.mp hpre_mem
  set δ := ENNReal.ofReal (δ₀ / 2)
  have hδ_pos : 0 < δ :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hS : ∀ T,
      {ω : Ω | ε ≤
        edist ((A T ω).pinv i j) (L⁻¹ i j)} ⊆
      {ω : Ω | ε ≤
        edist ((A T ω)⁻¹ i j) (L⁻¹ i j)} ∪
      ⋃ k : Fin n, ⋃ l : Fin n,
        {ω : Ω | δ ≤
          edist (A T ω k l) (L k l)} := by
    intro T ω hω
    simp only [Set.mem_union, Set.mem_setOf_eq,
      Set.mem_iUnion]
    by_cases hdet : (A T ω).det = 0
    · right
      by_contra hlt; push_neg at hlt
      have hkl : ∀ k l,
          dist (A T ω k l) (L k l) < δ₀ := by
        intro k l
        have hkl_enn :
            edist (A T ω k l) (L k l) < δ :=
          hlt k l
        rw [edist_dist] at hkl_enn
        have := (ENNReal.ofReal_lt_ofReal_iff
          (by positivity)).mp hkl_enn
        linarith
      have hdist : dist (A T ω) L < δ₀ := by
        rw [dist_pi_lt_iff hδ₀_pos]
        intro k
        rw [dist_pi_lt_iff hδ₀_pos]
        intro l
        exact hkl k l
      have hconc :=
        hδ₀_sub (Metric.mem_ball.mpr hdist)
      exact hconc hdet
    · left
      have hpinv : (A T ω).pinv = (A T ω)⁻¹ :=
        Matrix.pinv_eq_inv hdet
      simp only [Set.mem_setOf_eq] at hω
      rw [hpinv] at hω
      exact hω
  have hbound : ∀ T,
      μ {ω : Ω | ε ≤
        edist ((A T ω).pinv i j) (L⁻¹ i j)} ≤
      μ {ω : Ω | ε ≤
        edist ((A T ω)⁻¹ i j) (L⁻¹ i j)} +
      μ (⋃ k : Fin n, ⋃ l : Fin n,
        {ω : Ω | δ ≤
          edist (A T ω k l) (L k l)}) :=
    fun T => (measure_mono (hS T)).trans
      (measure_union_le _ _)
  have hsum : Tendsto (fun T =>
      μ {ω : Ω | ε ≤
        edist ((A T ω)⁻¹ i j) (L⁻¹ i j)} +
      μ (⋃ k : Fin n, ⋃ l : Fin n,
        {ω : Ω | δ ≤
          edist (A T ω k l) (L k l)}))
      atTop (𝓝 0) := by
    have h1 := h_inv i j ε hε
    have h2 :=
      MatrixLimitInProb.iUnion_tendsto μ hA δ
        hδ_pos
    have h := h1.add h2
    simp only [add_zero] at h
    exact h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum
  · filter_upwards with T; exact zero_le _
  · filter_upwards with T; exact hbound T

/-! ### Eventual-equality transfer -/

/-- If two matrix-valued sequences agree eventually, and one
converges in probability, so does the other. This is the
`MatrixLimitInProb` analogue of `Filter.Tendsto.congr`. -/
lemma MatrixLimitInProb.congr {n m : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A B : ℕ → Ω → Matrix (Fin n) (Fin m) ℝ}
    {L : Matrix (Fin n) (Fin m) ℝ}
    (h_eq : ∀ᶠ T in atTop,
      ∀ ω, A T ω = B T ω)
    (hA : MatrixLimitInProb μ A L) :
    MatrixLimitInProb μ B L := by
  intro i j ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (hA i j ε hε)
  · filter_upwards with T; exact zero_le _
  · filter_upwards [h_eq] with T hT
    apply measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rwa [hT ω]

end ProbabilityTheory
