/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# Measure Zero for Polynomial Zero Sets

This file proves that the zero set of a nonzero multivariate polynomial over `ℝ`
has Lebesgue measure zero. The proof proceeds by induction on the number of
variables, using Fubini–Tonelli to reduce to the univariate case.

## Main results

* `volume_polynomial_roots` : roots of a univariate polynomial have measure zero.
* `volume_mvPolynomial_roots` : zero set of a multivariate polynomial has
  measure zero.
-/

open MeasureTheory Set Polynomial

namespace MeasureTheory

/--
Base Case for Algebraic Varieties:
The set of roots of a non-zero univariate polynomial over ℝ has Lebesgue measure zero.
-/
lemma volume_polynomial_roots (p : ℝ[X]) (hp : p ≠ 0) :
    volume {x : ℝ | p.eval x = 0} = 0 := by
  have h_roots : {x : ℝ | p.eval x = 0} ⊆ ↑p.roots.toFinset := by
    intro x hx
    simp only [mem_setOf_eq] at hx
    simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]
    exact hx
  have h_count : {x : ℝ | p.eval x = 0}.Countable :=
    (Finset.finite_toSet p.roots.toFinset).countable.mono h_roots
  exact Countable.measure_zero h_count volume

/-- Evaluating an `MvPolynomial` is a continuous function. -/
lemma continuous_mvPolynomial_eval {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Continuous (fun x : Fin n → ℝ => MvPolynomial.eval x p) := by
  apply MvPolynomial.induction_on p
  · intro c
    simp only [MvPolynomial.eval_C]
    exact continuous_const
  · intro p1 p2 h1 h2
    simp only [map_add]
    exact Continuous.add h1 h2
  · intro p1 i h1
    simp only [map_mul, MvPolynomial.eval_X]
    exact Continuous.mul h1 (continuous_apply i)

/-- The zero set of any multivariate polynomial is measurable. -/
lemma measurableSet_mvPolynomial_roots {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    MeasurableSet {x : Fin n → ℝ | MvPolynomial.eval x p = 0} := by
  exact Continuous.measurable (continuous_mvPolynomial_eval p) (measurableSet_singleton 0)

/--
Algebraic Bridge:
Evaluating a multivariate polynomial in n+1 variables at (y, x) is exactly the same as
mapping its coefficients into polynomials in n variables, evaluating those at x to get a
univariate polynomial, and evaluating that at y.
-/
lemma eval_finCons_eq_eval_map_finSuccEquiv (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ)
    (y : ℝ) (x : Fin n → ℝ) :
    MvPolynomial.eval (Fin.cons y x) p =
    (Polynomial.map (MvPolynomial.eval x) (MvPolynomial.finSuccEquiv ℝ n p)).eval y := by
  apply MvPolynomial.induction_on p
  · intro c
    -- finSuccEquiv is an AlgEquiv, so it inherently preserves algebra maps (constants)
    have hc : (MvPolynomial.finSuccEquiv ℝ n) (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) :=
      AlgEquiv.commutes (MvPolynomial.finSuccEquiv ℝ n) c
    rw [MvPolynomial.eval_C, hc, Polynomial.map_C, Polynomial.eval_C, MvPolynomial.eval_C]
  · intro p1 p2 h1 h2
    rw [map_add, map_add, Polynomial.map_add, Polynomial.eval_add, h1, h2]
  · intro p1 i h1
    rw [map_mul, map_mul, Polynomial.map_mul, Polynomial.eval_mul, h1]
    congr 1
    revert i
    refine Fin.cases ?_ ?_
    · rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.eval_X,
        MvPolynomial.eval_X, Fin.cons_zero]
    · intro j
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, Polynomial.eval_C,
          MvPolynomial.eval_X, Fin.cons_succ, MvPolynomial.eval_X]

/--
The core Phase 2.1 Theorem: A non-zero multivariate polynomial has a zero-set of Lebesgue measure
    zero.
-/
lemma volume_mvPolynomial_roots (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval x p = 0} = 0 := by
  induction n with
  | zero =>
    -- Base case n = 0: p is a constant C c
    have hC : ∃ c, p = MvPolynomial.C c := by
      apply MvPolynomial.induction_on p
      · intro c; exact ⟨c, rfl⟩
      · rintro p1 p2 ⟨c1, hc1⟩ ⟨c2, hc2⟩; exact ⟨c1 + c2, by rw [hc1, hc2, map_add]⟩
      · rintro p1 i _
        exact i.elim0 -- Fin 0 is empty, so this branch is impossible
    rcases hC with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro h
      rw [h, map_zero] at hc
      exact hp hc
    have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x p = 0} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      rw [hc, MvPolynomial.eval_C]
      exact hc_ne
    rw [hempty, measure_empty]
  | succ m ih =>
    -- Inductive step n = m + 1
    let Q := MvPolynomial.finSuccEquiv ℝ m p
    have hQ_ne : Q ≠ 0 := by
      intro h
      have hp_eq : p = (MvPolynomial.finSuccEquiv ℝ m).symm Q := by
        exact (AlgEquiv.symm_apply_apply (MvPolynomial.finSuccEquiv ℝ m) p).symm
      rw [h, map_zero] at hp_eq
      exact hp hp_eq
    -- Since Q ≠ 0, it has a non-zero coefficient. We pick the leading coefficient.
    let c := Q.coeff Q.natDegree
    have hc_ne : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ_ne
    -- By the induction hypothesis, the zero set of this coefficient has m-dimensional measure 0
    have h_ih := ih c hc_ne
    let Z_c := {x : Fin m → ℝ | MvPolynomial.eval x c = 0}
    -- For any x not in Z_c, the 1D slice polynomial Q_x is non-zero, so its roots have 1D measure 0
    have h_slice : ∀ x ∉ Z_c, volume {y : ℝ | MvPolynomial.eval (Fin.cons y x) p = 0} = 0 := by
      intro x hx
      have h_map_ne : Polynomial.map (MvPolynomial.eval x) Q ≠ 0 := by
        intro h_eq
        have h_coeff : (Polynomial.map (MvPolynomial.eval x) Q).coeff Q.natDegree = 0 := by
          rw [h_eq, Polynomial.coeff_zero]
        rw [Polynomial.coeff_map] at h_coeff
        exact hx h_coeff
      have h_base := volume_polynomial_roots (Polynomial.map (MvPolynomial.eval x) Q) h_map_ne
      have h_set_eq : {y : ℝ | MvPolynomial.eval (Fin.cons y x) p = 0} =
                      {y : ℝ | (Polynomial.map (MvPolynomial.eval x) Q).eval y = 0} := by
        ext y
        simp only [mem_setOf_eq]
        rw [eval_finCons_eq_eval_map_finSuccEquiv]
      rw [h_set_eq]
      exact h_base
    -- Almost everywhere (i.e. outside Z_c), the slice has measure 0
    have h_ae_zero : ∀ᵐ x ∂volume, volume {y : ℝ | MvPolynomial.eval (Fin.cons y x) p = 0} = 0 := by
      have h_sub : {x : Fin m → ℝ | volume {y : ℝ | MvPolynomial.eval (Fin.cons y x) p =
          0} ≠ 0} ⊆ Z_c := by
        intro x hx
        by_contra hx_not
        exact hx (h_slice x hx_not)
      exact measure_mono_null h_sub h_ih
    -- ====================================================================
    -- Fubini/Tonelli Integration Step
    -- ====================================================================
    let S := {v : Fin (m + 1) → ℝ | MvPolynomial.eval v p = 0}
    have hS_meas : MeasurableSet S := measurableSet_mvPolynomial_roots p
    -- 1. The measure of S is the integral of its indicator
    have h_vol_eq : volume S = ∫⁻ v, S.indicator (fun _ => (1 : ENNReal)) v ∂volume := by
      rw [lintegral_indicator_const hS_meas, one_mul]
    -- 2. Apply Tonelli's Theorem via piFinSuccAboveEquiv
    have h_fubini_raw : (∫⁻ v, S.indicator (fun _ => (1 : ENNReal)) v ∂volume) =
        ∫⁻ y, ∫⁻ x, S.indicator (fun _ => (1 : ENNReal)) (Fin.cons (α :=
            fun _ => ℝ) y x) ∂volume ∂volume := by
      have hf : Measurable (S.indicator (fun _ => (1 : ENNReal))) :=
        measurable_const.indicator hS_meas
      set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      calc ∫⁻ v, S.indicator (fun _ => 1) v ∂volume
          = ∫⁻ p : ℝ × (Fin m → ℝ), S.indicator (fun _ => 1) (e.symm p) ∂volume := by
            have key :=
              (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).lintegral_comp
                (hf.comp e.symm.measurable)
            simp only [Function.comp] at key
            have fold_e : MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0 = e := rfl
            simp only [fold_e, e.symm_apply_apply] at key
            exact key
        _ = ∫⁻ y, ∫⁻ x, S.indicator (fun _ => 1) (e.symm (y, x)) ∂volume ∂volume := by
            exact lintegral_prod _ (hf.comp e.symm.measurable).aemeasurable
        _ = ∫⁻ y, ∫⁻ x, S.indicator (fun _ => 1) (Fin.cons (α :=
            fun _ => ℝ) y x) ∂volume ∂volume := by
            congr 1; ext y; congr 1; ext x; congr 1
            ext i; refine Fin.cases ?_ ?_ i
            · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.cons_zero]
            · intro j; simp [e, MeasurableEquiv.piFinSuccAbove, Fin.cons_succ]
    -- We must swap the integrals so we can integrate over `y` first
    have h_swap : (∫⁻ y, ∫⁻ x, S.indicator (fun _ => (1 : ENNReal)) (Fin.cons (α :=
        fun _ => ℝ) y x) ∂volume ∂volume) =
                  (∫⁻ x, ∫⁻ y, S.indicator (fun _ => (1 : ENNReal)) (Fin.cons (α :=
                      fun _ => ℝ) y x) ∂volume ∂volume) := by
      have h_cont : Continuous (fun p : ℝ × (Fin m → ℝ) => Fin.cons (α := fun _ => ℝ) p.1 p.2) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ ?_ i
        · exact continuous_fst
        · intro j
          exact (continuous_apply j).comp continuous_snd
      exact lintegral_lintegral_swap
        ((measurable_const.indicator hS_meas).comp h_cont.measurable).aemeasurable
    have h_fubini : (∫⁻ v, S.indicator (fun _ => (1 : ENNReal)) v ∂volume) =
        ∫⁻ x, ∫⁻ y, S.indicator (fun _ => (1 : ENNReal)) (Fin.cons (α :=
            fun _ => ℝ) y x) ∂volume ∂volume := by
      rw [h_fubini_raw, h_swap]
    -- 3. Show the inner integral evaluates exactly to the volume of the slice
    have h_slice_int : ∀ x, ∫⁻ y, S.indicator (fun _ => (1 : ENNReal)) (Fin.cons (α :=
        fun _ => ℝ) y x) ∂volume =
        volume {y : ℝ | MvPolynomial.eval (Fin.cons y x) p = 0} := by
      intro x
      have h_slice_meas : MeasurableSet {y : ℝ | MvPolynomial.eval (Fin.cons y x) p = 0} := by
        have h_eq : {y : ℝ | MvPolynomial.eval (Fin.cons y x) p = 0} =
                    {y : ℝ | (Polynomial.map (MvPolynomial.eval x) Q).eval y = 0} := by
          ext y; simp only [mem_setOf_eq]; rw [eval_finCons_eq_eval_map_finSuccEquiv]
        rw [h_eq]
        -- A 1D polynomial evaluates to 0 on a finite set or the whole line, both are measurable.
        by_cases h_map : Polynomial.map (MvPolynomial.eval x) Q = 0
        · rw [h_map]
          have h_univ : {y : ℝ | (0 : ℝ[X]).eval y = 0} = Set.univ := by ext y; simp
          rw [h_univ]
          exact MeasurableSet.univ
        · have h_count : {y : ℝ | (Polynomial.map (MvPolynomial.eval x) Q).eval y = 0}.Countable :=
            by
            have h_sub : {y : ℝ | (Polynomial.map (MvPolynomial.eval x) Q).eval y =
                0} ⊆ ↑(Polynomial.map (MvPolynomial.eval x) Q).roots.toFinset := by
              intro y hy
              simp only [mem_setOf_eq] at hy
              simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots h_map, IsRoot.def]
              exact hy
            exact (Finset.finite_toSet _).countable.mono h_sub
          exact h_count.measurableSet
      have h_indicator_eq : (fun y => S.indicator (fun _ => (1 : ENNReal)) (Fin.cons (α :=
          fun _ => ℝ) y x)) =
          {y : ℝ | MvPolynomial.eval (Fin.cons y x) p = 0}.indicator (fun _ => 1) := by
        ext y
        simp only [S, indicator_apply, mem_setOf_eq]
      rw [h_indicator_eq, lintegral_indicator_const h_slice_meas, one_mul]
    -- 4. Combine the Fubini expansion and the slice identity
    have h_combined : volume S = ∫⁻ x, volume {y : ℝ | MvPolynomial.eval (Fin.cons y x) p =
        0} ∂volume := by
      rw [h_vol_eq, h_fubini]
      congr 1; ext x; rw [h_slice_int]
    -- 5. Since the slices have measure 0 almost everywhere, the integral is 0
    rw [h_combined]
    have h_ae_eq : (fun x => volume {y : ℝ | MvPolynomial.eval (Fin.cons y x) p =
        0}) =ᵐ[volume] (fun x => 0) := by
      filter_upwards [h_ae_zero] with x hx
      exact hx
    rw [lintegral_congr_ae h_ae_eq, lintegral_zero]

end MeasureTheory
