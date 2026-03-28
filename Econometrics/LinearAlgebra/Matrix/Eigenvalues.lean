/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# Eigenvalue Bounds and Weyl's Inequality

This file provides a quadratic-form-based eigenvalue API for real
symmetric matrices, together with Weyl's additive eigenvalue
inequality and a scalar-quadratic-form factoring lemma.

## Main definitions

* `Matrix.IsEigLB` : predicate encoding `λ_min(A) ≥ c` via
  quadratic forms.
* `Matrix.IsEigUB` : predicate encoding `λ_max(A) ≤ c` via
  quadratic forms.

## Main results

* `Matrix.IsEigLB.add` : Weyl's inequality
  `λ_min(A + B) ≥ λ_min(A) + λ_min(B)`.
* `Matrix.IsEigLB.inv_upper` : eigenvalue bound inversion for
  invertible matrices.
* `Matrix.IsEigLB.of_inv_smul` : undo inverse-scalar on an
  eigenvalue lower bound.
* `Matrix.qform_smul` : `v'(c • M)v = c · (v'Mv)`.
-/

open Matrix Finset BigOperators

namespace Matrix

variable {n : ℕ}

/-! ### Auxiliary lemmas -/

/-- The dot product of a vector with itself is non-negative. -/
lemma dotProduct_self_nonneg (x : Fin n → ℝ) :
    (0 : ℝ) ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-! ### Eigenvalue lower bound predicate -/

/-- `c` is a lower bound on the eigenvalues of `A` (in
quadratic-form sense): `c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)` for
all vectors `x`. For symmetric `A`, this is equivalent to
`λ_min(A) ≥ c`. -/
def IsEigLB (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    Prop :=
  ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)

/-! ### Weyl's eigenvalue inequality -/

/-- **Weyl's inequality** (additive form): eigenvalue lower bounds
add under matrix addition. -/
theorem IsEigLB.add
    {A B : Matrix (Fin n) (Fin n) ℝ} {a b : ℝ}
    (hA : IsEigLB A a) (hB : IsEigLB B b) :
    IsEigLB (A + B) (a + b) := by
  intro x
  rw [add_mul, add_mulVec, dotProduct_add]
  exact add_le_add (hA x) (hB x)

/-- Eigenvalue lower bounds are monotone: a smaller bound is also
valid. -/
theorem IsEigLB.mono
    {A : Matrix (Fin n) (Fin n) ℝ} {c d : ℝ}
    (h : IsEigLB A c) (hdc : d ≤ c) :
    IsEigLB A d := by
  intro x
  exact le_trans
    (mul_le_mul_of_nonneg_right hdc
      (dotProduct_self_nonneg x))
    (h x)

/-- An eigenvalue lower bound gives a quadratic-form
inequality. -/
theorem IsEigLB.apply
    {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : IsEigLB A c) (x : Fin n → ℝ) :
    c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) :=
  h x

/-! ### Positive definite matrices -/

/-- For a positive definite matrix,
`0 ≤ x ⬝ᵥ (A *ᵥ x)` for all `x`. Converts from Mathlib's
Finsupp-based `PosDef` to `dotProduct`/`mulVec`. -/
lemma posDef_dotProduct_mulVec_nonneg
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  let v : Fin n →₀ ℝ :=
    Finsupp.equivFunOnFinite.symm x
  have h := hA.posSemidef.2 v
  have inner_sum : ∀ i xi,
      v.sum (fun j xj => star xi * A i j * xj) =
        ∑ j, star xi * A i j * x j := by
    intro i xi
    apply Finsupp.sum_fintype
    intro j; exact mul_zero _
  have heq_inner :
      (fun i xi =>
        v.sum (fun j xj =>
          star xi * A i j * xj)) =
      (fun i xi =>
        ∑ j, star xi * A i j * x j) := by
    ext i xi; exact inner_sum i xi
  rw [heq_inner] at h
  have outer_sum :
      v.sum (fun i xi =>
        ∑ j, star xi * A i j * x j) =
      ∑ i, ∑ j, star (x i) * A i j * x j := by
    apply Finsupp.sum_fintype
    intro i; apply Finset.sum_eq_zero; intro j _
    have h0 : star (0 : ℝ) = 0 := rfl
    rw [h0, zero_mul, zero_mul]
  rw [outer_sum] at h
  have heq :
      (∑ i, ∑ j, star (x i) * A i j * x j) =
        x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mulVec]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    have h_star : star (x i) = x i := rfl
    rw [h_star]; ring
  rw [heq] at h; exact h

/-- Zero is an eigenvalue lower bound for any positive definite
matrix: `λ_min(A) ≥ 0` when `A ≻ 0`. -/
theorem IsEigLB.zero_of_posDef
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : IsEigLB A 0 := by
  intro x; rw [zero_mul]
  exact posDef_dotProduct_mulVec_nonneg A hA x

/-! ### Eigenvalue upper bound predicate -/

/-- `c` is an upper bound on the eigenvalues of `A` (in
quadratic-form sense): `x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)` for
all vectors `x`. For symmetric `A`, this is equivalent to
`λ_max(A) ≤ c`. -/
def IsEigUB (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    Prop :=
  ∀ x : Fin n → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x)

/-- An eigenvalue upper bound gives a quadratic-form
inequality. -/
theorem IsEigUB.apply
    {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : IsEigUB A c) (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ c * (x ⬝ᵥ x) :=
  h x

/-! ### Eigenvalue bound inversion -/

/-- **Eigenvalue bound inversion**: if `λ_min(A⁻¹) ≥ c > 0`,
then `λ_max(A) ≤ 1/c`. -/
theorem IsEigLB.inv_upper
    {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hA_det : IsUnit A.det) (hc : 0 < c)
    (h : IsEigLB A⁻¹ c) : IsEigUB A (1 / c) := by
  intro x
  have hy : A⁻¹ *ᵥ (A *ᵥ x) = x := by
    rw [mulVec_mulVec, nonsing_inv_mul _ hA_det,
      one_mulVec]
  have h1 := h (A *ᵥ x)
  rw [hy] at h1
  have h2 :
      (A *ᵥ x) ⬝ᵥ x = x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mul_comm]
  rw [h2] at h1
  have h_sq :
      0 ≤ (x - c • (A *ᵥ x)) ⬝ᵥ
        (x - c • (A *ᵥ x)) := by
    simp only [dotProduct]
    apply Finset.sum_nonneg
    intro i _; exact mul_self_nonneg _
  have h_expand :
      (x - c • (A *ᵥ x)) ⬝ᵥ
        (x - c • (A *ᵥ x)) =
      x ⬝ᵥ x - 2 * c * (x ⬝ᵥ (A *ᵥ x)) +
        c ^ 2 * ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
    simp only [dotProduct, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h_expand] at h_sq
  have h_bound :
      c ^ 2 * ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) ≤
        c * (x ⬝ᵥ (A *ᵥ x)) := by
    calc c ^ 2 * ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))
        = c * (c * ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))) :=
        by ring
      _ ≤ c * (x ⬝ᵥ (A *ᵥ x)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hc)
  have h_final :
      c * (x ⬝ᵥ (A *ᵥ x)) ≤ x ⬝ᵥ x := by
    linarith
  calc x ⬝ᵥ (A *ᵥ x)
      = (c * (x ⬝ᵥ (A *ᵥ x))) / c := by
        rw [mul_div_cancel_left₀ _ hc.ne']
    _ ≤ (x ⬝ᵥ x) / c :=
        div_le_div_of_nonneg_right h_final hc.le
    _ = 1 / c * (x ⬝ᵥ x) := by ring

/-- Undo inverse-scalar: if `λ_min(s⁻¹ • A) ≥ c` and `s > 0`,
then `λ_min(A) ≥ c * s`. -/
theorem IsEigLB.of_inv_smul
    {A : Matrix (Fin n) (Fin n) ℝ}
    {c : ℝ} {s : ℝ} (hs : 0 < s)
    (h : IsEigLB (s⁻¹ • A) c) :
    IsEigLB A (c * s) := by
  intro x
  have h1 := h x
  have h2 :
      x ⬝ᵥ ((s⁻¹ • A) *ᵥ x) =
        s⁻¹ * (x ⬝ᵥ (A *ᵥ x)) := by
    rw [smul_mulVec]
    simp only [dotProduct, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h2] at h1
  have h3 :
      s * (c * (x ⬝ᵥ x)) ≤
        s * (s⁻¹ * (x ⬝ᵥ (A *ᵥ x))) :=
    mul_le_mul_of_nonneg_left h1 hs.le
  have h4 :
      s * (s⁻¹ * (x ⬝ᵥ (A *ᵥ x))) =
        x ⬝ᵥ (A *ᵥ x) := by
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne',
      one_mul]
  rw [h4] at h3
  linarith

/-! ### Scalar-quadratic-form factoring -/

/-- For a scalar `c`, matrix `M`, and column vector `v`:
`v'(c • M)v = c · (v'Mv)`. Used to pull `T⁻¹` scalars out of
quadratic forms. -/
lemma qform_smul {r : ℕ} (c : ℝ)
    (M : Matrix (Fin r) (Fin r) ℝ)
    (v : Matrix (Fin r) (Fin 1) ℝ) :
    (vᵀ * (c • M) * v) 0 0 =
      c * (vᵀ * M * v) 0 0 := by
  simp only [Matrix.mul_apply, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul]
  calc (∑ i : Fin r,
      (∑ j : Fin r, v j 0 * (c * M j i)) *
        v i 0)
    _ = ∑ i : Fin r, ∑ j : Fin r,
        (v j 0 * (c * M j i)) * v i 0 := by
        simp_rw [Finset.sum_mul]
    _ = ∑ i : Fin r, ∑ j : Fin r,
        c * (v j 0 * M j i * v i 0) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        ring
    _ = ∑ i : Fin r,
        c * ∑ j : Fin r,
          (v j 0 * M j i * v i 0) := by
        simp_rw [← Finset.mul_sum]
    _ = c * ∑ i : Fin r, ∑ j : Fin r,
        (v j 0 * M j i * v i 0) := by
        rw [← Finset.mul_sum]
    _ = c * ∑ i : Fin r,
        (∑ j : Fin r, v j 0 * M j i) *
          v i 0 := by
        simp_rw [Finset.sum_mul]

end Matrix
