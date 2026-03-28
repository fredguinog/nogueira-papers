/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib
import Econometrics.Analysis.InnerProductSpace.PseudoinverseGeometry

/-!
# Moore–Penrose Pseudoinverse for Matrices

This file defines the Moore–Penrose pseudoinverse of a matrix over `ℝ`
(or any `RCLike` field) by lifting to the geometric pseudoinverse on
Euclidean spaces. It proves uniqueness, the four Penrose conditions, and
derives key algebraic identities used in projection and trace calculations.

## Main definitions

* `Matrix.IsMoorePenroseInverse` : the four Moore–Penrose axioms.
* `Matrix.pinv` : the Moore–Penrose pseudoinverse of a matrix.

## Main results

* `Matrix.IsMoorePenroseInverse.unique` : uniqueness of the
  Moore–Penrose inverse.
* `Matrix.pinv_isMoorePenroseInverse` : `A.pinv` satisfies all four axioms.
* `Matrix.pinv_eq_inv` : for nonsingular square matrices, `pinv = inv`.
* `Matrix.trace_mul_pinv_mul_transpose_eq_rank` :
  `tr(A(AᵀA)⁺Aᵀ) = rank(A)`.
-/

open Matrix MeasureTheory

variable {m n 𝕜 : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]
variable [RCLike 𝕜]

namespace Matrix

/-- The four Moore–Penrose axioms for a pseudoinverse. -/
def IsMoorePenroseInverse (A : Matrix m n 𝕜) (A_pinv : Matrix n m 𝕜) :
    Prop :=
  A * A_pinv * A = A ∧
  A_pinv * A * A_pinv = A_pinv ∧
  (A * A_pinv)ᴴ = A * A_pinv ∧
  (A_pinv * A)ᴴ = A_pinv * A

/-- The Moore–Penrose inverse is unique. -/
theorem IsMoorePenroseInverse.unique {A : Matrix m n 𝕜}
    {B C : Matrix n m 𝕜}
    (hB : IsMoorePenroseInverse A B)
    (hC : IsMoorePenroseInverse A C) : B = C := by
  rcases hB with ⟨hB1, hB2, hB3, hB4⟩
  rcases hC with ⟨hC1, hC2, hC3, hC4⟩
  have eqB1 : B = B * Bᴴ * Aᴴ := by
    calc B = B * A * B := hB2.symm
      _ = B * (A * B) := by rw [Matrix.mul_assoc]
      _ = B * (A * B)ᴴ := by rw [hB3]
      _ = B * (Bᴴ * Aᴴ) := by rw [conjTranspose_mul]
      _ = B * Bᴴ * Aᴴ := by rw [← Matrix.mul_assoc]
  have eqB2 : B * Bᴴ * Aᴴ = B * A * C := by
    calc B * Bᴴ * Aᴴ
        = B * Bᴴ * (A * C * A)ᴴ := by rw [hC1]
      _ = B * Bᴴ * (Aᴴ * (Cᴴ * Aᴴ)) := by
          rw [conjTranspose_mul, conjTranspose_mul]
      _ = B * (Bᴴ * Aᴴ) * (Cᴴ * Aᴴ) := by
          simp only [← Matrix.mul_assoc]
      _ = B * (A * B)ᴴ * (A * C)ᴴ := by
          rw [← conjTranspose_mul A B,
              ← conjTranspose_mul A C]
      _ = B * (A * B) * (A * C) := by rw [hB3, hC3]
      _ = (B * A * B) * A * C := by
          simp only [← Matrix.mul_assoc]
      _ = B * A * C := by rw [hB2]
  have eqB : B = B * A * C := Eq.trans eqB1 eqB2
  have eqC1 : C = Aᴴ * Cᴴ * C := by
    calc C = C * A * C := hC2.symm
      _ = (C * A)ᴴ * C := by rw [hC4]
      _ = Aᴴ * Cᴴ * C := by rw [conjTranspose_mul]
  have eqC2 : Aᴴ * Cᴴ * C = B * A * C := by
    calc Aᴴ * Cᴴ * C
        = (A * B * A)ᴴ * Cᴴ * C := by rw [hB1]
      _ = (Aᴴ * (Bᴴ * Aᴴ)) * Cᴴ * C := by
          rw [conjTranspose_mul, conjTranspose_mul]
      _ = (Aᴴ * Bᴴ) * (Aᴴ * Cᴴ) * C := by
          simp only [← Matrix.mul_assoc]
      _ = (B * A)ᴴ * (C * A)ᴴ * C := by
          rw [← conjTranspose_mul B A,
              ← conjTranspose_mul C A]
      _ = (B * A) * (C * A) * C := by rw [hB4, hC4]
      _ = B * A * (C * A * C) := by
          rw [Matrix.mul_assoc (B * A) (C * A) C]
      _ = B * A * C := by rw [hC2]
  exact Eq.trans eqB (Eq.trans eqC1 eqC2).symm

/-- The Moore–Penrose pseudoinverse of a matrix, defined by lifting to the
geometric pseudoinverse on Euclidean spaces. -/
noncomputable def pinv (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  let e_n : EuclideanSpace 𝕜 n ≃ₗ[𝕜] (n → 𝕜) :=
    WithLp.linearEquiv 2 𝕜 (n → 𝕜)
  let e_m : EuclideanSpace 𝕜 m ≃ₗ[𝕜] (m → 𝕜) :=
    WithLp.linearEquiv 2 𝕜 (m → 𝕜)
  let T : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
    e_m.symm.toLinearMap.comp
      ((Matrix.toLin' A).comp e_n.toLinearMap)
  let T_pinv := LinearMap.pinv T
  LinearMap.toMatrix'
    (e_n.toLinearMap.comp (T_pinv.comp e_m.symm.toLinearMap))

lemma conjTranspose_eq_transpose_real {α β : Type*}
    [Fintype α] [Fintype β] (M : Matrix α β ℝ) : Mᴴ = Mᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- `A.pinv` satisfies all four Moore–Penrose axioms. -/
lemma pinv_isMoorePenroseInverse {m n : Type*} [Fintype m]
    [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n 𝕜) :
    IsMoorePenroseInverse A A.pinv := by
  set e_n := WithLp.linearEquiv 2 𝕜 (n → 𝕜)
  set e_m := WithLp.linearEquiv 2 𝕜 (m → 𝕜)
  set T : EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
    e_m.symm.toLinearMap.comp
      ((Matrix.toLin' A).comp e_n.toLinearMap) with hT_def
  obtain ⟨hTc1, hTc2, hTc3, hTc4⟩ :=
    LinearMap.pinv_satisfies_penroseConditions T
  have h_A_lin :
      Matrix.toLin' A =
        e_m.toLinearMap ∘ₗ (T ∘ₗ e_n.symm.toLinearMap) := by
    apply LinearMap.ext; intro x; simp [hT_def]
  have h_Apinv_lin :
      Matrix.toLin' A.pinv =
        e_n.toLinearMap ∘ₗ
          ((LinearMap.pinv T) ∘ₗ e_m.symm.toLinearMap) := by
    unfold Matrix.pinv
    simp only [Matrix.toLin'_toMatrix']
    rfl
  refine ⟨?cond1, ?cond2, ?cond3, ?cond4⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext; intro x
    simp only [toLin'_mul, h_A_lin, h_Apinv_lin,
      LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_apply_apply,
      EmbeddingLike.apply_eq_iff_eq]
    rw [hTc1 (e_n.symm x)]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext; intro x
    simp only [toLin'_mul, h_Apinv_lin, h_A_lin,
      LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_apply_apply,
      EmbeddingLike.apply_eq_iff_eq]
    rw [hTc2 (e_m.symm x)]
  · ext i j
    have hL : ∀ (M : Matrix m m 𝕜) (u v : m), M u v =
        inner 𝕜 (e_m.symm (Pi.single u 1))
          (e_m.symm (Matrix.toLin' M (Pi.single v 1))) := by
      intro M u v
      have H1 : Matrix.toLin' M (Pi.single v 1) =
          fun k => M k v := by
        ext k; simp [Matrix.toLin'_apply]
      rw [H1]
      simp only [PiLp.inner_apply]
      have H_sum : (∑ k : m,
          inner 𝕜 ((e_m.symm (Pi.single u 1)) k)
            ((e_m.symm (fun x ↦ M x v)) k)) = M u v := by
        have H_sum2 : (∑ k : m,
            inner 𝕜 ((e_m.symm (Pi.single u 1)) k)
              ((e_m.symm (fun x ↦ M x v)) k)) =
            ∑ k : m, if u = k then M u v else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          have h_inner :
              inner 𝕜 ((e_m.symm (Pi.single u 1)) k)
                ((e_m.symm (fun x ↦ M x v)) k) =
              starRingEnd 𝕜 ((Pi.single u 1 : m → 𝕜) k) *
                M k v := by
            dsimp [e_m, e_n]; exact RCLike.inner_apply' _ _
          rw [h_inner]
          by_cases h : u = k
          · rw [h]; simp
          · simp [h]
        rw [H_sum2]; simp
      exact H_sum.symm
    have hR : ∀ (M : Matrix m m 𝕜) (u v : m), Mᴴ u v =
        inner 𝕜
          (e_m.symm (Matrix.toLin' M (Pi.single u 1)))
          (e_m.symm (Pi.single v 1)) := by
      intro M u v
      have H1 : Matrix.toLin' M (Pi.single u 1) =
          fun k => M k u := by
        ext k; simp [Matrix.toLin'_apply]
      rw [H1]
      simp only [PiLp.inner_apply]
      have H_sum : (∑ k : m,
          inner 𝕜 ((e_m.symm (fun x ↦ M x u)) k)
            ((e_m.symm (Pi.single v 1)) k)) = Mᴴ u v := by
        have H_sum2 : (∑ k : m,
            inner 𝕜 ((e_m.symm (fun x ↦ M x u)) k)
              ((e_m.symm (Pi.single v 1)) k)) =
            ∑ k : m, if v = k then Mᴴ u v else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          have h_inner :
              inner 𝕜 ((e_m.symm (fun x ↦ M x u)) k)
                ((e_m.symm (Pi.single v 1)) k) =
              starRingEnd 𝕜 (M k u) *
                (Pi.single v 1 : m → 𝕜) k := by
            dsimp [e_m, e_n]; exact RCLike.inner_apply' _ _
          rw [h_inner]
          by_cases h : v = k
          · rw [h]; simp [Matrix.conjTranspose_apply]
          · simp [h]
        rw [H_sum2]; simp
      exact H_sum.symm
    rw [hR (A * A.pinv) i j, hL (A * A.pinv) i j]
    have h_T_pinv : ∀ (x : m → 𝕜),
        e_m.symm (Matrix.toLin' (A * A.pinv) x) =
          T (LinearMap.pinv T (e_m.symm x)) := by
      intro x
      have h_eq :
          Matrix.toLin' (A * A.pinv) x =
            e_m (T (LinearMap.pinv T (e_m.symm x))) := by
        simp [Matrix.toLin'_mul, h_A_lin, h_Apinv_lin]
      rw [h_eq]; exact LinearEquiv.symm_apply_apply _ _
    rw [h_T_pinv (Pi.single i 1),
        h_T_pinv (Pi.single j 1)]
    exact hTc3 (e_m.symm (Pi.single i 1))
      (e_m.symm (Pi.single j 1))
  · ext i j
    have hL : ∀ (M : Matrix n n 𝕜) (u v : n), M u v =
        inner 𝕜 (e_n.symm (Pi.single u 1))
          (e_n.symm (Matrix.toLin' M (Pi.single v 1))) := by
      intro M u v
      have H1 : Matrix.toLin' M (Pi.single v 1) =
          fun k => M k v := by
        ext k; simp [Matrix.toLin'_apply]
      rw [H1]
      simp only [PiLp.inner_apply]
      have H_sum : (∑ k : n,
          inner 𝕜 ((e_n.symm (Pi.single u 1)) k)
            ((e_n.symm (fun x ↦ M x v)) k)) = M u v := by
        have H_sum2 : (∑ k : n,
            inner 𝕜 ((e_n.symm (Pi.single u 1)) k)
              ((e_n.symm (fun x ↦ M x v)) k)) =
            ∑ k : n, if u = k then M u v else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          have h_inner :
              inner 𝕜 ((e_n.symm (Pi.single u 1)) k)
                ((e_n.symm (fun x ↦ M x v)) k) =
              starRingEnd 𝕜 ((Pi.single u 1 : n → 𝕜) k) *
                M k v := by
            dsimp [e_m, e_n]; exact RCLike.inner_apply' _ _
          rw [h_inner]
          by_cases h : u = k
          · rw [h]; simp
          · simp [h]
        rw [H_sum2]; simp
      exact H_sum.symm
    have hR : ∀ (M : Matrix n n 𝕜) (u v : n), Mᴴ u v =
        inner 𝕜
          (e_n.symm (Matrix.toLin' M (Pi.single u 1)))
          (e_n.symm (Pi.single v 1)) := by
      intro M u v
      have H1 : Matrix.toLin' M (Pi.single u 1) =
          fun k => M k u := by
        ext k; simp [Matrix.toLin'_apply]
      rw [H1]
      simp only [PiLp.inner_apply]
      have H_sum : (∑ k : n,
          inner 𝕜 ((e_n.symm (fun x ↦ M x u)) k)
            ((e_n.symm (Pi.single v 1)) k)) = Mᴴ u v := by
        have H_sum2 : (∑ k : n,
            inner 𝕜 ((e_n.symm (fun x ↦ M x u)) k)
              ((e_n.symm (Pi.single v 1)) k)) =
            ∑ k : n, if v = k then Mᴴ u v else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          have h_inner :
              inner 𝕜 ((e_n.symm (fun x ↦ M x u)) k)
                ((e_n.symm (Pi.single v 1)) k) =
              starRingEnd 𝕜 (M k u) *
                (Pi.single v 1 : n → 𝕜) k := by
            dsimp [e_m, e_n]; exact RCLike.inner_apply' _ _
          rw [h_inner]
          by_cases h : v = k
          · rw [h]; simp [Matrix.conjTranspose_apply]
          · simp [h]
        rw [H_sum2]; simp
      exact H_sum.symm
    rw [hR (A.pinv * A) i j, hL (A.pinv * A) i j]
    have h_pinv_T : ∀ (x : n → 𝕜),
        e_n.symm (Matrix.toLin' (A.pinv * A) x) =
          LinearMap.pinv T (T (e_n.symm x)) := by
      intro x
      have h_eq :
          Matrix.toLin' (A.pinv * A) x =
            e_n (LinearMap.pinv T (T (e_n.symm x))) := by
        simp [Matrix.toLin'_mul, h_A_lin, h_Apinv_lin]
      rw [h_eq]; exact LinearEquiv.symm_apply_apply _ _
    rw [h_pinv_T (Pi.single i 1),
        h_pinv_T (Pi.single j 1)]
    exact hTc4 (e_n.symm (Pi.single i 1))
      (e_n.symm (Pi.single j 1))

variable {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- Scalar multiples commute with `pinv`: `(c • A).pinv = c⁻¹ • A.pinv`. -/
theorem pinv_smul (c : ℝ) (hc : c ≠ 0) (A : Matrix m n ℝ) :
    (c • A).pinv = c⁻¹ • A.pinv := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := pinv_isMoorePenroseInverse A
  apply IsMoorePenroseInverse.unique
    (pinv_isMoorePenroseInverse (c • A))
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : (c • A) * (c⁻¹ • A.pinv) =
        (c * c⁻¹) • (A * A.pinv) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h2 : (c * c⁻¹) • (A * A.pinv) = A * A.pinv := by
      rw [mul_inv_cancel₀ hc, one_smul]
    rw [h1, h2, Matrix.mul_smul, hA1]
  · have h1 : (c⁻¹ • A.pinv) * (c • A) =
        (c⁻¹ * c) • (A.pinv * A) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h2 : (c⁻¹ * c) • (A.pinv * A) = A.pinv * A := by
      rw [inv_mul_cancel₀ hc, one_smul]
    rw [h1, h2, Matrix.mul_smul, hA2]
  · have h1 : (c • A) * (c⁻¹ • A.pinv) =
        (c * c⁻¹) • (A * A.pinv) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h2 : (c * c⁻¹) • (A * A.pinv) = A * A.pinv := by
      rw [mul_inv_cancel₀ hc, one_smul]
    rw [h1, h2]; exact hA3
  · have h1 : (c⁻¹ • A.pinv) * (c • A) =
        (c⁻¹ * c) • (A.pinv * A) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h2 : (c⁻¹ * c) • (A.pinv * A) = A.pinv * A := by
      rw [inv_mul_cancel₀ hc, one_smul]
    rw [h1, h2]; exact hA4

/-- Transposition commutes with `pinv`: `A.pinvᵀ = Aᵀ.pinv`. -/
theorem pinv_transpose (A : Matrix m n ℝ) :
    (A.pinvᵀ) = (Aᵀ).pinv := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := pinv_isMoorePenroseInverse A
  have hA3' : (A * A.pinv)ᵀ = A * A.pinv := by
    rw [← conjTranspose_eq_transpose_real]; exact hA3
  have hA4' : (A.pinv * A)ᵀ = A.pinv * A := by
    rw [← conjTranspose_eq_transpose_real]; exact hA4
  symm
  apply IsMoorePenroseInverse.unique
    (pinv_isMoorePenroseInverse Aᵀ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Aᵀ * A.pinvᵀ * Aᵀ
        = (A.pinv * A)ᵀ * Aᵀ := by
          rw [← Matrix.transpose_mul]
      _ = (A * (A.pinv * A))ᵀ := by
          rw [← Matrix.transpose_mul]
      _ = (A * A.pinv * A)ᵀ := by
          rw [← Matrix.mul_assoc]
      _ = Aᵀ := by rw [hA1]
  · calc A.pinvᵀ * Aᵀ * A.pinvᵀ
        = (A * A.pinv)ᵀ * A.pinvᵀ := by
          rw [← Matrix.transpose_mul]
      _ = (A.pinv * (A * A.pinv))ᵀ := by
          rw [← Matrix.transpose_mul]
      _ = (A.pinv * A * A.pinv)ᵀ := by
          rw [← Matrix.mul_assoc]
      _ = A.pinvᵀ := by rw [hA2]
  · rw [conjTranspose_eq_transpose_real]
    calc (Aᵀ * A.pinvᵀ)ᵀ
        = A.pinvᵀᵀ * Aᵀᵀ := by rw [Matrix.transpose_mul]
      _ = A.pinv * A := by
          rw [Matrix.transpose_transpose,
              Matrix.transpose_transpose]
      _ = (A.pinv * A)ᵀ := hA4'.symm
      _ = Aᵀ * A.pinvᵀ := by rw [Matrix.transpose_mul]
  · rw [conjTranspose_eq_transpose_real]
    calc (A.pinvᵀ * Aᵀ)ᵀ
        = Aᵀᵀ * A.pinvᵀᵀ := by rw [Matrix.transpose_mul]
      _ = A * A.pinv := by
          rw [Matrix.transpose_transpose,
              Matrix.transpose_transpose]
      _ = (A * A.pinv)ᵀ := hA3'.symm
      _ = A.pinvᵀ * Aᵀ := by rw [Matrix.transpose_mul]

/-- `A * (AᵀA)⁺ * (AᵀA) = A`. -/
theorem mul_pinv_mul_transpose_mul_self (A : Matrix m n ℝ) :
    A * (Aᵀ * A).pinv * (Aᵀ * A) = A := by
  set Q := Aᵀ * A with hQ_def
  set P := Q.pinv * Q with hP_def
  obtain ⟨hQ1, _, _, hQ4⟩ := pinv_isMoorePenroseInverse Q
  have hQ_sym : Qᵀ = Q := by
    simp [hQ_def, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hP_symm : Pᵀ = P := by
    rw [hP_def, ← conjTranspose_eq_transpose_real]
    exact hQ4
  have hQ_P : Q * P = Q := by
    rw [hP_def, ← Matrix.mul_assoc, hQ1]
  have hPQ : P * Q = Q := by
    calc P * Q
        = ((P * Q)ᵀ)ᵀ := (Matrix.transpose_transpose _).symm
      _ = (Qᵀ * Pᵀ)ᵀ := by rw [Matrix.transpose_mul]
      _ = (Q * P)ᵀ := by rw [hQ_sym, hP_symm]
      _ = Qᵀ := by rw [hQ_P]
      _ = Q := hQ_sym
  have hFrob : (A * P - A)ᵀ * (A * P - A) = 0 := by
    have h_expand :
        (A * P - A)ᵀ * (A * P - A) =
          (P - 1) * Q * (P - 1) := by
      calc (A * P - A)ᵀ * (A * P - A)
        _ = (A * (P - 1))ᵀ * (A * (P - 1)) := by
            simp only [Matrix.mul_sub, Matrix.mul_one]
        _ = (P - 1)ᵀ * Aᵀ * (A * (P - 1)) := by
            rw [Matrix.transpose_mul]
        _ = (P - 1)ᵀ * (Aᵀ * A) * (P - 1) := by
            simp only [Matrix.mul_assoc]
        _ = (Pᵀ - 1) * Q * (P - 1) := by
            rw [Matrix.transpose_sub,
                Matrix.transpose_one, ← hQ_def]
        _ = (P - 1) * Q * (P - 1) := by rw [hP_symm]
    rw [h_expand, Matrix.sub_mul, Matrix.one_mul, hPQ,
        sub_self, Matrix.zero_mul]
  suffices hAPeqA : A * P = A by
    calc A * (Aᵀ * A).pinv * (Aᵀ * A)
        = A * ((Aᵀ * A).pinv * (Aᵀ * A)) := by
          rw [Matrix.mul_assoc]
      _ = A * P := rfl
      _ = A := hAPeqA
  ext i j
  have h_sum_sq : ∑ k, ((A * P) k j - A k j) ^ 2 = 0 := by
    have h_diag :
        ((A * P - A)ᵀ * (A * P - A)) j j = 0 := by
      rw [hFrob]; rfl
    calc ∑ k, ((A * P) k j - A k j) ^ 2
      _ = ∑ k, ((A * P - A)ᵀ j k) *
            ((A * P - A) k j) := by
          apply Finset.sum_congr rfl
          intro k _; rw [sq]; rfl
      _ = ((A * P - A)ᵀ * (A * P - A)) j j := rfl
      _ = 0 := h_diag
  have h_each : (A * P) i j - A i j = 0 := by
    have h_le :
        ((A * P) i j - A i j) ^ 2 ≤
          ∑ k, ((A * P) k j - A k j) ^ 2 :=
      Finset.single_le_sum
        (f := fun k => ((A * P) k j - A k j) ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    rw [h_sum_sq] at h_le
    exact sq_eq_zero_iff.mp (le_antisymm h_le (sq_nonneg _))
  linarith

/-- For nonsingular square matrices, `pinv = inv`. -/
theorem pinv_eq_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hdet : A.det ≠ 0) :
    A.pinv = A⁻¹ := by
  have hA_det : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  apply IsMoorePenroseInverse.unique
    (pinv_isMoorePenroseInverse A)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_nonsing_inv _ hA_det, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_mul _ hA_det, Matrix.one_mul]
  · rw [Matrix.mul_nonsing_inv _ hA_det]
    exact Matrix.conjTranspose_one
  · rw [Matrix.nonsing_inv_mul _ hA_det]
    exact Matrix.conjTranspose_one

/-- `tr(A(AᵀA)⁺Aᵀ) = rank(A)`. -/
theorem trace_mul_pinv_mul_transpose_eq_rank {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (A * (Aᵀ * A).pinv * Aᵀ) =
      (Matrix.rank A : ℝ) := by
  set P := A * (Aᵀ * A).pinv * Aᵀ with hP_def
  have hP_idemp : P * P = P := by
    rw [hP_def]
    obtain ⟨_, hQ2, _, _⟩ :=
      pinv_isMoorePenroseInverse (Aᵀ * A)
    have h_rearrange :
        A * (Aᵀ * A).pinv * Aᵀ *
          (A * (Aᵀ * A).pinv * Aᵀ) =
        A * ((Aᵀ * A).pinv * (Aᵀ * A) *
          (Aᵀ * A).pinv) * Aᵀ := by
      simp only [← Matrix.mul_assoc]
    rw [h_rearrange, hQ2]
  have hP_symm : Pᵀ = P := by
    rw [hP_def]
    calc (A * (Aᵀ * A).pinv * Aᵀ)ᵀ
        = Aᵀᵀ * (A * (Aᵀ * A).pinv)ᵀ := by
          rw [Matrix.transpose_mul]
      _ = A * (A * (Aᵀ * A).pinv)ᵀ := by
          rw [Matrix.transpose_transpose]
      _ = A * ((Aᵀ * A).pinvᵀ * Aᵀ) := by
          rw [Matrix.transpose_mul]
      _ = A * (Aᵀ * A).pinvᵀ * Aᵀ := by
          rw [Matrix.mul_assoc]
      _ = A * ((Aᵀ * A)ᵀ).pinv * Aᵀ := by
          rw [pinv_transpose]
      _ = A * (Aᵀ * Aᵀᵀ).pinv * Aᵀ := by
          rw [Matrix.transpose_mul]
      _ = A * (Aᵀ * A).pinv * Aᵀ := by
          rw [Matrix.transpose_transpose]
  have h_trace_rank_P :
      Matrix.trace P = (Matrix.rank P : ℝ) := by
    have hP_herm : P.IsHermitian := by
      change Pᴴ = P
      rw [conjTranspose_eq_transpose_real]
      exact hP_symm
    have h_trace_eq :
        Matrix.trace P =
          ∑ i, hP_herm.eigenvalues i := by
      set S : Matrix (Fin m) (Fin m) ℝ :=
        ↑(hP_herm.eigenvectorUnitary)
      set Si : Matrix (Fin m) (Fin m) ℝ :=
        star (↑(hP_herm.eigenvectorUnitary) :
          Matrix (Fin m) (Fin m) ℝ)
      set D := Matrix.diagonal
        ((@RCLike.ofReal ℝ _) ∘
          IsHermitian.eigenvalues hP_herm)
      have hSiS : Si * S = 1 :=
        UnitaryGroup.star_mul_self _
      have h_spec : P = S * D * Si := by
        have h := hP_herm.spectral_theorem
        rwa [Unitary.conjStarAlgAut_apply] at h
      calc Matrix.trace P
        _ = Matrix.trace (S * (D * Si)) := by
            rw [h_spec, Matrix.mul_assoc]
        _ = Matrix.trace (D * Si * S) := by
            rw [Matrix.trace_mul_comm]
        _ = Matrix.trace (D * (Si * S)) := by
            rw [Matrix.mul_assoc]
        _ = Matrix.trace D := by
            rw [hSiS, Matrix.mul_one]
        _ = ∑ i, IsHermitian.eigenvalues hP_herm i := by
            rw [Matrix.trace_diagonal]
            simp [Function.comp]
    rw [h_trace_eq]
    have h_eig_sq :
        ∀ i, hP_herm.eigenvalues i ^ 2 =
          hP_herm.eigenvalues i := by
      intro i
      set S : Matrix (Fin m) (Fin m) ℝ :=
        ↑(hP_herm.eigenvectorUnitary)
      set Si : Matrix (Fin m) (Fin m) ℝ :=
        star (↑(hP_herm.eigenvectorUnitary) :
          Matrix (Fin m) (Fin m) ℝ)
      set D := Matrix.diagonal
        ((@RCLike.ofReal ℝ _) ∘
          IsHermitian.eigenvalues hP_herm)
      have hSiS : Si * S = 1 :=
        UnitaryGroup.star_mul_self _
      have hSSi : S * Si = 1 :=
        Matrix.mul_eq_one_comm.mp hSiS
      have h_spec : P = S * D * Si := by
        have h := hP_herm.spectral_theorem
        rwa [Unitary.conjStarAlgAut_apply] at h
      have h_D_sq : D * D = D := by
        have h1 : S * (D * D) * Si = S * D * Si := by
          calc S * (D * D) * Si
            _ = (S * D * Si) * (S * D * Si) := by
                simp only [Matrix.mul_assoc]
                rw [← Matrix.mul_assoc Si S (D * Si),
                    hSiS, Matrix.one_mul]
            _ = P * P := by rw [← h_spec]
            _ = P := hP_idemp
            _ = S * D * Si := h_spec
        calc D * D
          _ = 1 * (D * D) * 1 := by
              rw [Matrix.one_mul, Matrix.mul_one]
          _ = Si * S * (D * D) * (S * Si) := by
              rw [hSiS, hSSi]
          _ = Si * (S * (D * D) * Si) * S := by
              simp only [Matrix.mul_assoc]
              rw [hSSi, hSiS]
          _ = Si * (S * D * Si) * S := by rw [h1]
          _ = (Si * S) * D * (Si * S) := by
              simp only [Matrix.mul_assoc]
          _ = D := by
              rw [hSiS, Matrix.one_mul, Matrix.mul_one]
      have h_entry := congr_fun (congr_fun h_D_sq i) i
      dsimp only [D] at h_entry
      simp only [Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply_eq,
        Function.comp_apply] at h_entry
      rw [sq]; exact_mod_cast h_entry
    have h_eig_01 :
        ∀ i, hP_herm.eigenvalues i = 0 ∨
          hP_herm.eigenvalues i = 1 := by
      intro i
      have h := h_eig_sq i
      have : hP_herm.eigenvalues i *
          (hP_herm.eigenvalues i - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)
    conv_lhs =>
      rw [show (∑ i, hP_herm.eigenvalues i) =
        ∑ i, if hP_herm.eigenvalues i = 1
          then (1 : ℝ) else 0 from by
        apply Finset.sum_congr rfl; intro i _
        rcases h_eig_01 i with h | h <;> simp [h]]
    rw [← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one]
    rw [Matrix.IsHermitian.rank_eq_card_non_zero_eigs
        hP_herm]
    congr 1; symm
    apply Fintype.card_of_subtype (Finset.univ.filter _)
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hi; rcases h_eig_01 i with h | h <;> simp_all
    · intro hi; rcases h_eig_01 i with h | h <;> simp_all
  rw [h_trace_rank_P]
  congr 1
  apply Nat.le_antisymm
  · have hP_eq : P = A * ((Aᵀ * A).pinv * Aᵀ) := by
      rw [hP_def, Matrix.mul_assoc]
    rw [hP_eq]; exact Matrix.rank_mul_le_left _ _
  · have h_PA : P * A = A := by
      rw [hP_def]
      calc A * (Aᵀ * A).pinv * Aᵀ * A
          = A * (Aᵀ * A).pinv * (Aᵀ * A) := by
            simp only [← Matrix.mul_assoc]
        _ = A := mul_pinv_mul_transpose_mul_self A
    nth_rw 1 [← h_PA]
    exact Matrix.rank_mul_le_left _ _

/-- If `A T → L` entrywise and `L` is nonsingular, then
`(A T).pinv → L⁻¹` entrywise. -/
theorem tendsto_pinv {A : ℕ → Matrix n n ℝ}
    {L : Matrix n n ℝ}
    (hA : Filter.Tendsto A Filter.atTop (nhds L))
    (hL : L.det ≠ 0) :
    Filter.Tendsto (fun T => (A T).pinv)
      Filter.atTop (nhds L⁻¹) := by
  have h_det_cont :
      Continuous (Matrix.det : Matrix n n ℝ → ℝ) :=
    continuous_id.matrix_det
  have h_det_tend :
      Filter.Tendsto (fun T => (A T).det)
        Filter.atTop (nhds L.det) :=
    (h_det_cont.tendsto L).comp hA
  have h_ev_det : ∀ᶠ T in Filter.atTop,
      (A T).det ≠ 0 :=
    h_det_tend.eventually (isOpen_ne.mem_nhds hL)
  suffices h_inv :
      Filter.Tendsto (fun T => (A T)⁻¹)
        Filter.atTop (nhds L⁻¹) by
    exact h_inv.congr' (by
      filter_upwards [h_ev_det] with T hT
      exact (pinv_eq_inv hT).symm)
  have h_adj_cont :
      Continuous (Matrix.adjugate :
        Matrix n n ℝ → Matrix n n ℝ) :=
    continuous_id.matrix_adjugate
  change Filter.Tendsto
    (fun T => Ring.inverse (A T).det • (A T).adjugate)
    Filter.atTop
    (nhds (Ring.inverse L.det • L.adjugate))
  apply Filter.Tendsto.smul
  · have hri : ∀ (x : ℝ), Ring.inverse x = x⁻¹ :=
      congr_fun Ring.inverse_eq_inv'
    simp only [hri]
    exact (continuousAt_inv₀ (G₀ := ℝ) hL).tendsto.comp
      h_det_tend
  · exact (h_adj_cont.tendsto L).comp hA

end Matrix
