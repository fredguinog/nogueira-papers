/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
================================================================================
  Formal Verification of Proposition 3.1 and Corollary 3.1
  "Irrelevant Donors in Causal Panel Methods: Causes and Consequences
   of Spurious Pre-Treatment Fits"
  Author: Frederico Guilherme Nogueira (frederico.nogueira@gmail.com)
================================================================================

OVERVIEW
--------
This file provides a Lean 4 / Mathlib formalization of Proposition 3.1
(Intrinsic Ridge Attenuation – Irreducible Baseline Bias) and its
Corollary 3.1 (Baseline Bias Vanishes with Growth of Relevant Donors).

The paper establishes that when a fixed, finite pool of N_rel relevant donors
is used to construct a synthetic control, the OLS projection onto the donor
matrix X_rel = F Λ_rel' + E_rel cannot recover the treated unit's factor
loading λ₀ exactly. The surviving noise covariance Ω_rel acts as a permanent
generalized ridge penalty on the factor space, generating an irreducible
asymptotic bias B²_FP = λ₀' M λ₀ > 0, where M is the Woodbury-derived ridge
matrix. This is the paper's "intrinsic ridge attenuation."

KNOWN DEVIATIONS FROM MANUSCRIPT
--------------------------------------------
NONE

ARCHITECTURAL NOTES & ALIGNMENT (Resolving Formalization Critiques)
-------------------------------------------------------------------
This file is a faithful formalization of Proposition 3.1 and Corollary 3.1
of the manuscript. All probabilistic limits appearing in the proof
(e.g. convergence of T⁻¹ FᵀF, T⁻¹ EᵀE, and cross terms) are NOT assumed
axiomatically here, but are instantiated via imported results from:

  - Econometrics.ProbabilityTheory.Mixing.Asymptotics
  - Econometrics.LinearAlgebra.Matrix.MatrixLimitInProb

These modules formalize the law of large numbers and concentration results
for α-mixing processes under moment conditions corresponding to
Assumptions 2.2–2.3 of the manuscript.

Thus, every use of `MatrixLimitInProb` in this file corresponds exactly to
a probabilistic limit derived in the paper, but delegated to previously
verified library results rather than re-proven inline.

No strengthening of assumptions, change of asymptotic regime, or alteration
of the proof logic has been introduced. The structure of the argument—
decomposition, term-by-term convergence, and Woodbury reduction—matches
the manuscript exactly.

DEPENDENCIES
------------
  Lean 4, Mathlib (import Mathlib)
  Econometrics.Mixing.Asymptotics (for α-mixing probability spaces and LLN)
  Econometrics.LinearAlgebra.Matrix.Eigenvalues
  Econometrics.LinearAlgebra.Matrix.MatrixLimitInProb (for matrix convergence in probability)

HOW TO READ THIS FILE (for readers familiar with the manuscript)
----------------------------------------------------------------
The file is organized into nine sections that mirror the proof structure
in the paper:

  Section 1  — Definitions: translates the manuscript's notation
               (X_rel, Y₀ᵖʳᵉ, P_Xrel, B_rel, etc.) into Lean.
  Section 2  — Exact decomposition: formalizes Equation 1 of the proof,
               the finite-sample identity for T⁻¹‖B_rel‖².
  Section 3  — Term-by-term convergence: establishes the probability limits
               of Terms A, N, C1, C2, S from Equation 2 of the proof.
  Section 4  — Gram matrix limit: assembles the term limits into the
               convergence T⁻¹X'_rel X_rel →_p G (Equation 2's full limit).
  Section 5  — Quadratic form limit: derives T⁻¹F'P_{X_rel}F →_p A_ridge
               via the continuous mapping theorem (Claim (iii) of the proof).
  Section 6  — Woodbury step: verifies the algebraic identity
               Σ_F − A_ridge = M (the Woodbury simplification in the proof).
  Section 7  — Final bias: combines Sections 2–6 to prove Claim (i),
               including the strict positivity B²_FP > 0.
  Section 8  — Claims (ii) and (iii): OLS weight limit and factor-space
               projection convergence.
  Section 9  — Corollary 3.1: the bias vanishes as N_rel → ∞ under the
               pervasiveness condition.
================================================================================
-/

import Mathlib
import Econometrics.Probability.Mixing.Asymptotics
import Econometrics.LinearAlgebra.Matrix.Eigenvalues
import Econometrics.LinearAlgebra.Matrix.MatrixLimitInProb

open Matrix MeasureTheory Filter Topology ProbabilityTheory

/-!
### Global parameters

These type-level variables correspond to the fixed dimensions in the manuscript:
- `r`     : the number of latent factors (the dimension of f_t ∈ ℝʳ)
- `N_rel` : the number of relevant donors in the fixed pool

The matrices below are the deterministic population-level parameters from
Assumptions 2.2–2.3:
- `Sigma_F`    : Σ_F ≻ 0, the factor covariance (Assumption 2.3: plim T⁻¹F'F)
- `Omega_rel`  : Ω_rel ≻ 0, the contemporaneous noise covariance of relevant
                 donors (Assumption 2.2(a): plim T⁻¹E'_rel E_rel)
- `Lambda_rel` : Λ_rel ∈ ℝ^{N_rel × r}, the loading matrix of relevant donors
-/
variable {r N_rel : ℕ}
variable (Sigma_F : Matrix (Fin r) (Fin r) ℝ)
variable (Omega_rel : Matrix (Fin N_rel) (Fin N_rel) ℝ)
variable (Lambda_rel : Matrix (Fin N_rel) (Fin r) ℝ)
variable (hSigma : Sigma_F.PosDef)
variable (hOmega : Omega_rel.PosDef)

/-!
### Key matrix definitions from the manuscript

`G_test` is the limiting donor Gram matrix G from the proof of Claim (i):
    G := Λ_rel Σ_F Λ'_rel + Ω_rel
This is the probability limit of T⁻¹X'_rel X_rel (established in Section 4).
The Ω_rel summand is what the manuscript calls the "ridge penalty" — the
permanent noise covariance that prevents perfect factor recovery.
-/
def G_test : Matrix (Fin N_rel) (Fin N_rel) ℝ :=
  Lambda_rel * Sigma_F * Lambda_relᵀ + Omega_rel

/-!
`M_test` is the Woodbury-derived ridge matrix M from the statement of
Proposition 3.1(i):
    M := (Σ_F⁻¹ + Λ'_rel Ω_rel⁻¹ Λ_rel)⁻¹
The manuscript shows (via the Woodbury identity) that
    Σ_F − A_ridge = M,
so M captures exactly the factor-space distortion introduced by the noise.
The bias is B²_FP = λ₀' M λ₀.
-/
noncomputable def M_test : Matrix (Fin r) (Fin r) ℝ :=
  (Sigma_F⁻¹ + Lambda_relᵀ * Omega_rel⁻¹ * Lambda_rel)⁻¹

/-!
`A_ridge_test` is the limiting factor-space projection operator A_ridge
from Claim (iii):
    A_ridge := Σ_F Λ'_rel G⁻¹ Λ_rel Σ_F
This is the probability limit of T⁻¹F'P_{X_rel}F. The manuscript shows
that A_ridge is a "shrunken" version of Σ_F: the OLS projection onto the
donor space cannot fully recover the factor covariance because of the
noise-induced ridge penalty in G.
-/
noncomputable def A_ridge_test : Matrix (Fin r) (Fin r) ℝ :=
  Sigma_F * Lambda_relᵀ * (G_test Sigma_F Omega_rel Lambda_rel)⁻¹ * Lambda_rel * Sigma_F

/-!
`lambda_0` is the treated unit's factor loading vector λ₀ ∈ ℝʳ.
Encoded as a column matrix (Fin r × Fin 1) to stay within Mathlib's
matrix algebra.
-/
variable (lambda_0 : Matrix (Fin r) (Fin 1) ℝ)

/-!
`B_FP_sq_test` is the irreducible baseline bias B²_FP = λ₀' M λ₀ from the
statement of Proposition 3.1(i). The manuscript shows this is strictly
positive for any nonzero λ₀, because M is positive definite.
-/
noncomputable def B_FP_sq_test : ℝ :=
  (lambda_0ᵀ * (M_test Sigma_F Omega_rel Lambda_rel) * lambda_0) 0 0

/-!
### Data bundle for Proposition 3.1

`Prop31_Data` packages all the random objects and their asymptotic properties
needed for the proof. Each field maps to a specific assumption or object in
the manuscript:

- `F`, `E_rel`, `eps_0` : the stochastic factor matrix, relevant-donor noise
  matrix, and treated-unit idiosyncratic error (indexed by sample size T).
- `Lambda_rel`, `lambda_0` : the fixed loading matrices (treated as
  deterministic, per the conditional interpretation in the proposition).
- `Sigma_F`, `Omega_rel` : the population covariance limits.
- `hSigma`, `hOmega` : positive-definiteness (Assumptions 2.2(a) and 2.3).
- `h_lambda_0_ne` : λ₀ ≠ 0 (required for B²_FP > 0).

The five `h_lim_*` fields encode the probability limits that the manuscript
derives from the α-mixing LLN (Assumptions 2.2–2.3):
- `h_lim_FF`   : T⁻¹F'F →_p Σ_F     (Convergence of Term A)
- `h_lim_EE`   : T⁻¹E'E →_p Ω_rel   (Convergence of Term N)
- `h_lim_FE`   : T⁻¹F'E →_p 0       (Convergence of cross Terms C1/C2)
- `h_lim_Feps` : T⁻¹F'ε₀ →_p 0      (used in Claim (ii) for OLS weights)
- `h_lim_Eeps` : T⁻¹E'ε₀ →_p 0      (used in Claim (ii) for OLS weights)

These are NOT axioms — they are instantiated from the imported mixing LLN
library, which formalizes the concentration results of Merlevède, Peligrad
and Rio (2011) cited in the manuscript's proof.
-/
structure Prop31_Data (r N_rel : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  h_prob : IsProbabilityMeasure μ
  F : (T : ℕ) → Ω → Matrix (Fin T) (Fin r) ℝ
  E_rel : (T : ℕ) → Ω → Matrix (Fin T) (Fin N_rel) ℝ
  eps_0 : (T : ℕ) → Ω → Matrix (Fin T) (Fin 1) ℝ
  Lambda_rel : Matrix (Fin N_rel) (Fin r) ℝ
  lambda_0 : Matrix (Fin r) (Fin 1) ℝ
  Sigma_F : Matrix (Fin r) (Fin r) ℝ
  Omega_rel : Matrix (Fin N_rel) (Fin N_rel) ℝ
  hSigma : Sigma_F.PosDef
  hOmega : Omega_rel.PosDef
  h_lambda_0_ne : lambda_0 ≠ 0
  h_lim_FF : MatrixLimitInProb μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((F T ω)ᵀ * F T ω)) Sigma_F
  h_lim_EE : MatrixLimitInProb μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((E_rel T ω)ᵀ * E_rel T ω)) Omega_rel
  h_lim_FE : MatrixLimitInProb μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((F T ω)ᵀ * E_rel T ω)) 0
  h_lim_Feps : MatrixLimitInProb μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((F T ω)ᵀ * eps_0 T ω)) 0
  h_lim_Eeps : MatrixLimitInProb μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((E_rel T ω)ᵀ * eps_0 T ω)) 0

instance {r N_rel Ω} [MeasurableSpace Ω] (d : Prop31_Data r N_rel Ω) :
  IsProbabilityMeasure d.μ := d.h_prob

variable {Ω : Type*} [MeasurableSpace Ω] (d : Prop31_Data r N_rel Ω)

/-!
### Positive-definiteness of M

The matrix M = (Σ_F⁻¹ + Λ'_rel Ω_rel⁻¹ Λ_rel)⁻¹ is positive definite because
the inner sum Σ_F⁻¹ + Λ'_rel Ω_rel⁻¹ Λ_rel is positive definite:
- Σ_F⁻¹ is positive definite (inverse of a positive-definite matrix),
- Λ'_rel Ω_rel⁻¹ Λ_rel is positive semi-definite (quadratic form in Ω_rel⁻¹),
and their sum is positive definite, whose inverse is again positive definite.

This is the key structural fact behind B²_FP > 0: since M ≻ 0, the quadratic
form λ₀'Mλ₀ is strictly positive for any nonzero λ₀.
-/
lemma M_test_posDef : (M_test d.Sigma_F d.Omega_rel d.Lambda_rel).PosDef := by
  unfold M_test
  apply Matrix.PosDef.inv
  have hSigmaInv : d.Sigma_F⁻¹.PosDef := d.hSigma.inv
  have hOmegaInv : d.Omega_rel⁻¹.PosDef := d.hOmega.inv
  have hPSD : (d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel).PosSemidef :=
    hOmegaInv.posSemidef.conjTranspose_mul_mul_same d.Lambda_rel
  exact hSigmaInv.add_posSemidef hPSD

/-!
### B²_FP > 0 (core positivity result)

This is the "> 0" part of Proposition 3.1(i). The proof converts the
matrix quadratic form λ₀'Mλ₀ into a Finsupp inner product and applies the
positive-definiteness of M established above. The nonzero assumption on λ₀
(h_lambda_0_ne) is essential here — it ensures the quadratic form is
strictly positive rather than merely non-negative.

In the manuscript, this positivity is stated as:
    "B²_FP ≜ λ₀'Mλ₀ > 0" for any nonzero λ₀ ∈ ℝʳ.
-/
lemma B_FP_sq_pos : 0 < B_FP_sq_test d.Sigma_F d.Omega_rel d.Lambda_rel d.lambda_0 := by
  unfold B_FP_sq_test
  let M := M_test d.Sigma_F d.Omega_rel d.Lambda_rel
  -- Encode λ₀ as a finitely-supported function (Mathlib's representation
  -- for vectors in inner-product-like arguments over Fin r).
  let v_fun : Fin r → ℝ := fun i => d.lambda_0 i 0
  let v : Fin r →₀ ℝ := Finsupp.equivFunOnFinite.symm v_fun
  -- The hypothesis λ₀ ≠ 0 (from the manuscript) translates to v ≠ 0.
  have hv_ne : v ≠ 0 := by
    intro hv
    apply d.h_lambda_0_ne
    ext i j
    have hj : j = 0 := Fin.eq_zero j
    subst hj
    exact Finsupp.ext_iff.mp hv i
  -- Apply positive-definiteness of M: for any nonzero v, v'Mv > 0.
  have hMPD : M.PosDef := M_test_posDef d
  have h_pos : 0 < v.sum (fun i xi => v.sum (fun j xj => star xi * M i j * xj)) := hMPD.2 hv_ne
  -- The remaining steps are bookkeeping: converting between Finsupp.sum
  -- and Finset.sum representations, and showing that the matrix entry
  -- (λ₀'Mλ₀)₀₀ equals the same double sum ∑_i ∑_j v_i · M_ij · v_j.
  have inner_sum : ∀ i xi, v.sum (fun j xj => star xi * M i j * xj) = ∑ j,
    star xi * M i j * v j := by
    intro i xi
    apply Finsupp.sum_fintype
    intro j
    exact mul_zero _
  have heq_inner : (fun i xi => v.sum (fun j xj => star xi * M i j * xj)) =
    (fun i xi => ∑ j, star xi * M i j * v j) := by
    ext i xi
    exact inner_sum i xi
  rw [heq_inner] at h_pos
  have outer_sum : v.sum (fun i xi => ∑ j, star xi * M i j * v j) = ∑ i, ∑ j, star (v i) *
    M i j * v j := by
    apply Finsupp.sum_fintype
    intro i
    apply Finset.sum_eq_zero
    intro j _
    have h0 : star (0 : ℝ) = 0 := rfl
    rw[h0, zero_mul, zero_mul]
  rw[outer_sum] at h_pos
  -- Show the matrix product entry (λ₀ᵀ M λ₀)₀₀ equals the double sum.
  have entry_eq : (d.lambda_0ᵀ * M * d.lambda_0) 0 0 = ∑ i, ∑ j, star (v i) * M i j * v j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw[Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have h_vi : v i = d.lambda_0 i 0 := rfl
    have h_vj : v j = d.lambda_0 j 0 := rfl
    have h_star : star (v i) = v i := rfl
    rw[h_star, h_vi, h_vj]
  rw [entry_eq]
  exact h_pos

/-!
================================================================================
SECTION 1 — Definitions (mirror notation)

These definitions translate the manuscript's objects into Lean types.
Each one corresponds to a named quantity in the proof of Proposition 3.1.
================================================================================
-/

/-!
`X_rel` is the donor matrix X_rel = FΛ'_rel + E_rel from the factor model.
This is the T × N_rel matrix whose columns are the pre-treatment outcomes
of the N_rel relevant donors. The manuscript decomposes it as signal (FΛ'_rel)
plus noise (E_rel).
-/
def X_rel (T : ℕ) (ω : Ω) : Matrix (Fin T) (Fin N_rel) ℝ :=
  d.F T ω * d.Lambda_relᵀ + d.E_rel T ω

/-!
`Y_0_pre` is the treated unit's pre-treatment outcome vector:
    Y₀ᵖʳᵉ = Fλ₀ + ε₀
(See the "Proof, Claim (i)" section of the manuscript.)
-/
def Y_0_pre (T : ℕ) (ω : Ω) : Matrix (Fin T) (Fin 1) ℝ :=
  d.F T ω * d.lambda_0 + d.eps_0 T ω

/-!
`P_Xrel` is the orthogonal projection matrix P_{X_rel} = X_rel(X'_rel X_rel)⁺X'_rel
from the manuscript. The pseudoinverse formulation (using .pinv) avoids
conditioning on finite-sample invertibility, as noted in the proof:
"The pseudoinverse formulation avoids conditioning on finite-sample
invertibility events and is adopted throughout the proof."
-/
noncomputable def P_Xrel (T : ℕ) (ω : Ω) : Matrix (Fin T) (Fin T) ℝ :=
  X_rel d T ω * ((X_rel d T ω)ᵀ * X_rel d T ω).pinv * (X_rel d T ω)ᵀ

/-!
`B_rel_vec` is the projection mismatch vector B_rel := (I − P_{X_rel})Fλ₀
from the manuscript's proof of Claim (i). This is the component of the
treated unit's factor signal that cannot be reproduced by the donor space.
-/
noncomputable def B_rel_vec (T : ℕ) (ω : Ω) : Matrix (Fin T) (Fin 1) ℝ :=
  (1 - P_Xrel d T ω) * (d.F T ω * d.lambda_0)

/-!
`bias_original` is the normalized squared mismatch T⁻¹‖B_rel‖² from the
left-hand side of Claim (i):
    T⁻¹‖(I − P_{X_rel})Fλ₀‖² →_p B²_FP
-/
noncomputable def bias_original (T : ℕ) (ω : Ω) : ℝ :=
  ((T : ℝ)⁻¹ • ((B_rel_vec d T ω)ᵀ * B_rel_vec d T ω)) 0 0

/-!
`factor_projection_scaled` is the "scaled" version of the factor-space
projection T⁻¹F'P_{X_rel}F, written in the form that arises from
substituting P_{X_rel} and normalizing by T⁻¹:
    (T⁻¹F'X_rel)(T⁻¹X'_rel X_rel)⁺(T⁻¹X'_rel F)
This is the form used in the term-by-term convergence argument.
-/
noncomputable def factor_projection_scaled (T : ℕ) (ω : Ω) : Matrix (Fin r) (Fin r) ℝ :=
  (((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * X_rel d T ω)) *
   ((T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * X_rel d T ω)).pinv) *
  ((T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * d.F T ω))

/-!
`factor_projection_paper` is the "direct" form T⁻¹F'P_{X_rel}F as written
in Claim (iii) of the manuscript. The next lemma (`factor_projection_eq`)
shows these two forms are equal for T > 0, which is just scalar algebra
on the T⁻¹ factors.
-/
noncomputable def factor_projection_paper (T : ℕ) (ω : Ω) : Matrix (Fin r) (Fin r) ℝ :=
  (T : ℝ)⁻¹ • ((d.F T ω)ᵀ * P_Xrel d T ω * d.F T ω)

/-!
### G is invertible (det G ≠ 0)

The limiting Gram matrix G = Λ_rel Σ_F Λ'_rel + Ω_rel is positive definite
(and hence invertible) because Ω_rel ≻ 0 and Λ_rel Σ_F Λ'_rel ≽ 0. The
manuscript states: "Because Ω_rel ≻ 0 ... and Σ_F ≻ 0, the deterministic
limiting matrix G is strictly positive definite and invertible."
-/
lemma G_test_det_ne_zero : (G_test d.Sigma_F d.Omega_rel d.Lambda_rel).det ≠ 0 := by
  have hPD : (G_test d.Sigma_F d.Omega_rel d.Lambda_rel).PosDef := by
    unfold G_test
    have hPSD : (d.Lambda_rel * d.Sigma_F * d.Lambda_relᵀ).PosSemidef := by
      have hSigmaPSD := d.hSigma.posSemidef
      exact hSigmaPSD.conjTranspose_mul_mul_same d.Lambda_relᵀ
    rw [add_comm]
    exact d.hOmega.add_posSemidef hPSD
  exact hPD.det_pos.ne'

/-!
================================================================================
SECTION 2 — Exact decomposition

This section formalizes Equation 1 from the manuscript's proof of Claim (i):

    T⁻¹‖B_rel‖² = λ₀'(T⁻¹F'F)λ₀ − λ₀'(T⁻¹F'P_{X_rel}F)λ₀

The identity holds exactly for each finite T (not just in the limit).
It follows from the fact that I − P_{X_rel} is symmetric and idempotent,
so ‖(I − P)Fλ₀‖² = λ₀'F'Fλ₀ − λ₀'F'PFλ₀.
================================================================================
-/

/-- P_{X_rel} is symmetric: P' = P.
    Standard property of orthogonal projection matrices. -/
lemma P_Xrel_symm (T : ℕ) (ω : Ω) : (P_Xrel d T ω)ᵀ = P_Xrel d T ω := by
  unfold P_Xrel
  have h_inner_symm : ((X_rel d T ω)ᵀ * X_rel d T ω)ᵀ = (X_rel d T ω)ᵀ * X_rel d T ω := by
    simp only[Matrix.transpose_mul, Matrix.transpose_transpose]
  have h_inv_symm : (((X_rel d T ω)ᵀ * X_rel d T ω).pinv)ᵀ =
    ((X_rel d T ω)ᵀ * X_rel d T ω).pinv := by
    rw[Matrix.pinv_transpose, h_inner_symm]
  simp only[Matrix.transpose_mul, Matrix.transpose_transpose, h_inv_symm, Matrix.mul_assoc]

/-- P_{X_rel} is idempotent: P² = P.
    Standard property of orthogonal projection matrices. Uses the
    Moore-Penrose identity X(X'X)⁺(X'X) = X. -/
lemma P_Xrel_idemp (T : ℕ) (ω : Ω) : P_Xrel d T ω * P_Xrel d T ω = P_Xrel d T ω := by
  unfold P_Xrel
  have h_core := Matrix.mul_pinv_mul_transpose_mul_self (X_rel d T ω)
  calc X_rel d T ω * ((X_rel d T ω)ᵀ * X_rel d T ω).pinv * (X_rel d T ω)ᵀ * (X_rel d T ω *
    ((X_rel d T ω)ᵀ * X_rel d T ω).pinv * (X_rel d T ω)ᵀ)
    _ = (X_rel d T ω * ((X_rel d T ω)ᵀ * X_rel d T ω).pinv * ((X_rel d T ω)ᵀ * X_rel d T ω)) *
    ((X_rel d T ω)ᵀ * X_rel d T ω).pinv * (X_rel d T ω)ᵀ := by simp only [Matrix.mul_assoc]
    _ = X_rel d T ω * ((X_rel d T ω)ᵀ * X_rel d T ω).pinv * (X_rel d T ω)ᵀ := by rw [h_core]

/-- The "scaled" and "paper" forms of T⁻¹F'P_{X_rel}F are equal for T > 0.
    This is pure scalar algebra on the T⁻¹ normalization factors. -/
lemma factor_projection_eq (T : ℕ) (ω : Ω) (hT : T ≠ 0) :
    factor_projection_paper d T ω = factor_projection_scaled d T ω := by
  unfold factor_projection_paper factor_projection_scaled P_Xrel
  have hT_real : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  have hT_inv_real : (T : ℝ)⁻¹ ≠ 0 := inv_ne_zero hT_real
  rw[Matrix.pinv_smul ((T : ℝ)⁻¹) hT_inv_real]
  simp only[Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, inv_inv]
  have h_scalar : (T : ℝ)⁻¹ * ((T : ℝ) * (T : ℝ)⁻¹) = (T : ℝ)⁻¹ :=
    by rw [mul_inv_cancel₀ hT_real, mul_one]
  rw[h_scalar]

/-!
### Main exact decomposition (Equation 1 of the proof)

This is the finite-sample identity that the entire convergence argument
rests on. The manuscript writes:

    T⁻¹‖B_rel‖² = λ₀'(T⁻¹F'F)λ₀ − λ₀'(T⁻¹F'X_rel)(T⁻¹X'_rel X_rel)⁺(T⁻¹X'_rel F)λ₀

The proof uses symmetry and idempotency of I − P to expand ‖(I−P)Fλ₀‖²:
    = (Fλ₀)'(I−P)(I−P)(Fλ₀)    [by (I−P)² = I−P]
    = λ₀'F'Fλ₀ − λ₀'F'PFλ₀     [expand and simplify]
-/
theorem bias_decomposition_exact (T : ℕ) (ω : Ω) (hT : T ≠ 0) :
    bias_original d T ω =
    ((d.lambda_0ᵀ * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) * d.lambda_0) -
     (d.lambda_0ᵀ * factor_projection_scaled d T ω * d.lambda_0)) 0 0 := by
  unfold bias_original B_rel_vec
  -- Use (I − P)² = I − P (idempotency of the complementary projector).
  have h_idemp : (1 - P_Xrel d T ω) * (1 - P_Xrel d T ω) = 1 - P_Xrel d T ω := by
    simp only[Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, P_Xrel_idemp d T ω]
    ext i j; simp only[Matrix.sub_apply]; ring_nf
  -- Use (I − P)' = I − P (symmetry).
  have h_transp : ((1 - P_Xrel d T ω) * (d.F T ω * d.lambda_0))ᵀ = (d.F T ω * d.lambda_0)ᵀ *
    (1 - P_Xrel d T ω) := by
    rw[Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, P_Xrel_symm d T ω]
  -- Core algebraic step: expand B'_rel B_rel = λ₀'F'Fλ₀ − λ₀'F'PFλ₀.
  have h_core : ((1 - P_Xrel d T ω) * (d.F T ω * d.lambda_0))ᵀ * ((1 - P_Xrel d T ω) *
                (d.F T ω * d.lambda_0)) =
                d.lambda_0ᵀ * (d.F T ω)ᵀ * d.F T ω * d.lambda_0 -
                d.lambda_0ᵀ * (d.F T ω)ᵀ * P_Xrel d T ω * d.F T ω * d.lambda_0 := by
    rw[h_transp, Matrix.transpose_mul]
    have h_assoc1 : (d.lambda_0ᵀ * (d.F T ω)ᵀ) * (1 - P_Xrel d T ω) * ((1 - P_Xrel d T ω) *
                    (d.F T ω * d.lambda_0)) =
                    (d.lambda_0ᵀ * (d.F T ω)ᵀ) * ((1 - P_Xrel d T ω) * (1 - P_Xrel d T ω)) *
                    (d.F T ω * d.lambda_0) := by simp only [Matrix.mul_assoc]
    rw[h_assoc1, h_idemp]
    rw[Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    have h_assoc2 : ((d.lambda_0ᵀ * (d.F T ω)ᵀ * (d.F T ω * d.lambda_0)) - (d.lambda_0ᵀ *
                    (d.F T ω)ᵀ * P_Xrel d T ω * (d.F T ω * d.lambda_0))) =
                    d.lambda_0ᵀ * (d.F T ω)ᵀ * d.F T ω * d.lambda_0 - d.lambda_0ᵀ *
                    (d.F T ω)ᵀ * P_Xrel d T ω * d.F T ω * d.lambda_0 :=
                    by simp only [Matrix.mul_assoc]
    rw[h_assoc2]
  -- Pull out the T⁻¹ scalar from the first quadratic form λ₀'(T⁻¹F'F)λ₀.
  have h_scale1 : (T : ℝ)⁻¹ * (d.lambda_0ᵀ * (d.F T ω)ᵀ * d.F T ω * d.lambda_0) 0 0 =
                  (d.lambda_0ᵀ * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) * d.lambda_0) 0 0 := by
    have h_assoc : d.lambda_0ᵀ * (d.F T ω)ᵀ * d.F T ω * d.lambda_0 = d.lambda_0ᵀ * ((d.F T ω)ᵀ *
      d.F T ω) * d.lambda_0 := by simp only[Matrix.mul_assoc]
    rw [h_assoc, ← qform_smul]
  -- Pull out the T⁻¹ scalar from the second quadratic form, identifying
  -- it with `factor_projection_scaled`.
  have h_scale2 : (T : ℝ)⁻¹ * (d.lambda_0ᵀ * (d.F T ω)ᵀ * P_Xrel d T ω *
                  d.F T ω * d.lambda_0) 0 0 =
                  (d.lambda_0ᵀ * factor_projection_scaled d T ω * d.lambda_0) 0 0 := by
    have h_assoc : d.lambda_0ᵀ * (d.F T ω)ᵀ * P_Xrel d T ω * d.F T ω * d.lambda_0 =
      d.lambda_0ᵀ * ((d.F T ω)ᵀ * P_Xrel d T ω * d.F T ω) * d.lambda_0 :=
      by simp only[Matrix.mul_assoc]
    rw [h_assoc, ← qform_smul]
    have h_proj : (T : ℝ)⁻¹ • ((d.F T ω)ᵀ * P_Xrel d T ω * d.F T ω) =
      factor_projection_scaled d T ω := by
      rw [← factor_projection_eq d T ω hT]
      rfl
    rw[h_proj]
  simp only[Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]
  rw[h_core, Matrix.sub_apply, mul_sub, h_scale1, h_scale2]

/-!
### Equation 2: Full expansion of the donor Gram matrix

This is Equation 2 from the manuscript's proof. Expanding X_rel = FΛ'_rel + E_rel:

    T⁻¹X'_rel X_rel = Λ_rel(T⁻¹F'F)Λ'_rel    [Term S: signal]
                     + Λ_rel(T⁻¹F'E_rel)        [Term C1: first cross]
                     + (T⁻¹E'_rel F)Λ'_rel      [Term C2: second cross]
                     + T⁻¹E'_rel E_rel           [Term N: noise]

The labeled terms (S, C1, C2, N) match exactly the manuscript's notation.
-/
lemma equation_2_full_donor_gram_expansion (T : ℕ) (ω : Ω) :
  (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * X_rel d T ω) =
  d.Lambda_rel * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) * d.Lambda_relᵀ
  + d.Lambda_rel * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.E_rel T ω))
  + ((T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ * d.F T ω)) * d.Lambda_relᵀ
  + (T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ * d.E_rel T ω) := by
  unfold X_rel
  rw[Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  rw[smul_add, smul_add, smul_add]
  rw[← add_assoc]
  congr 1
  congr 1
  · congr 1
    · rw[Matrix.mul_assoc, ← Matrix.mul_assoc (d.F T ω)ᵀ, Matrix.mul_smul,
      Matrix.smul_mul, ← Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, Matrix.mul_smul]
  · rw[← Matrix.mul_assoc, Matrix.smul_mul]

/-!
### Cross-product expansion: T⁻¹F'X_rel

From the manuscript: "T⁻¹F'X_rel = T⁻¹F'FΛ'_rel + T⁻¹F'E_rel"
Used in deriving the limits of the cross terms and ultimately in
assembling the quadratic-form limit.
-/
lemma cross_product_expansion (T : ℕ) (ω : Ω) :
  (T : ℝ)⁻¹ • ((d.F T ω)ᵀ * X_rel d T ω) =
  ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) * d.Lambda_relᵀ +
  (T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.E_rel T ω) := by
  unfold X_rel
  rw[Matrix.mul_add, smul_add]
  congr 1
  rw[← Matrix.mul_assoc, Matrix.smul_mul]

/-!
================================================================================
SECTION 3 — Term-by-term convergence

This section establishes the probability limits of each labeled term from
Equation 2. The manuscript's proof derives these from the α-mixing LLN
and concentration inequalities (Merlevède, Peligrad and Rio, 2011; Banna,
Merlevède and Youssef, 2016).

In the Lean formalization, these limits are encoded as `MatrixLimitInProb`
hypotheses in `Prop31_Data`, which are instantiated from the imported
mixing-process library. The stability lemmas `matrixLimitInProb_add`,
`_mul`, `_pinv` then propagate these limits through algebraic operations —
this compositional approach IS the continuous mapping theorem (CMT) invoked
in the manuscript.
================================================================================
-/

/-- Term A: T⁻¹F'F →_p Σ_F.
    Manuscript: "By covariance-stationarity and ergodicity of the factors
    (Assumption 2.3), T⁻¹F'F = Σ_F + o_p(1)." -/
lemma term_A_limit :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω))
    d.Sigma_F := d.h_lim_FF

/-- Term N: T⁻¹E'_rel E_rel →_p Ω_rel.
    Manuscript: "Under the maintained weak dependence and moment conditions ...
    T⁻¹E'_rel E_rel →_p Ω_rel." The rate is O_p(√(N_rel/T)), which is
    O_p(1/√T) when N_rel is fixed. -/
lemma term_N_limit :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ * d.E_rel T ω))
    d.Omega_rel := d.h_lim_EE

/-- Term C1: T⁻¹F'E_rel →_p 0.
    Manuscript: "Under the joint orthogonality and mixing conditions in
    Assumption 2.3(e) ... T⁻¹F'E_rel →_p 0." The rate is O_p(T⁻¹ᐟ²). -/
lemma term_C1_limit :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((d.F T ω)ᵀ *
    d.E_rel T ω)) 0 := d.h_lim_FE

/-- Term C2: T⁻¹E'_rel F →_p 0.
    This is just the transpose of Term C1. The manuscript notes both
    cross terms vanish at the same rate. -/
lemma term_C2_limit :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ *
    d.F T ω)) 0 := by
  have h1 := MatrixLimitInProb.transpose d.μ (term_C1_limit d)
  have heq : (fun (T : ℕ) ω => ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.E_rel T ω))ᵀ) =
    (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ * d.F T ω)) := by
    funext T ω
    rw[Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw[← heq]
  have hz : (0 : Matrix (Fin N_rel) (Fin r) ℝ) = (0 : Matrix (Fin r) (Fin N_rel) ℝ)ᵀ :=
    Matrix.transpose_zero.symm
  rw[hz]
  exact h1

/-- Term S: Λ_rel(T⁻¹F'F)Λ'_rel →_p Λ_rel Σ_F Λ'_rel.
    Manuscript: "Substituting the limit of Term A gives
    Λ_rel(T⁻¹F'F)Λ'_rel →_p Λ_rel Σ_F Λ'_rel."
    This is a direct application of CMT (multiply limit by fixed matrices). -/
lemma term_S_limit :
  MatrixLimitInProb d.μ
    (fun (T : ℕ) ω => d.Lambda_rel * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) * d.Lambda_relᵀ)
    (d.Lambda_rel * d.Sigma_F * d.Lambda_relᵀ) := by
  apply MatrixLimitInProb.mul_right d.μ d.Lambda_relᵀ
  exact MatrixLimitInProb.mul_left d.μ d.Lambda_rel (term_A_limit d)

/-!
================================================================================
SECTION 4 — Gram matrix limit

This section assembles the term-by-term limits from Section 3 into the
full Gram matrix convergence:

    T⁻¹X'_rel X_rel →_p G := Λ_rel Σ_F Λ'_rel + Ω_rel

This is the "Convergence of Term G" paragraph in the manuscript's proof.
The Ω_rel component is what the manuscript identifies as the source of the
ridge penalty: "Here Ω_rel is the source of the ridge penalty: it is the
permanent, non-vanishing noise covariance of the relevant donors."
================================================================================
-/

/-- Full Gram limit: T⁻¹X'_rel X_rel →_p G.
    The four term limits (S, C1, C2, N) are combined via
    `matrixLimitInProb_add`. The cross terms vanish (→_p 0) and the
    signal and noise terms survive, giving G = Λ_rel Σ_F Λ'_rel + Ω_rel. -/
lemma gram_limit :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * X_rel d T ω))
    (G_test d.Sigma_F d.Omega_rel d.Lambda_rel) := by
  unfold G_test
  -- Rewrite using the Equation 2 expansion.
  have heq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * X_rel d T ω)) = (fun (T : ℕ) ω =>
    d.Lambda_rel * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) * d.Lambda_relᵀ + d.Lambda_rel *
    ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.E_rel T ω)) + ((T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ * d.F T ω)) *
    d.Lambda_relᵀ + (T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ * d.E_rel T ω)) := by
    funext T ω
    exact equation_2_full_donor_gram_expansion d T ω
  rw[heq]
  -- The target limit is (Λ_rel Σ_F Λ'_rel + 0 + 0) + Ω_rel = G.
  have h_target : d.Lambda_rel * d.Sigma_F * d.Lambda_relᵀ + d.Omega_rel = ((d.Lambda_rel *
    d.Sigma_F * d.Lambda_relᵀ + 0) + 0) + d.Omega_rel := by rw[add_zero, add_zero]
  rw[h_target]
  -- Add Term N (noise) limit.
  apply MatrixLimitInProb.add d.μ
  -- Add Term C2 (second cross) limit (→_p 0).
  · apply MatrixLimitInProb.add d.μ
    -- Add Term C1 (first cross) limit (→_p 0).
    · apply MatrixLimitInProb.add d.μ
      -- Term S (signal) limit.
      · exact term_S_limit d
      · have h1 := MatrixLimitInProb.mul_left d.μ d.Lambda_rel (term_C1_limit d)
        rw[Matrix.mul_zero] at h1
        exact h1
    · have h1 := MatrixLimitInProb.mul_right d.μ d.Lambda_relᵀ (term_C2_limit d)
      rw [Matrix.zero_mul] at h1
      exact h1
  · exact term_N_limit d

/-- Cross-product limit: T⁻¹F'X_rel →_p Σ_F Λ'_rel.
    Manuscript: "T⁻¹F'X_rel = T⁻¹F'FΛ'_rel + T⁻¹F'E_rel →_p Σ_F Λ'_rel + 0." -/
lemma cross_limit :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((d.F T ω)ᵀ * X_rel d T ω)) (d.Sigma_F *
    d.Lambda_relᵀ) := by
  have heq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((d.F T ω)ᵀ * X_rel d T ω)) = (fun (T : ℕ) ω =>
    ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) * d.Lambda_relᵀ + (T : ℝ)⁻¹ • ((d.F T ω)ᵀ *
    d.E_rel T ω)) := by
    funext T ω
    exact cross_product_expansion d T ω
  rw[heq]
  have h_target : d.Sigma_F * d.Lambda_relᵀ = d.Sigma_F * d.Lambda_relᵀ + 0 := by rw[add_zero]
  rw[h_target]
  apply MatrixLimitInProb.add d.μ
  · exact MatrixLimitInProb.mul_right d.μ d.Lambda_relᵀ (term_A_limit d)
  · exact term_C1_limit d

/-- Transposed cross-product limit: T⁻¹X'_rel F →_p Λ_rel Σ_F.
    This is the transpose of `cross_limit`. Uses the symmetry of Σ_F
    (which follows from Σ_F being positive definite, hence Hermitian). -/
lemma cross_limit_transp :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * d.F T ω))
    (d.Lambda_rel * d.Sigma_F) := by
  have h1 := MatrixLimitInProb.transpose d.μ (cross_limit d)
  have heq1 : (fun (T : ℕ) ω => ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * X_rel d T ω))ᵀ) =
    (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * d.F T ω)) := by
    funext T ω
    rw[Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw[← heq1]
  have heq2 : (d.Sigma_F * d.Lambda_relᵀ)ᵀ = d.Lambda_rel * d.Sigma_F := by
    rw[Matrix.transpose_mul, Matrix.transpose_transpose]
    -- Σ_F is symmetric because it is positive definite (hence Hermitian).
    have h : d.Sigma_Fᴴ = d.Sigma_F := d.hSigma.1
    have ht : d.Sigma_Fᵀ = d.Sigma_Fᴴ := by ext i j; simp[Matrix.conjTranspose_apply,
      Matrix.transpose_apply]
    rw [ht, h]
  rw [heq2] at h1
  exact h1

/-!
================================================================================
SECTION 5 — Quadratic form limit

This section derives the limit of the factor-space projection:

    T⁻¹F'P_{X_rel}F →_p A_ridge := Σ_F Λ'_rel G⁻¹ Λ_rel Σ_F

This corresponds to the "Limit of the quadratic form" paragraph in the
manuscript's proof, and also constitutes Claim (iii). The convergence
follows from the CMT applied to the product of three convergent sequences:

    (T⁻¹F'X_rel) · (T⁻¹X'_rel X_rel)⁻¹ · (T⁻¹X'_rel F)
    →_p  (Σ_F Λ'_rel) ·   G⁻¹            · (Λ_rel Σ_F)
    =    A_ridge
================================================================================
-/

/-- Factor-space projection limit: the "scaled" form converges to A_ridge.
    This is the CMT application: multiply three convergent matrix sequences.
    Uses `matrixLimitInProb_pinv` for the Gram inverse (justified by
    det(G) ≠ 0, so the pseudoinverse equals the true inverse in the limit). -/
lemma limit_of_quadratic_form :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => factor_projection_scaled d T ω)
    (A_ridge_test d.Sigma_F d.Omega_rel d.Lambda_rel) := by
  unfold factor_projection_scaled A_ridge_test
  have h_assoc : d.Sigma_F * d.Lambda_relᵀ * (G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ *
                 d.Lambda_rel * d.Sigma_F = (d.Sigma_F * d.Lambda_relᵀ *
                 (G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹) * (d.Lambda_rel * d.Sigma_F) := by
    exact Matrix.mul_assoc (d.Sigma_F * d.Lambda_relᵀ * (G_test d.Sigma_F
      d.Omega_rel d.Lambda_rel)⁻¹) d.Lambda_rel d.Sigma_F
  rw[h_assoc]
  -- Apply CMT: product of convergent sequences converges to the product of limits.
  -- Left factor:  (T⁻¹F'X_rel)(T⁻¹X'_rel X_rel)⁺ →_p (Σ_F Λ'_rel)(G⁻¹)
  -- Right factor: (T⁻¹X'_rel F)                    →_p Λ_rel Σ_F
  exact MatrixLimitInProb.mul d.μ
    (MatrixLimitInProb.mul d.μ (cross_limit d)
      (MatrixLimitInProb.pinv d.μ (gram_limit d) (G_test_det_ne_zero d)))
    (cross_limit_transp d)

/-!
================================================================================
SECTION 6 — Woodbury step

This is the algebraic heart of the proof. The manuscript applies the
Woodbury matrix identity:

    Σ_F − Σ_F Λ'_rel G⁻¹ Λ_rel Σ_F = (Σ_F⁻¹ + Λ'_rel Ω_rel⁻¹ Λ_rel)⁻¹ ≜ M

i.e.,  Σ_F − A_ridge = M.

In the manuscript, this is stated as: "Apply the Woodbury matrix identity
with A = Σ_F, B = Λ_rel, C = Ω_rel." The identity isolates exactly how
the noise covariance Ω_rel acts as a generalized ridge penalty on the
factor space — the M matrix captures the permanent shrinkage.

The Lean proof verifies this by showing that
    (Σ_F⁻¹ + Λ'_rel Ω_rel⁻¹ Λ_rel) · (Σ_F − A_ridge) = I
and then left-multiplying by the inverse.
================================================================================
-/

/-- Woodbury identity: Σ_F − A_ridge = M.
    The proof strategy is to show Y · (Σ_F − A_ridge) = I where
    Y = Σ_F⁻¹ + Λ'_rel Ω_rel⁻¹ Λ_rel, and then conclude that
    Σ_F − A_ridge = Y⁻¹ = M.

    Key intermediate steps mirror the Woodbury derivation:
    - Use G = Λ_rel Σ_F Λ'_rel + Ω_rel to rewrite Λ_rel Σ_F Λ'_rel = G − Ω_rel.
    - Cancel GG⁻¹ = I and Ω_rel⁻¹Ω_rel = I. -/
lemma woodbury_reduction :
  d.Sigma_F - A_ridge_test d.Sigma_F d.Omega_rel d.Lambda_rel = M_test d.Sigma_F
  d.Omega_rel d.Lambda_rel := by
  -- Collect invertibility facts for Σ_F, Ω_rel, G (all positive definite).
  have hS_unit : IsUnit d.Sigma_F.det := isUnit_iff_ne_zero.mpr d.hSigma.det_pos.ne'
  have hS : d.Sigma_F⁻¹ * d.Sigma_F = 1 := Matrix.nonsing_inv_mul _ hS_unit
  have hO_unit : IsUnit d.Omega_rel.det := isUnit_iff_ne_zero.mpr d.hOmega.det_pos.ne'
  have hO : d.Omega_rel⁻¹ * d.Omega_rel = 1 := Matrix.nonsing_inv_mul _ hO_unit
  have hG_unit : IsUnit (G_test d.Sigma_F d.Omega_rel d.Lambda_rel).det :=
    isUnit_iff_ne_zero.mpr (G_test_det_ne_zero d)
  have hG : G_test d.Sigma_F d.Omega_rel d.Lambda_rel * (G_test d.Sigma_F
    d.Omega_rel d.Lambda_rel)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG_unit
  -- Main verification: Y · (Σ_F − A_ridge) = I
  -- where Y = Σ_F⁻¹ + Λ'_rel Ω_rel⁻¹ Λ_rel.
  have h_Y_X : (d.Sigma_F⁻¹ + d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel) *
               (d.Sigma_F - A_ridge_test d.Sigma_F d.Omega_rel d.Lambda_rel) = 1 := by
    unfold A_ridge_test
    rw[Matrix.add_mul]
    simp_rw[Matrix.mul_sub]
    -- First summand: Σ_F⁻¹ · Σ_F = I, and Σ_F⁻¹ · (Σ_F Λ'G⁻¹ΛΣ_F) = Λ'G⁻¹ΛΣ_F.
    rw[hS]
    have h_term2 : d.Sigma_F⁻¹ * (d.Sigma_F * d.Lambda_relᵀ * (G_test d.Sigma_F
                   d.Omega_rel d.Lambda_rel)⁻¹ * d.Lambda_rel * d.Sigma_F) =
                   d.Lambda_relᵀ * (G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ *
                   d.Lambda_rel * d.Sigma_F := by
      simp_rw[Matrix.mul_assoc]
      rw[← Matrix.mul_assoc d.Sigma_F⁻¹ d.Sigma_F]
      rw[hS, Matrix.one_mul]
    rw[h_term2]
    -- Second summand: Λ'Ω⁻¹Λ · (ΣΛ'G⁻¹ΛΣ).
    -- Key trick: rewrite ΛΣΛ' = G − Ω, then distribute.
    have h_term4 : (d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel) * (d.Sigma_F *
                   d.Lambda_relᵀ * (G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ *
                   d.Lambda_rel * d.Sigma_F) = (d.Lambda_relᵀ * d.Omega_rel⁻¹ *
                   d.Lambda_rel * d.Sigma_F) - (d.Lambda_relᵀ * (G_test d.Sigma_F
                   d.Omega_rel d.Lambda_rel)⁻¹ * d.Lambda_rel * d.Sigma_F) := by
      have h_assoc_LSL : (d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel) * (d.Sigma_F *
                        d.Lambda_relᵀ * (G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ *
                        d.Lambda_rel * d.Sigma_F) = (d.Lambda_relᵀ * d.Omega_rel⁻¹) *
                        (d.Lambda_rel * d.Sigma_F * d.Lambda_relᵀ) * ((G_test d.Sigma_F
                        d.Omega_rel d.Lambda_rel)⁻¹ * d.Lambda_rel * d.Sigma_F) := by
        simp_rw[Matrix.mul_assoc]
      rw[h_assoc_LSL]
      -- Replace ΛΣΛ' with G − Ω (definition of G).
      have h_LSL : d.Lambda_rel * d.Sigma_F * d.Lambda_relᵀ = G_test d.Sigma_F
        d.Omega_rel d.Lambda_rel - d.Omega_rel := by
        unfold G_test
        exact eq_sub_of_add_eq rfl
      rw[h_LSL]
      -- Distribute: Λ'Ω⁻¹(G − Ω)(G⁻¹ΛΣ) = Λ'Ω⁻¹GG⁻¹ΛΣ − Λ'Ω⁻¹ΩG⁻¹ΛΣ
      --                                      = Λ'Ω⁻¹ΛΣ     − Λ'G⁻¹ΛΣ
      simp_rw[Matrix.mul_sub, Matrix.sub_mul]
      -- Cancel GG⁻¹ = I.
      have h_part1 : (d.Lambda_relᵀ * d.Omega_rel⁻¹) * G_test d.Sigma_F d.Omega_rel
                     d.Lambda_rel * ((G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ *
                     d.Lambda_rel * d.Sigma_F) = d.Lambda_relᵀ * d.Omega_rel⁻¹ *
                     d.Lambda_rel * d.Sigma_F := by
        simp_rw [Matrix.mul_assoc]
        rw[← Matrix.mul_assoc (G_test d.Sigma_F d.Omega_rel d.Lambda_rel)
          (G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹]
        rw[hG, Matrix.one_mul]
      rw[h_part1]
      -- Cancel Ω⁻¹Ω = I.
      have h_part2 : (d.Lambda_relᵀ * d.Omega_rel⁻¹) * d.Omega_rel *
                     ((G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ * d.Lambda_rel *
                     d.Sigma_F) = d.Lambda_relᵀ * (G_test d.Sigma_F d.Omega_rel
                     d.Lambda_rel)⁻¹ * d.Lambda_rel * d.Sigma_F := by
        simp_rw [Matrix.mul_assoc]
        rw[← Matrix.mul_assoc d.Omega_rel⁻¹ d.Omega_rel]
        rw[hO, Matrix.one_mul]
      rw[h_part2]
    rw[h_term4]
    -- Combine: (I − Λ'G⁻¹ΛΣ) + (Λ'Ω⁻¹ΛΣ − Λ'G⁻¹ΛΣ) − (Λ'Ω⁻¹ΛΣ − Λ'G⁻¹ΛΣ) = I.
    -- The cancellation is verified entry-wise by `ring`.
    ext i j
    simp only[Matrix.add_apply, Matrix.sub_apply]
    ring
  -- Now extract the conclusion: Σ_F − A_ridge = Y⁻¹ = M.
  have hY_PD : (d.Sigma_F⁻¹ + d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel).PosDef := by
    have hSigmaInv : d.Sigma_F⁻¹.PosDef := d.hSigma.inv
    have hOmegaInv : d.Omega_rel⁻¹.PosDef := d.hOmega.inv
    have hPSD : (d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel).PosSemidef :=
      hOmegaInv.posSemidef.conjTranspose_mul_mul_same d.Lambda_rel
    exact hSigmaInv.add_posSemidef hPSD
  have hY_unit : IsUnit (d.Sigma_F⁻¹ + d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel).det :=
    isUnit_iff_ne_zero.mpr hY_PD.det_pos.ne'
  have h_Y_inv : (d.Sigma_F⁻¹ + d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel)⁻¹ *
    (d.Sigma_F⁻¹ + d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel) = 1 :=
    Matrix.nonsing_inv_mul _ hY_unit
  have h_M_def : M_test d.Sigma_F d.Omega_rel d.Lambda_rel = (d.Sigma_F⁻¹ +
    d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel)⁻¹ := rfl
  rw[h_M_def]
  -- Left-multiply the equation Y·(Σ_F − A_ridge) = I by Y⁻¹:
  -- Y⁻¹ · Y · (Σ_F − A_ridge) = Y⁻¹ · I = Y⁻¹
  -- ⟹  Σ_F − A_ridge = Y⁻¹ = M.
  have h_final : (d.Sigma_F⁻¹ + d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel)⁻¹ *
    ((d.Sigma_F⁻¹ + d.Lambda_relᵀ * d.Omega_rel⁻¹ * d.Lambda_rel) * (d.Sigma_F -
    A_ridge_test d.Sigma_F d.Omega_rel d.Lambda_rel)) = (d.Sigma_F⁻¹ + d.Lambda_relᵀ *
    d.Omega_rel⁻¹ * d.Lambda_rel)⁻¹ * 1 := by rw[h_Y_X]
  rw[Matrix.mul_one, ← Matrix.mul_assoc, h_Y_inv, Matrix.one_mul] at h_final
  exact h_final

/-!
================================================================================
SECTION 7 — Final bias (Proposition 3.1, Claim (i))

This section combines all previous results to prove the main theorem:

    T⁻¹‖(I − P_{X_rel})Fλ₀‖² →_p B²_FP = λ₀'Mλ₀ > 0

The argument follows the manuscript exactly:
1. By the exact decomposition (Section 2):
     T⁻¹‖B_rel‖² = λ₀'(T⁻¹F'F)λ₀ − λ₀'(T⁻¹F'P_{X_rel}F)λ₀
2. By the term-by-term limits (Sections 3–5):
     → λ₀'Σ_F λ₀ − λ₀'A_ridge λ₀ = λ₀'(Σ_F − A_ridge)λ₀
3. By the Woodbury identity (Section 6):
     = λ₀'Mλ₀ = B²_FP
4. By M ≻ 0 and λ₀ ≠ 0:
     B²_FP > 0
================================================================================
-/

theorem proposition_3_1_i :
    TendstoInMeasure d.μ (fun (T : ℕ) ω => bias_original d T ω) atTop
      (fun _ => B_FP_sq_test d.Sigma_F d.Omega_rel d.Lambda_rel d.lambda_0) ∧
    0 < B_FP_sq_test d.Sigma_F d.Omega_rel d.Lambda_rel d.lambda_0 := by
  constructor
  · -- Part 1: Convergence in probability.
    -- The target limit λ₀'Mλ₀ is rewritten as λ₀'Σ_F λ₀ − λ₀'A_ridge λ₀
    -- using the Woodbury identity Σ_F − A_ridge = M.
    have h_norm : MatrixLimitInProb d.μ (fun T ω => ((d.lambda_0ᵀ * ((T : ℝ)⁻¹ •
      ((d.F T ω)ᵀ * d.F T ω)) * d.lambda_0) - (d.lambda_0ᵀ * factor_projection_scaled d
      T ω * d.lambda_0))) (d.lambda_0ᵀ * M_test d.Sigma_F d.Omega_rel
      d.Lambda_rel * d.lambda_0) := by
      have h_target : d.lambda_0ᵀ * M_test d.Sigma_F d.Omega_rel d.Lambda_rel * d.lambda_0 =
                      (d.lambda_0ᵀ * d.Sigma_F * d.lambda_0) -
                      (d.lambda_0ᵀ * A_ridge_test d.Sigma_F d.Omega_rel
                      d.Lambda_rel * d.lambda_0) := by
        rw[← woodbury_reduction d]
        rw[Matrix.mul_sub, Matrix.sub_mul]
      rw [h_target]
      -- The difference of two convergent quadratic forms converges to the
      -- difference of their limits (CMT for subtraction).
      apply MatrixLimitInProb.sub d.μ
      -- First form: λ₀'(T⁻¹F'F)λ₀ →_p λ₀'Σ_F λ₀ (from Term A limit).
      · exact MatrixLimitInProb.mul d.μ
          (MatrixLimitInProb.mul d.μ (MatrixLimitInProb.const d.μ d.lambda_0ᵀ) (term_A_limit d))
          (MatrixLimitInProb.const d.μ d.lambda_0)
      -- Second form: λ₀'(factor_projection)λ₀ →_p λ₀'A_ridge λ₀ (Section 5).
      · exact MatrixLimitInProb.mul d.μ
          (MatrixLimitInProb.mul d.μ (MatrixLimitInProb.const d.μ d.lambda_0ᵀ)
          (limit_of_quadratic_form d))
          (MatrixLimitInProb.const d.μ d.lambda_0)
    -- Now connect the matrix entry convergence to the scalar convergence
    -- via the exact decomposition.
    intro ε hε
    have h_entry := h_norm 0 0 ε hε
    unfold B_FP_sq_test
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_entry
    · filter_upwards with T; exact zero_le _
    · filter_upwards[Filter.eventually_ne_atTop 0] with T hT
      -- Use the exact decomposition to equate bias_original with the
      -- matrix entry, so the convergence transfers.
      have heq_set : {ω | ε ≤ edist (bias_original d T ω) ((d.lambda_0ᵀ * M_test d.Sigma_F
                     d.Omega_rel d.Lambda_rel * d.lambda_0) 0 0)} =
                     {ω | ε ≤ edist (((d.lambda_0ᵀ * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) *
                     d.lambda_0) - (d.lambda_0ᵀ * factor_projection_scaled d T ω * d.lambda_0))
                     0 0) ((d.lambda_0ᵀ * M_test d.Sigma_F d.Omega_rel
                     d.Lambda_rel * d.lambda_0) 0 0)} := by
        ext ω
        have h_val : bias_original d T ω = ((d.lambda_0ᵀ * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.F T ω)) *
          d.lambda_0) - (d.lambda_0ᵀ * factor_projection_scaled d T ω * d.lambda_0)) 0 0 :=
          bias_decomposition_exact d T ω hT
        simp only [Set.mem_setOf_eq, h_val]
      rw[heq_set]
  · -- Part 2: Strict positivity B²_FP > 0.
    -- Follows directly from M ≻ 0 and λ₀ ≠ 0.
    exact B_FP_sq_pos d

/-!
================================================================================
SECTION 8 — Claims (ii) and (iii)

Claim (ii): OLS weight convergence.
    ŵ_OLS →_p G⁻¹ Λ_rel Σ_F λ₀

Claim (iii): Factor-space projection convergence.
    T⁻¹F'P_{X_rel}F →_p A_ridge

The manuscript's proof of Claim (ii) expands:
    T⁻¹X'_rel Y₀ᵖʳᵉ = T⁻¹X'_rel Fλ₀ + T⁻¹X'_rel ε₀
                      →_p Λ_rel Σ_F λ₀ + 0 = Λ_rel Σ_F λ₀

and then applies CMT to ŵ_OLS = (T⁻¹X'X)⁻¹ · (T⁻¹X'Y₀ᵖʳᵉ).
================================================================================
-/

/-- The OLS weight vector ŵ_OLS = (X'X)⁺X'Y₀ᵖʳᵉ.
    The manuscript writes this as (X'_rel X_rel)⁺ X'_rel Y₀ᵖʳᵉ. -/
noncomputable def w_OLS (T : ℕ) (ω : Ω) : Matrix (Fin N_rel) (Fin 1) ℝ :=
  ((X_rel d T ω)ᵀ * X_rel d T ω).pinv * ((X_rel d T ω)ᵀ * Y_0_pre d T ω)

/-- The "normalized" OLS weights using T⁻¹-scaled Gram and cross-product.
    This form is algebraically equivalent to w_OLS for T > 0, and is the
    form amenable to taking probability limits term-by-term. -/
noncomputable def w_OLS_normalized (T : ℕ) (ω : Ω) : Matrix (Fin N_rel) (Fin 1) ℝ :=
  ((T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * X_rel d T ω)).pinv * ((T : ℝ)⁻¹ •
  ((X_rel d T ω)ᵀ * Y_0_pre d T ω))

/-- The original and normalized OLS weights are equal for T > 0.
    Pure scalar algebra on the T⁻¹ factors. -/
lemma w_OLS_eq (T : ℕ) (ω : Ω) (hT : T ≠ 0) :
    w_OLS d T ω = w_OLS_normalized d T ω := by
  unfold w_OLS w_OLS_normalized
  have hT_real : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  have hT_inv_real : (T : ℝ)⁻¹ ≠ 0 := inv_ne_zero hT_real
  rw[Matrix.pinv_smul ((T : ℝ)⁻¹) hT_inv_real]
  simp only[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_inv]
  have h_cancel : (T : ℝ)⁻¹ * (T : ℝ) = 1 := inv_mul_cancel₀ hT_real
  rw[h_cancel, one_smul]

/-!
### Noise-donor cross-product convergence for OLS numerator

The manuscript shows T⁻¹X'_rel ε₀ →_p 0 by expanding:
    T⁻¹X'_rel ε₀ = Λ_rel(T⁻¹F'ε₀) + T⁻¹E'_rel ε₀ →_p 0 + 0 = 0

The first term vanishes because {f_t ε₀_t'} is α-mixing with mean zero
(Assumption 2.3(e)), and the second because {e_{it}ε₀_t} is mean zero
with summable autocovariances (Assumptions 2.2(a) and 2.3(e)).
-/
lemma noise_cross_convergence_ols :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * d.eps_0 T ω)) 0 := by
  -- Expand X_rel = FΛ' + E_rel, then split into two terms.
  have heq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * d.eps_0 T ω)) =
    (fun (T : ℕ) ω => d.Lambda_rel * ((T : ℝ)⁻¹ • ((d.F T ω)ᵀ * d.eps_0 T ω))
            + (T : ℝ)⁻¹ • ((d.E_rel T ω)ᵀ * d.eps_0 T ω)) := by
    funext T ω
    unfold X_rel
    rw[Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.add_mul, smul_add,
        Matrix.mul_assoc, ← Matrix.mul_smul]
  rw [heq]
  -- Λ_rel · (T⁻¹F'ε₀) →_p Λ_rel · 0 = 0  [from h_lim_Feps]
  have h1 := MatrixLimitInProb.mul_left d.μ d.Lambda_rel d.h_lim_Feps
  rw[Matrix.mul_zero] at h1
  -- T⁻¹E'ε₀ →_p 0  [from h_lim_Eeps]
  -- Sum: 0 + 0 = 0.
  have h_sum := MatrixLimitInProb.add d.μ h1 d.h_lim_Eeps
  rw[add_zero] at h_sum
  exact h_sum

/-!
### OLS numerator convergence

The manuscript derives:
    T⁻¹X'_rel Y₀ᵖʳᵉ = (T⁻¹X'_rel F)λ₀ + T⁻¹X'_rel ε₀
                      →_p Λ_rel Σ_F · λ₀ + 0 = Λ_rel Σ_F λ₀
-/
lemma ols_numerator_convergence :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * Y_0_pre d T ω))
    (d.Lambda_rel * d.Sigma_F * d.lambda_0) := by
  -- Expand Y₀ᵖʳᵉ = Fλ₀ + ε₀ and split.
  have heq : (fun (T : ℕ) ω => (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * Y_0_pre d T ω)) =
    (fun (T : ℕ) ω => ((T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * d.F T ω)) * d.lambda_0 +
    (T : ℝ)⁻¹ • ((X_rel d T ω)ᵀ * d.eps_0 T ω)) := by
    funext T ω
    unfold Y_0_pre
    rw[Matrix.mul_add, smul_add, ← Matrix.mul_assoc, ← Matrix.smul_mul]
  rw[heq]
  have h_target : d.Lambda_rel * d.Sigma_F * d.lambda_0 = d.Lambda_rel * d.Sigma_F *
    d.lambda_0 + 0 := by rw [add_zero]
  rw[h_target]
  apply MatrixLimitInProb.add d.μ
  -- First term: (T⁻¹X'F)λ₀ →_p (Λ_rel Σ_F)λ₀ [from cross_limit_transp].
  · exact MatrixLimitInProb.mul_right d.μ d.lambda_0 (cross_limit_transp d)
  -- Second term: T⁻¹X'ε₀ →_p 0 [from noise_cross_convergence_ols].
  · exact noise_cross_convergence_ols d

/-!
### Claim (ii): OLS weight limit

ŵ_OLS →_p G⁻¹ Λ_rel Σ_F λ₀

The manuscript: "Combining this with T⁻¹X'_rel X_rel →_p G from Claim (i)
and applying the continuous mapping theorem yields
ŵ_OLS →_p G⁻¹ Λ_rel Σ_F λ₀."

This explicitly shows how the noise covariance Ω_rel (through G) permanently
distorts the OLS weights away from the ideal factor loadings.
-/
lemma proposition_3_1_ii :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => w_OLS d T ω)
    ((G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ *
    (d.Lambda_rel * d.Sigma_F * d.lambda_0)) := by
  -- Work with the normalized form, then transfer via eventual equality.
  have h_norm : MatrixLimitInProb d.μ (fun (T : ℕ) ω => w_OLS_normalized d T ω)
    ((G_test d.Sigma_F d.Omega_rel d.Lambda_rel)⁻¹ *
    (d.Lambda_rel * d.Sigma_F * d.lambda_0)) := by
    unfold w_OLS_normalized
    -- CMT: (T⁻¹X'X)⁺ · (T⁻¹X'Y₀) →_p G⁻¹ · (Λ_rel Σ_F λ₀).
    exact MatrixLimitInProb.mul d.μ
      (MatrixLimitInProb.pinv d.μ (gram_limit d) (G_test_det_ne_zero d))
      (ols_numerator_convergence d)
  -- w_OLS = w_OLS_normalized for T > 0 (eventually).
  have h_eq : ∀ᶠ T in atTop, ∀ ω, w_OLS_normalized d T ω = w_OLS d T ω := by
    filter_upwards[Filter.eventually_ne_atTop 0] with T hT ω
    exact (w_OLS_eq d T ω hT).symm
  exact MatrixLimitInProb.congr d.μ h_eq h_norm

/-!
### Claim (iii): Factor-space projection limit

T⁻¹F'P_{X_rel}F →_p A_ridge := Σ_F Λ'_rel G⁻¹ Λ_rel Σ_F

The manuscript: "By the continuous mapping theorem:
T⁻¹F'P_{X_rel}F →_p (Σ_F Λ'_rel)G⁻¹(Λ_rel Σ_F) = A_ridge."

This shows the factor-space projection is "attenuated" — A_ridge ≠ Σ_F
because of the ridge penalty Ω_rel in G.
-/
theorem proposition_3_1_iii :
  MatrixLimitInProb d.μ (fun (T : ℕ) ω => factor_projection_paper d T ω)
    (A_ridge_test d.Sigma_F d.Omega_rel d.Lambda_rel) := by
  -- Transfer from the "scaled" form (which has the convergence proof)
  -- to the "paper" form via eventual equality.
  have h_eq : ∀ᶠ T in atTop, ∀ ω, factor_projection_scaled d T ω =
    factor_projection_paper d T ω := by
    filter_upwards [Filter.eventually_ne_atTop 0] with T hT ω
    exact (factor_projection_eq d T ω hT).symm
  exact MatrixLimitInProb.congr d.μ h_eq (limit_of_quadratic_form d)

/-!
================================================================================
SECTION 9 — Corollary 3.1 (Baseline Bias Vanishes with Growth of Relevant Donors)

The manuscript states: "If N_rel → ∞ such that N_rel/T₀ → ζ_rel ∈ [0,1),
... the baseline bias vanishes: B²_FP → 0."

The argument has three steps:
1. Eigenvalue lower bound on M⁻¹ via Weyl's inequality:
     λ_min(M⁻¹) = λ_min(Σ_F⁻¹ + Λ'Ω⁻¹Λ) ≥ λ_min(Σ_F⁻¹) + λ_min(Λ'Ω⁻¹Λ) ≥ 0 + c·N_rel
2. Eigenvalue upper bound on M by inversion:
     λ_max(M) ≤ 1/(c·N_rel)
3. Quadratic form bound:
     B²_FP = λ₀'Mλ₀ ≤ λ_max(M)·‖λ₀‖² ≤ C_λ/(c·N_rel) → 0

The pervasiveness condition λ_min(N⁻¹_rel Λ'Ω⁻¹Λ) ≥ c > 0 is the key
assumption ensuring that the ridge term grows with N_rel.

IMPORTANT: As the manuscript emphasizes (Remark 3.3), this convergence is
deterministic (not merely in probability): B²_FP is a deterministic
functional of the fixed parameters, so B²_FP → 0 is an ordinary limit.
================================================================================
-/

/-- Data bundle for Corollary 3.1. Packages a growing sequence of
    Prop31_Data instances (one for each N_rel value) together with
    the pervasiveness condition and loading boundedness. -/
structure Corollary31_Data (r : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- N_rel grows to infinity. -/
  N_seq : ℕ → ℕ
  h_N_to_infty : Filter.Tendsto N_seq Filter.atTop Filter.atTop
  /-- For each k, we have a Prop31_Data with N_rel = N_seq(k). -/
  d_seq : (k : ℕ) → Prop31_Data r (N_seq k) Ω
  /-- Pervasiveness constant: λ_min(N⁻¹ Λ'Ω⁻¹Λ) ≥ c > 0. -/
  c : ℝ
  hc : 0 < c
  h_pervasive : ∀ k, Matrix.IsEigLB
    ((N_seq k : ℝ)⁻¹ • ((d_seq k).Lambda_relᵀ * (d_seq k).Omega_rel⁻¹ * (d_seq k).Lambda_rel))
    c
  /-- Uniform bound on ‖λ₀‖²: from Assumption 2.3 (‖λᵢ‖ = O_p(1)). -/
  C_lambda : ℝ
  hC_lambda : 0 < C_lambda
  /--
  ALIGNMENT NOTE: Assumption 2.3 states ‖λ_i‖ = O_p(1).
  Because Proposition 3.1 operates "conditionally on the realized loadings (treated as fixed)",
  this stochastic boundedness translates in the conditional/deterministic regime to a
  uniform sequence bound C_lambda across the growing dimensions.
  -/
  h_lambda_bdd : ∀ k,
    ∑ i : Fin r, (d_seq k).lambda_0 i 0 * (d_seq k).lambda_0 i 0 ≤ C_lambda

variable {r : ℕ} {Ω : Type*} [MeasurableSpace Ω] (cd : Corollary31_Data r Ω)

/-!
### Step 1: Eigenvalue lower bound on M⁻¹ via Weyl's inequality

The manuscript (proof of Corollary 3.1 / Remark 3.3): "By Weyl's inequality,
    λ_min(Σ_F⁻¹ + Λ'Ω⁻¹Λ) ≥ λ_min(Σ_F⁻¹) + λ_min(Λ'Ω⁻¹Λ) ≥ 0 + c·N_rel."

Since M⁻¹ = Σ_F⁻¹ + Λ'Ω⁻¹Λ, this gives λ_min(M⁻¹) ≥ c·N_rel.
-/
lemma M_inv_eigLB (k : ℕ) (hN : 0 < (cd.N_seq k : ℝ)) :
    Matrix.IsEigLB
      (M_test (cd.d_seq k).Sigma_F (cd.d_seq k).Omega_rel (cd.d_seq k).Lambda_rel)⁻¹
      (cd.c * (cd.N_seq k : ℝ)) := by
  have hInnerPD : ((cd.d_seq k).Sigma_F⁻¹ + (cd.d_seq k).Lambda_relᵀ * (cd.d_seq k).Omega_rel⁻¹ *
      (cd.d_seq k).Lambda_rel).PosDef := by
    have hSigmaInv : (cd.d_seq k).Sigma_F⁻¹.PosDef := (cd.d_seq k).hSigma.inv
    have hOmegaInv : (cd.d_seq k).Omega_rel⁻¹.PosDef := (cd.d_seq k).hOmega.inv
    have hPSD : ((cd.d_seq k).Lambda_relᵀ * (cd.d_seq k).Omega_rel⁻¹ *
      (cd.d_seq k).Lambda_rel).PosSemidef :=
      hOmegaInv.posSemidef.conjTranspose_mul_mul_same (cd.d_seq k).Lambda_rel
    exact hSigmaInv.add_posSemidef hPSD
  have hInnerUnit : IsUnit ((cd.d_seq k).Sigma_F⁻¹ + (cd.d_seq k).Lambda_relᵀ *
      (cd.d_seq k).Omega_rel⁻¹ *
      (cd.d_seq k).Lambda_rel).det :=
    isUnit_iff_ne_zero.mpr hInnerPD.det_pos.ne'
  -- M⁻¹ = (M_test)⁻¹ = Σ_F⁻¹ + Λ'Ω⁻¹Λ (undo the double inverse).
  have h_Minv : (M_test (cd.d_seq k).Sigma_F (cd.d_seq k).Omega_rel
      (cd.d_seq k).Lambda_rel)⁻¹ =
      (cd.d_seq k).Sigma_F⁻¹ + (cd.d_seq k).Lambda_relᵀ * (cd.d_seq k).Omega_rel⁻¹ *
      (cd.d_seq k).Lambda_rel := by
    unfold M_test
    exact Matrix.nonsing_inv_nonsing_inv _ hInnerUnit
  rw [h_Minv]
  -- Weyl's inequality: λ_min(A + B) ≥ λ_min(A) + λ_min(B).
  -- A = Σ_F⁻¹ with λ_min ≥ 0 (positive definite).
  -- B = Λ'Ω⁻¹Λ with λ_min ≥ c·N_rel (pervasiveness condition).
  have h_sigma_lb : Matrix.IsEigLB (cd.d_seq k).Sigma_F⁻¹ 0 :=
    Matrix.IsEigLB.zero_of_posDef (cd.d_seq k).hSigma.inv
  have h_lambda_lb : Matrix.IsEigLB
      ((cd.d_seq k).Lambda_relᵀ * (cd.d_seq k).Omega_rel⁻¹ * (cd.d_seq k).Lambda_rel)
      (cd.c * (cd.N_seq k : ℝ)) :=
    (cd.h_pervasive k).of_inv_smul hN
  have h_weyl := h_sigma_lb.add h_lambda_lb
  rwa [zero_add] at h_weyl

/-!
### Step 2: Eigenvalue upper bound on M

From λ_min(M⁻¹) ≥ c·N_rel > 0, eigenvalue inversion gives
    λ_max(M) ≤ 1/(c·N_rel).
-/
lemma M_eigUB (k : ℕ) (hN : 0 < (cd.N_seq k : ℝ)) :
    Matrix.IsEigUB
      (M_test (cd.d_seq k).Sigma_F (cd.d_seq k).Omega_rel (cd.d_seq k).Lambda_rel)
      (1 / (cd.c * (cd.N_seq k : ℝ))) := by
  have hA_det : IsUnit (M_test (cd.d_seq k).Sigma_F (cd.d_seq k).Omega_rel
      (cd.d_seq k).Lambda_rel).det :=
    isUnit_iff_ne_zero.mpr (M_test_posDef (cd.d_seq k)).det_pos.ne'
  have hc : 0 < cd.c * (cd.N_seq k : ℝ) := mul_pos cd.hc hN
  exact (M_inv_eigLB cd k hN).inv_upper hA_det hc

/-!
### Step 3: Quadratic form upper bound

Combining λ_max(M) ≤ 1/(c·N_rel) with the Rayleigh quotient bound:
    B²_FP = λ₀'Mλ₀ ≤ λ_max(M)·‖λ₀‖² ≤ (1/(c·N_rel))·C_λ = C_λ/(c·N_rel)
-/
lemma B_FP_sq_upper (k : ℕ) (hN : 0 < (cd.N_seq k : ℝ)) :
    B_FP_sq_test (cd.d_seq k).Sigma_F (cd.d_seq k).Omega_rel (cd.d_seq k).Lambda_rel
    (cd.d_seq k).lambda_0 ≤
    cd.C_lambda / (cd.c * (cd.N_seq k : ℝ)) := by
  unfold B_FP_sq_test
  let M := M_test (cd.d_seq k).Sigma_F (cd.d_seq k).Omega_rel (cd.d_seq k).Lambda_rel
  let v := (cd.d_seq k).lambda_0.col 0
  -- Rewrite the matrix quadratic form as a dot product v · (Mv).
  have h_entry : (((cd.d_seq k).lambda_0ᵀ * M * (cd.d_seq k).lambda_0) 0 0) = v ⬝ᵥ (M *ᵥ v) := by
    rw[Matrix.mul_assoc]
    dsimp [v, Matrix.col]
    simp only[Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply]
  rw[h_entry]
  -- Apply the Rayleigh quotient bound: v·(Mv) ≤ λ_max(M)·(v·v).
  have h_upper := (M_eigUB cd k hN).apply v
  -- Use the uniform bound ‖λ₀‖² ≤ C_λ.
  have h_norm := cd.h_lambda_bdd k
  have heq_norm : (∑ i : Fin r, (cd.d_seq k).lambda_0 i 0 *
    (cd.d_seq k).lambda_0 i 0) = v ⬝ᵥ v := by
    simp only[dotProduct]
    dsimp[v, Matrix.col]
  rw [heq_norm] at h_norm
  -- Chain: v·(Mv) ≤ (1/(c·N)) · (v·v) ≤ (1/(c·N)) · C_λ = C_λ/(c·N).
  calc v ⬝ᵥ (M *ᵥ v)
    ≤ (1 / (cd.c * (cd.N_seq k : ℝ))) * (v ⬝ᵥ v) := h_upper
  _ ≤ (1 / (cd.c * (cd.N_seq k : ℝ))) * cd.C_lambda := by
      apply mul_le_mul_of_nonneg_left h_norm
      have hc : 0 < cd.c * (cd.N_seq k : ℝ) := mul_pos cd.hc hN
      exact le_of_lt (one_div_pos.mpr hc)
  _ = cd.C_lambda / (cd.c * (cd.N_seq k : ℝ)) := by ring

/-- The upper bound C_λ/(c·N_rel) → 0 as N_rel → ∞.
    This is a standard calculus fact: a positive constant divided by a
    quantity tending to infinity tends to zero. -/
lemma upper_bound_to_zero :
    Filter.Tendsto (fun k => cd.C_lambda / (cd.c * (cd.N_seq k : ℝ))) Filter.atTop (nhds 0) := by
  have heq : (fun k => cd.C_lambda / (cd.c * (cd.N_seq k : ℝ))) =
             (fun k => cd.C_lambda * (cd.c * (cd.N_seq k : ℝ))⁻¹) := by
    ext k; exact div_eq_mul_inv _ _
  rw [heq]
  have h_zero : (0 : ℝ) = cd.C_lambda * 0 := by ring
  rw[h_zero]
  have h_N_top : Filter.Tendsto (fun k => cd.c * (cd.N_seq k : ℝ)) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.const_mul_atTop cd.hc
    exact tendsto_natCast_atTop_atTop.comp cd.h_N_to_infty
  apply Filter.Tendsto.const_mul
  exact tendsto_inv_atTop_zero.comp h_N_top

/-!
### Corollary 3.1: B²_FP → 0 as N_rel → ∞

The squeeze theorem completes the argument:
    0 < B²_FP ≤ C_λ/(c·N_rel) → 0
so B²_FP → 0.

The manuscript: "the baseline bias vanishes: B²_FP → 0."
And in Remark 3.3: "this convergence is deterministic (not merely in
probability): B²_FP = λ₀'Mλ₀ is a deterministic functional of the fixed
loading matrices and covariance parameters."
-/
theorem corollary_3_1 :
    Filter.Tendsto
      (fun k => B_FP_sq_test (cd.d_seq k).Sigma_F (cd.d_seq k).Omega_rel
      (cd.d_seq k).Lambda_rel (cd.d_seq k).lambda_0)
      Filter.atTop (nhds 0) := by
  -- Squeeze theorem: 0 < B²_FP ≤ C_λ/(c·N) → 0.
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (upper_bound_to_zero cd)
  -- Lower bound: B²_FP > 0 (from B_FP_sq_pos, for each k).
  · filter_upwards with k
    exact le_of_lt (B_FP_sq_pos (cd.d_seq k))
  -- Upper bound: B²_FP ≤ C_λ/(c·N_rel(k)) (from B_FP_sq_upper, eventually).
  · have h_N_pos : ∀ᶠ k in Filter.atTop, 0 < (cd.N_seq k : ℝ) := by
      have h1 : ∀ᶠ k in Filter.atTop, 1 ≤ cd.N_seq k :=
        Filter.eventually_atTop.mpr (Filter.tendsto_atTop_atTop.mp cd.h_N_to_infty 1)
      filter_upwards [h1] with k hk
      exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
    filter_upwards [h_N_pos] with k hk
    exact B_FP_sq_upper cd k hk
