# Lean Econometrics: Formal Verification for Causal Inference

[![Lean](https://img.shields.io/badge/Lean_4-v4.26-blue.svg)](https://leanprover.github.io/)
[![Mathlib](https://img.shields.io/badge/Mathlib4-v4.26.0-blue.svg)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-MIT-green.svg)](https://opensource.org/licenses/MIT)

**Lean Econometrics** is a formally verified library for causal inference
and econometric theory, built on the
[Lean 4 theorem prover](https://leanprover.github.io/) and
[Mathlib4](https://github.com/leanprover-community/mathlib4).

Every definition, lemma, and theorem in this repository is
machine-checked — eliminating logical gaps, unstated assumptions, and
algebraic errors from advanced econometric proofs.

## Repository Structure
```
Econometrics/
├── Analysis/
│   ├── Asymptotics/
│   │   └── RankSaturation.lean           # Rank saturation and κ-fraction limits
│   └── InnerProductSpace/
│       └── PseudoinverseGeometry.lean    # Geometric pseudoinverse via orthogonal projection
├── LinearAlgebra/
│   └── Matrix/
│       ├── AnnihilatorTrace.lean         # Annihilator projections and trace identities
│       ├── Eigenvalues.lean              # Weyl's inequality and quadratic-form eigenvalue API
│       ├── Instances.lean                # NormedAddCommGroup/NormedSpace/MeasurableSpace for Matrix
│       ├── MatrixLimitInProb.lean        # Matrix-valued convergence in probability
│       ├── MoorePenrose.lean             # Moore–Penrose pseudoinverse: uniqueness, axioms, trace
│       ├── Norms.lean                    # Squared L² norm, L∞ norm, Cauchy–Schwarz
│       ├── SpectralBounds.lean           # Spectral bounds and the master projector estimate
│       └── TraceNorm.lean                # Trace–norm identity ‖Mv‖² = tr(MᵀM · vvᵀ)
├── MeasureTheory/
│   ├── BochnerMatrixCommute.lean         # Commutation of trace and Bochner integral
│   └── PolynomialZeroSet.lean            # Multivariate polynomial zero sets have measure zero
├── Probability/
│   ├── ConditionalMixing.lean            # Conditional mixing bounds and cross-sectional orthogonality
│   ├── ConvergenceInMeasure.lean         # Algebra of convergence in measure
│   ├── CovarianceMatrix.lean             # Covariance matrix and scalar covariance identity
│   ├── LLN/
│   │   └── ChebyshevWLLN.lean            # Chebyshev weak law of large numbers
│   ├── LpConvergence.lean                # L² convergence implies convergence in measure
│   ├── Mixing/
│   │   ├── Alpha.lean                    # α-mixing coefficients and decay conditions
│   │   ├── Asymptotics.lean              # Davidson's Theorem 14.1 and LLN for mixing processes
│   │   ├── Basic.lean                    # Filtrations and σ-algebras for stochastic processes
│   │   ├── Covariance.lean               # Covariance inequality for α-mixing processes
│   │   └── QuadraticFormBound.lean       # AM–GM double-sum bounds for quadratic forms
│   └── RandomMatrix/
│       ├── FullRank.lean                 # Almost sure invertibility of random matrices
│       └── TraceConcentration.lean       # Trace concentration for quadratic forms
└── Nogueira2026a/
    ├── Proposition_3_1.lean              # Intrinsic Ridge Attenuation (Prop 3.1 + Cor 3.1)
    └── Theorem_4_3.lean                  # Geometric Decomposition, Asymptotic Resolution,
                                          # and the Spurious Fit Trap (Lemma 4.2 + Thm 4.3 + Cor 4.4)
```

## Formalized Papers

### Irrelevant Donors in Causal Panel Methods: Causes and Consequences of Spurious Pre-Treatment Fits

**Author:** Frederico Guilherme Nogueira (2026)
· [SSRN Working Paper](#)
· **Namespace:** `Econometrics.Nogueira2026a`

This formalization covers the complete mathematical backbone of the
paper — four main results, each machine-verified from first principles:

| Manuscript Result | Lean Location | What It Proves |
|---|---|---|
| **Proposition 3.1** | `Proposition_3_1.lean` | The irreducible baseline bias B²_FP = λ₀′Mλ₀ > 0 arising from intrinsic ridge attenuation when using a finite pool of relevant donors |
| **Corollary 3.1** | `Proposition_3_1.lean` | B²_FP → 0 as N_rel → ∞ under the pervasiveness condition, via Weyl's eigenvalue inequality |
| **Lemma 4.2** | `Theorem_4_3.lean` | Exact finite-sample 6-term geometric decomposition of the pre-treatment residual |
| **Theorem 4.3** | `Theorem_4_3.lean` | Asymptotic resolution: T⁻¹‖r‖² →ₚ B²_FP · M_FP + δ² · M_δ + σ²(1 − κ) + oₚ(1), with three cross terms vanishing by distinct mechanisms |
| **Corollary 4.4** | `Theorem_4_3.lean` | The Spurious Fit Trap: under differential masking (Assumption 4.1), the δ² term vanishes from the residual despite δ² > 0, making pre-treatment fit diagnostics uninformative about structural identification failure |

The proof architecture separates generic probability theory (the
reusable library) from manuscript-specific arguments, with each
probabilistic limit traced to its source assumption.

## Foundations Library

The `Econometrics/` namespace provides a reusable library bridging
Mathlib4 with econometric theory. Key components:

**Linear Algebra & Matrix Theory**
- Moore–Penrose pseudoinverse: uniqueness, all four Penrose conditions,
  scalar/transpose commutation, trace identity tr(A(AᵀA)⁺Aᵀ) = rank(A)
- Geometric pseudoinverse via orthogonal projection on inner product
  spaces
- Eigenvalue bounds via quadratic forms, Weyl's additive inequality,
  eigenvalue bound inversion
- Annihilator projections, trace identities, spectral bounds

**Measure Theory & Probability**
- Algebra of convergence in measure: addition, multiplication, finite
  sums, products, squeeze lemmas, Cauchy–Schwarz, deterministic lifts
- Matrix-valued convergence in probability with full algebra of limits
- L² → convergence in measure (Chebyshev/Markov)
- α-mixing coefficients, Davidson's covariance inequality (Theorem
  14.1), and LLN for mixing processes
- Polynomial zero sets have Lebesgue measure zero (Fubini induction)
- Almost sure invertibility of absolutely continuous random matrices

**Asymptotic Theory**
- Rank saturation and noise-trace fraction limits
- Trace concentration for quadratic forms at rate O(1/T)
- Conditional mixing bounds and cross-sectional orthogonality WLLN

## Building and Verifying
```bash
git clone https://github.com/yourusername/lean-econometrics.git
cd lean-econometrics
lake update
lake build
```

Requires [elan](https://github.com/leanprover/elan) (the Lean version
manager). The build fetches Mathlib4 automatically via Lake.

To check a single file interactively, open it in VS Code with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

## Contributing

Contributions are welcome — whether extending the foundations library,
formalizing additional econometric results, or improving proof style for
Mathlib4 compatibility. Please open an issue to discuss before
submitting a PR.

## License

MIT. See [LICENSE](./LICENSE).

## Author

**Frederico Guilherme Nogueira** — Director of Data and Econometrics at
[Oppen Social](https://oppen.social/), applying causal inference to
public policy evaluation in Brazil. BSc in Computer Engineering (ITA),
MSc in Artificial Intelligence (Utrecht University).
