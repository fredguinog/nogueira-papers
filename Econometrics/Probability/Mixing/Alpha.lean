/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Econometrics.Probability.Mixing.Basic

/-!
# α-Mixing Coefficients

This file defines strong mixing (α-mixing) for discrete-time stochastic processes
and records the two decay conditions used in the limit theory.

## Main definitions

* `ProbabilityTheory.alphaMixingValues μ S1 S2` : the set of absolute differences
  `|μ(A ∩ B) − μ(A)μ(B)|` ranging over `A ∈ S1`, `B ∈ S2`.
* `ProbabilityTheory.alphaMixingCoeff μ S1 S2` : the supremum of `alphaMixingValues`,
  i.e. the standard α-mixing coefficient between the two event families.
* `ProbabilityTheory.IsAlphaMixing μ X` : the mixing coefficients of `X` tend to zero.
* `ProbabilityTheory.HasPolynomialMixingDecay μ X ρ` : polynomial decay `α(h) ≤ C h^{-ρ}`.

## Implementation notes

`S1` and `S2` are given as `Set (Set Ω)` rather than `MeasurableSpace Ω` to avoid
Lean's typeclass synthesizer conflating the sub-σ-algebra with the ambient one.
The mixing coefficient between the past and future of `X` is then formed by passing
`(pastSigmaAlgebra X s).MeasurableSet'` and `(futureSigmaAlgebra X t).MeasurableSet'`.

## References

* Bradley, R. C. (2007). *Introduction to Strong Mixing Conditions*. Kendrick Press.
* Davidson, J. (1994). *Stochastic Limit Theory*. Oxford University Press.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]

/-! ### The mixing coefficient -/

/-- The set of all absolute differences `|μ(A ∩ B) − μ(A)μ(B)|`
as `A` ranges over `S1` and `B` ranges over `S2`. -/
def alphaMixingValues (μ : Measure Ω) (S1 S2 : Set (Set Ω)) : Set ℝ :=
  { x | ∃ A B, A ∈ S1 ∧ B ∈ S2 ∧
    x = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| }

/-- The α-mixing coefficient between two families of events `S1` and `S2`,
defined as the supremum of `|μ(A ∩ B) − μ(A)μ(B)|` over all `A ∈ S1`, `B ∈ S2`. -/
noncomputable def alphaMixingCoeff (μ : Measure Ω) (S1 S2 : Set (Set Ω)) : ℝ :=
  sSup (alphaMixingValues μ S1 S2)

/-! ### Mixing conditions -/

/-- A process `X` is **α-mixing** (strongly mixing) if the mixing coefficient
`α(h)` between its past up to time `0` and its future from time `h` tends to zero. -/
def IsAlphaMixing (μ : Measure Ω) (X : ℕ → Ω → E) : Prop :=
  Tendsto
    (fun h => alphaMixingCoeff μ
      (pastSigmaAlgebra X 0).MeasurableSet'
      (futureSigmaAlgebra X h).MeasurableSet')
    atTop (nhds 0)

/-- A process `X` has **polynomial mixing decay** with exponent `ρ > 0` if there
exists a constant `C > 0` such that `α(h) ≤ C · h^{-ρ}` for all `h ≥ 1`. -/
def HasPolynomialMixingDecay (μ : Measure Ω) (X : ℕ → Ω → E) (ρ : ℝ) : Prop :=
  ∃ C > 0, ∀ h : ℕ, 1 ≤ h →
    alphaMixingCoeff μ
      (pastSigmaAlgebra X 0).MeasurableSet'
      (futureSigmaAlgebra X h).MeasurableSet'
    ≤ C * (h : ℝ) ^ (-ρ)

end ProbabilityTheory
