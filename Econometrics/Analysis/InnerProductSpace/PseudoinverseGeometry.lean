/-
Copyright (c) 2026 Frederico Guilherme Nogueira. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederico Guilherme Nogueira
-/

import Mathlib

/-!
# Geometric Pseudoinverse via Orthogonal Projection

This file defines the pseudoinverse of a linear map between finite-dimensional
inner product spaces using the orthogonal complement of the kernel.

## Main definitions

* `LinearMap.restrictKerOrthogonal` : the restriction of `T` to `(ker T)ᗮ`,
  landing in `range T`.
* `LinearMap.restrictKerOrthogonalEquiv` : the linear equivalence
  `(ker T)ᗮ ≃ₗ range T`.
* `LinearMap.pinv` : the geometric pseudoinverse `F →ₗ E`.

## Main results

* `LinearMap.comp_pinv_eq_orthogonalProjection` :
  `T ∘ T† = orthogonalProjection (range T)`.
* `LinearMap.pinv_comp_eq_orthogonalProjection` :
  `T† ∘ T = orthogonalProjection (ker T)ᗮ`.
* `LinearMap.pinv_satisfies_penroseConditions` :
  `T†` satisfies all four Moore–Penrose axioms.
-/

open Submodule LinearMap
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace LinearMap

/-! ### The restriction to the orthogonal complement of the kernel -/

/-- The restriction of `T` to `(ker T)ᗮ`, landing in `range T`. -/
noncomputable def restrictKerOrthogonal (T : E →ₗ[𝕜] F) :
    (LinearMap.ker T)ᗮ →ₗ[𝕜] LinearMap.range T :=
  T.rangeRestrict.comp (Submodule.subtype (LinearMap.ker T)ᗮ)

/-! ### The restriction is an isomorphism -/

/-- The restriction of `T` to `(ker T)ᗮ` is injective. -/
lemma restrictKerOrthogonal_injective (T : E →ₗ[𝕜] F) :
    Function.Injective (restrictKerOrthogonal T) := by
  intro x y hxy
  have h1 : T x.1 = T y.1 := congr_arg Subtype.val hxy
  have h2 : T (x.1 - y.1) = 0 := by rw [map_sub, h1, sub_self]
  have h3 : x.1 - y.1 ∈ LinearMap.ker T := h2
  have h4 : x.1 - y.1 ∈ (LinearMap.ker T)ᗮ := Submodule.sub_mem _ x.2 y.2
  have h5 : x.1 - y.1 ∈ LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ := ⟨h3, h4⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h5
  ext; exact sub_eq_zero.mp h5

/-- The restriction of `T` to `(ker T)ᗮ` is surjective. -/
lemma restrictKerOrthogonal_surjective
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] F) :
    Function.Surjective (restrictKerOrthogonal T) := by
  rintro ⟨y, hy⟩
  rcases LinearMap.mem_range.mp hy with ⟨x, rfl⟩
  have h_mem :
      x - (orthogonalProjection (LinearMap.ker T) x : E) ∈
        (LinearMap.ker T)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal x
  use ⟨x - (orthogonalProjection (LinearMap.ker T) x : E), h_mem⟩
  apply Subtype.ext
  change T (x - (orthogonalProjection (LinearMap.ker T) x : E)) = T x
  have hu :
      T (orthogonalProjection (LinearMap.ker T) x : E) = 0 :=
    LinearMap.mem_ker.mp (orthogonalProjection (LinearMap.ker T) x).2
  rw [map_sub, hu, sub_zero]

/-- The restriction of `T` to `(ker T)ᗮ` is a linear equivalence onto
`range T`. -/
noncomputable def restrictKerOrthogonalEquiv
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] F) :
    (LinearMap.ker T)ᗮ ≃ₗ[𝕜] LinearMap.range T :=
  LinearEquiv.ofBijective (restrictKerOrthogonal T)
    ⟨restrictKerOrthogonal_injective T,
     restrictKerOrthogonal_surjective T⟩

/-! ### The geometric pseudoinverse -/

/-- The geometric pseudoinverse of a linear map `T : E →ₗ F`, defined as the
composition `incl ∘ iso⁻¹ ∘ proj_range` where `iso` is the restriction of `T`
to `(ker T)ᗮ`. -/
noncomputable def pinv
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (T : E →ₗ[𝕜] F) :
    F →ₗ[𝕜] E :=
  let proj_range :=
    (orthogonalProjection (LinearMap.range T) :
      F →ₗ[𝕜] LinearMap.range T)
  let iso_inv := (restrictKerOrthogonalEquiv T).symm.toLinearMap
  let incl := Submodule.subtype (LinearMap.ker T)ᗮ
  incl.comp (iso_inv.comp proj_range)

/-! ### The fundamental computational identity -/

/-- `(restrictKerOrthogonalEquiv T w).val = T w.val`. -/
@[simp]
lemma restrictKerOrthogonalEquiv_val_eq
    [FiniteDimensional 𝕜 E] (T : E →ₗ[𝕜] F)
    (w : (LinearMap.ker T)ᗮ) :
    (restrictKerOrthogonalEquiv T w).val = T w.val := by
  simp only [restrictKerOrthogonalEquiv, LinearEquiv.ofBijective_apply,
    restrictKerOrthogonal, LinearMap.comp_apply, Submodule.subtype_apply]
  rfl

/-! ### T ∘ T† = orthogonal projection onto range T -/

/-- `T (pinv T y) = ↑((range T).orthogonalProjection y)`. -/
theorem comp_pinv_eq_orthogonalProjection
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) (y : F) :
    T (pinv T y) =
      (orthogonalProjection (LinearMap.range T) y : F) := by
  simp only [pinv, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearEquiv.coe_toLinearMap]
  have key := restrictKerOrthogonalEquiv_val_eq T
    ((restrictKerOrthogonalEquiv T).symm
      (orthogonalProjection (LinearMap.range T) y))
  rw [LinearEquiv.apply_symm_apply] at key
  exact key.symm

/-! ### T† ∘ T = orthogonal projection onto (ker T)ᗮ -/

/-- Uniqueness in `(ker T)ᗮ`: elements with the same `T`-image coincide. -/
lemma kerOrth_unique (T : E →ₗ[𝕜] F) {p q : E}
    (hp : p ∈ (LinearMap.ker T)ᗮ) (hq : q ∈ (LinearMap.ker T)ᗮ)
    (hTp : T p = T q) : p = q := by
  have h_diff_ker : p - q ∈ LinearMap.ker T := by
    simp [LinearMap.mem_ker, map_sub, hTp]
  have h_diff_orth : p - q ∈ (LinearMap.ker T)ᗮ :=
    Submodule.sub_mem _ hp hq
  have h_zero : p - q ∈ LinearMap.ker T ⊓ (LinearMap.ker T)ᗮ :=
    Submodule.mem_inf.mpr ⟨h_diff_ker, h_diff_orth⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h_zero
  exact sub_eq_zero.mp h_zero

/-- `pinv T (T x) = ↑((ker T)ᗮ.orthogonalProjection x)`. -/
theorem pinv_comp_eq_orthogonalProjection
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) (x : E) :
    pinv T (T x) =
      (orthogonalProjection (LinearMap.ker T)ᗮ x : E) := by
  apply kerOrth_unique T
  · -- pinv T (T x) ∈ (ker T)ᗮ : by construction
    simp only [pinv, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap]
    exact ((restrictKerOrthogonalEquiv T).symm _).2
  · -- ↑(proj⊥ x) ∈ (ker T)ᗮ : by definition
    exact (orthogonalProjection (LinearMap.ker T)ᗮ x).2
  · -- T (pinv T (T x)) = T ↑(proj⊥ x)
    have h1 :
        T (pinv T (T x)) =
          (orthogonalProjection (LinearMap.range T) (T x) : F) :=
      comp_pinv_eq_orthogonalProjection T (T x)
    have h2 :
        (orthogonalProjection (LinearMap.range T) (T x) : F) =
          T x :=
      Submodule.starProjection_eq_self_iff.mpr
        (LinearMap.mem_range_self T x)
    rw [h1, h2]
    have h_decomp :
        (orthogonalProjection (LinearMap.ker T) x : E) +
          (orthogonalProjection (LinearMap.ker T)ᗮ x : E) = x :=
      Submodule.starProjection_add_starProjection_orthogonal x
    have h_proj_ker :
        T (orthogonalProjection (LinearMap.ker T) x : E) = 0 :=
      LinearMap.mem_ker.mp
        (orthogonalProjection (LinearMap.ker T) x).2
    calc T x
        = T ((orthogonalProjection (LinearMap.ker T) x : E) +
             (orthogonalProjection (LinearMap.ker T)ᗮ x : E)) := by
          congr 1; exact h_decomp.symm
      _ = T (orthogonalProjection (LinearMap.ker T) x : E) +
          T (orthogonalProjection (LinearMap.ker T)ᗮ x : E) :=
          map_add T _ _
      _ = 0 +
          T (orthogonalProjection (LinearMap.ker T)ᗮ x : E) := by
          rw [h_proj_ker]
      _ = T (orthogonalProjection (LinearMap.ker T)ᗮ x : E) :=
          zero_add _

/-! ### All four Moore–Penrose conditions -/

/-- The geometric pseudoinverse satisfies all four Moore–Penrose conditions.
(3) and (4) are self-adjointness of `T ∘ T†` and `T† ∘ T`, which hold because
orthogonal projections are self-adjoint.
The `⟪·,·⟫_𝕜` notation is available via `open scoped InnerProductSpace`. -/
theorem pinv_satisfies_penroseConditions
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) :
    (∀ x,       T (pinv T (T x)) = T x) ∧
    (∀ y,       pinv T (T (pinv T y)) = pinv T y) ∧
    (∀ y z : F, ⟪T (pinv T y), z⟫_𝕜 = ⟪y, T (pinv T z)⟫_𝕜) ∧
    (∀ x w : E, ⟪pinv T (T x), w⟫_𝕜 =
                  ⟪x, pinv T (T w)⟫_𝕜) := by
  refine ⟨?cond1, ?cond2, ?cond3, ?cond4⟩
  · -- (1) T ∘ T† ∘ T = T
    intro x
    rw [comp_pinv_eq_orthogonalProjection]
    exact Submodule.starProjection_eq_self_iff.mpr
      (LinearMap.mem_range_self T x)
  · -- (2) T† ∘ T ∘ T† = T†
    intro y
    rw [pinv_comp_eq_orthogonalProjection]
    apply Submodule.starProjection_eq_self_iff.mpr
    simp only [pinv, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_toLinearMap]
    exact ((restrictKerOrthogonalEquiv T).symm _).2
  · -- (3) T ∘ T† is self-adjoint
    intro y z
    simp_rw [comp_pinv_eq_orthogonalProjection]
    exact Submodule.inner_starProjection_left_eq_right
      (LinearMap.range T) y z
  · -- (4) T† ∘ T is self-adjoint
    intro x w
    simp_rw [pinv_comp_eq_orthogonalProjection]
    exact Submodule.inner_starProjection_left_eq_right
      (LinearMap.ker T)ᗮ x w

end LinearMap
