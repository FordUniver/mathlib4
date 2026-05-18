/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness on Hilbert spaces

Hilbert-flavoured restatements of the `LipschitzSmoothWith` API from
`Mathlib.Analysis.Calculus.LipschitzSmooth.Basic` and the descent lemma from
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv`, expressing the derivative via
the gradient `∇` and the inner product `⟪·, ·⟫` rather than `fderiv` and
continuous linear functionals.

For differentiable `f` the two views agree via `inner_gradient_left` from
`Mathlib.Analysis.Calculus.Gradient.Basic`; the wrappers below convert each
fderiv-form statement into its inner-product form under that hypothesis.

## Main results

* `lipschitzWith_fderiv_iff_lipschitzWith_gradient` — the Riesz isomorphism identifies
  `LipschitzWith K (fderiv ℝ f)` with `LipschitzWith K (∇ f)`.
* `CocoerciveWith.lipschitzWith_gradient` — `K`-cocoercivity of the gradient implies
  its `K`-Lipschitz continuity.
* `lipschitzSmoothWith_iff_inner_gradient` — characterisation in gradient form under
  `Differentiable`.
* `LipschitzSmoothWith.inner_gradient_descent_le` — the descent inequality in gradient form.
* `LipschitzSmoothWith.inner_gradient_sub_le` — variance bound on the gradient.
* `Differentiable.lipschitzSmoothWith_of_lipschitzWith_gradient` — descent lemma in
  Hilbert form: a `K`-Lipschitz gradient implies `K`-smoothness.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

open InnerProductSpace
open scoped Gradient RealInnerProductSpace

/-! ### Riesz isomorphism -/

/-- The Riesz isomorphism identifies the Lipschitz constant of the Fréchet derivative with
that of the gradient: `LipschitzWith K (fderiv ℝ f) ↔ LipschitzWith K (∇ f)`. Unconditional —
the gradient is *defined* via Riesz from the fderiv, and Riesz is an isometry. -/
theorem lipschitzWith_fderiv_iff_lipschitzWith_gradient {K : NNReal} {f : F → ℝ} :
    LipschitzWith K (fderiv ℝ f) ↔ LipschitzWith K (∇ f) :=
  toDual_comp_gradient (𝕜 := ℝ) (f := f) ▸ (toDual ℝ F).isometry.lipschitzWith_iff K

/-! ### Co-coercivity -/

/-- A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x, y`. Equivalent to the standard
`(1/K)·‖·‖² ≤ ⟪·,·⟫` form when `0 < K`, but well-defined and meaningful even at `K = 0`
(then forces `∇ f` constant). The conclusion of the Baillon-Haddad theorem. -/
abbrev CocoerciveWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ ↑K * ⟪∇ f y - ∇ f x, y - x⟫

/-- A `K`-cocoercive gradient is `K`-Lipschitz. (One direction of the Baillon-Haddad
characterisation; the reverse requires convexity.) -/
theorem CocoerciveWith.lipschitzWith_gradient {K : NNReal} {f : F → ℝ}
    (h : CocoerciveWith K f) : LipschitzWith K (∇ f) :=
  lipschitzWith_iff_dist_le_mul.mpr fun x y => by
    simp only [dist_eq_norm']
    have hcs : ⟪∇ f y - ∇ f x, y - x⟫ ≤ ‖∇ f y - ∇ f x‖ * ‖y - x‖ := real_inner_le_norm _ _
    nlinarith [h x y, mul_nonneg K.coe_nonneg (norm_nonneg (y - x)),
              mul_le_mul_of_nonneg_left hcs K.coe_nonneg]

/-! ### Inner-product restatements of K-smoothness -/

variable {K : NNReal} {f : F → ℝ}

theorem lipschitzSmoothWith_iff_inner_gradient (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔
      ∀ x y : F, f y ≤ f x + ⟪∇ f x, y - x⟫ + ↑K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv hf]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [inner_gradient_left, dist_eq_norm']

namespace LipschitzSmoothWith

theorem inner_gradient_descent_le (h : LipschitzSmoothWith K f) (x y : F)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + ⟪∇ f x, y - x⟫ + ↑K / 2 * ‖y - x‖ ^ 2 := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_le x y hf

theorem inner_gradient_sub_le (h : LipschitzSmoothWith K f) (x y : F)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    ⟪∇ f y - ∇ f x, y - x⟫ ≤ ↑K * ‖y - x‖ ^ 2 := by
  simp only [← dist_eq_norm', inner_sub_left, inner_gradient_left, ← ContinuousLinearMap.sub_apply]
  exact h.fderiv_sub_apply_le x y hfx hfy

end LipschitzSmoothWith

/-! ### Descent lemma (Hilbert form) -/

/-- **Descent lemma (Hilbert form).** If `f : F → ℝ` is differentiable on a Hilbert space
and its gradient `∇ f` is `K`-Lipschitz, then `f` is `K`-smooth. -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith_gradient {K : NNReal} {f : F → ℝ}
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (∇ f)) : LipschitzSmoothWith K f :=
  hf.lipschitzSmoothWith_of_lipschitzWith (lipschitzWith_fderiv_iff_lipschitzWith_gradient.mpr hL)
