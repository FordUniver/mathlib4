/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Cocoercivity

A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies

`‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫`

for all `x` and `y`. This file also proves that a `K`-cocoercive gradient is
`K`-Lipschitz.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open scoped Gradient RealInnerProductSpace

/-- A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫` for all `x` and `y`. -/
abbrev CocoerciveWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫

/-- A `K`-cocoercive gradient is `K`-Lipschitz. -/
theorem CocoerciveWith.lipschitzWith_gradient (h : CocoerciveWith K f) : LipschitzWith K (∇ f) :=
  lipschitzWith_iff_dist_le_mul.mpr fun x y ↦ by
    simp only [dist_eq_norm']
    nlinarith [h x y, mul_nonneg K.coe_nonneg (norm_nonneg (y - x)),
      mul_le_mul_of_nonneg_left (real_inner_le_norm (∇ f y - ∇ f x) (y - x)) K.coe_nonneg]
