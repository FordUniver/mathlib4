/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness on a Hilbert space via the gradient

On a Hilbert space `F`, the Lipschitz-smoothness predicates admit gradient-form
characterisations. The identity `fderiv ℝ f x (y - x) = ⟪∇ f x, y - x⟫`
follows from Riesz representation (`inner_gradient_left`), and the two-sided Taylor bound becomes
`‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K/2 · ‖y - x‖²`.

This file also defines the **`CocoerciveWith K f`** predicate (the conclusion of the
Baillon-Haddad theorem) and the elementary direction `K`-cocoercive ⟹ `K`-Lipschitz
gradient.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {K : NNReal} {f : F → ℝ}

open scoped Gradient RealInnerProductSpace

theorem lipschitzSmoothOnWith_iff_inner_gradient {s : Set F} :
    LipschitzSmoothOnWith ℝ K f s ↔
      (∀ x ∈ s, DifferentiableAt ℝ f x) ∧
        ∀ x ∈ s, ∀ y ∈ s,
          ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothOnWith_iff_fderiv]
  refine and_congr_right fun _ ↦ ?_
  simp only [inner_gradient_left, dist_eq_norm']

theorem lipschitzSmoothWith_iff_inner_gradient :
    LipschitzSmoothWith ℝ K f ↔
      ∀ x y : F, ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv_norm_le]
  simp only [inner_gradient_left, dist_eq_norm']

namespace LipschitzSmoothOnWith

variable {s : Set F}

theorem inner_gradient_norm_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : F} (hx : x ∈ s) {y : F} (hy : y ∈ s) :
    ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  (lipschitzSmoothOnWith_iff_inner_gradient.mp h).2 x hx y hy

theorem inner_gradient_descent_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : F} (hx : x ∈ s) {y : F} (hy : y ∈ s) :
    f y ≤ f x + ⟪∇ f x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2 := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_le hx hy

theorem inner_gradient_descent_ge (h : LipschitzSmoothOnWith ℝ K f s)
    {x : F} (hx : x ∈ s) {y : F} (hy : y ∈ s) :
    f x + ⟪∇ f x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_ge hx hy

theorem inner_gradient_sub_le (h : LipschitzSmoothOnWith ℝ K f s)
    {x : F} (hx : x ∈ s) {y : F} (hy : y ∈ s) :
    ⟪∇ f y - ∇ f x, y - x⟫ ≤ K * ‖y - x‖ ^ 2 := by
  simp only [← dist_eq_norm', inner_sub_left, inner_gradient_left, ← sub_apply]
  exact h.fderiv_sub_apply_le hx hy

end LipschitzSmoothOnWith

namespace LipschitzSmoothWith

theorem inner_gradient_norm_le (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    ‖f y - f x - ⟪∇ f x, y - x⟫‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  lipschitzSmoothWith_iff_inner_gradient.mp h x y

theorem inner_gradient_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    f y ≤ f x + ⟪∇ f x, y - x⟫ + K / 2 * ‖y - x‖ ^ 2 := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_le x y

theorem inner_gradient_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    f x + ⟪∇ f x, y - x⟫ - K / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  rw [inner_gradient_left, ← dist_eq_norm']
  exact h.fderiv_descent_ge x y

theorem inner_gradient_sub_le (h : LipschitzSmoothWith ℝ K f) (x y : F) :
    ⟪∇ f y - ∇ f x, y - x⟫ ≤ K * ‖y - x‖ ^ 2 := by
  simp only [← dist_eq_norm', inner_sub_left, inner_gradient_left, ← sub_apply]
  exact h.fderiv_sub_apply_le x y

end LipschitzSmoothWith

/-! ### Cocoercivity -/

/-- A function `f : F → ℝ` on a Hilbert space is **`K`-cocoercive** if its gradient satisfies
`‖∇ f y - ∇ f x‖² ≤ K · ⟪∇ f y - ∇ f x, y - x⟫` for all `x, y`. Equivalent to the standard
`(1/K)·‖·‖² ≤ ⟪·,·⟫` form when `0 < K`, but well-defined and meaningful even at `K = 0`
(then forces `∇ f` constant). The conclusion of the Baillon-Haddad theorem. -/
abbrev CocoerciveWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ x y : F, ‖∇ f y - ∇ f x‖ ^ 2 ≤ K * ⟪∇ f y - ∇ f x, y - x⟫

/-- A `K`-cocoercive gradient is `K`-Lipschitz. (One direction of the Baillon-Haddad
characterisation; the reverse requires convexity.) -/
theorem CocoerciveWith.lipschitzWith_gradient (h : CocoerciveWith K f) : LipschitzWith K (∇ f) :=
  lipschitzWith_iff_dist_le_mul.mpr fun x y => by
    simp only [dist_eq_norm']
    nlinarith [h x y, mul_nonneg K.coe_nonneg (norm_nonneg (y - x)),
              mul_le_mul_of_nonneg_left (real_inner_le_norm (∇ f y - ∇ f x) (y - x)) K.coe_nonneg]
