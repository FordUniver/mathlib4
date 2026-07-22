/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness in 1D via the derivative

For a `K`-smooth function `f : 𝕜 → F`, the Taylor bound takes its 1D form

`‖f y - f x - (y - x) • deriv f x‖ ≤ K/2 · ‖y - x‖²`,

and `K`-smoothness already implies differentiability in one dimension. The bound is lifted from
the Fréchet-derivative form in
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv` via `fderiv_eq_smul_deriv`.
For real-valued `f` the one-sided bounds take their classical forms

`f y ≤ f x + deriv f x * (y - x) + K/2 · (y - x)²`,
`(deriv f y - deriv f x) * (y - x) ≤ K · (y - x)²`,

with the scalar action spelled as multiplication (`smul_eq_mul` bridges the two).
-/

public section

open Filter Asymptotics
open scoped Topology

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : 𝕜 → F}

/-- A `K`-smooth function in one dimension is differentiable. -/
theorem LipschitzSmoothWith.differentiable (h : LipschitzSmoothWith 𝕜 K f) :
    Differentiable 𝕜 f := fun x => by
  let hx := h.lipschitzSmoothWithAt x
  refine (hx.hasFDerivAt ?_).differentiableAt
  change Continuous (hx.lineDerivLinearMap.toContinuousLinearMap₁ : 𝕜 → F)
  exact hx.lineDerivLinearMap.toContinuousLinearMap₁.continuous

private theorem differentiable_of_deriv_bound
    (h : ∀ x y : 𝕜, ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2) :
    Differentiable 𝕜 f := by
  intro x
  refine (HasDerivAt.of_isLittleO (f' := deriv f x) ?_).differentiableAt
  have hbigO : (fun y => f y - f x - (y - x) • deriv f x) =O[𝓝 x]
      fun y => ‖y - x‖ ^ 2 := by
    refine IsBigO.of_bound (K / 2) (Eventually.of_forall fun y => ?_)
    simpa using h x y
  exact hbigO.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

theorem lipschitzSmoothWith_iff_deriv :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y : 𝕜, ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  constructor
  · intro h
    rw [lipschitzSmoothWith_iff_fderiv h.differentiable] at h
    simpa only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev] using h
  · intro h
    rw [lipschitzSmoothWith_iff_fderiv (differentiable_of_deriv_bound h)]
    simpa only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev] using h

end NormedField

namespace LipschitzSmoothWith

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : 𝕜 → F}

theorem deriv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : 𝕜) :
    ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  simpa only [fderiv_eq_smul_deriv, dist_comm x y, dist_eq_norm]
    using h.fderiv_norm_le x y (h.differentiable x)

end NormedField

/-! ### Real-valued functions -/

section Real

variable {K : NNReal} {f : ℝ → ℝ}

theorem deriv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    f y ≤ f x + deriv f x * (y - x) + K / 2 * (y - x) ^ 2 := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_le x y (h.differentiable x)

theorem deriv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    f x + deriv f x * (y - x) - K / 2 * (y - x) ^ 2 ≤ f y := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_ge x y (h.differentiable x)

theorem deriv_sub_mul_le (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    (deriv f y - deriv f x) * (y - x) ≤ K * (y - x) ^ 2 := by
  simpa only [sub_apply, fderiv_eq_deriv_mul, ← sub_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_sub_apply_le x y (h.differentiable x) (h.differentiable y)

end Real

end LipschitzSmoothWith
