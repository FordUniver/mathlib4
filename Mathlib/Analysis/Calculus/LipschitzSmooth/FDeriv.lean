/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Lipschitz smoothness via the Fréchet derivative

Fréchet-derivative restatements of the `LipschitzSmoothWith` predicate for
`f : E → F`. For differentiable `f`, `lineDeriv 𝕜 f x v = fderiv 𝕜 f x v`
pointwise, and the predicate is equivalent to the two-sided Taylor bound stated
in `fderiv` form. A continuous `K`-smooth function is Fréchet differentiable;
in finite-dimensional spaces over a complete field, continuity follows automatically.
The one-sided descent bounds require an order on the codomain and are stated for
real-valued `f` in a dedicated section.
-/

public section

open Filter Asymptotics
open scoped Topology

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F}

theorem lipschitzSmoothWith_iff_fderiv (hf : Differentiable 𝕜 f) :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y : E, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 := by
  rw [lipschitzSmoothWith_iff_lineDeriv]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [(hf x).lineDeriv_eq_fderiv]

end NormedField

namespace LipschitzSmoothWith

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F}

/-- A `K`-smooth function is Fréchet differentiable at `x` if its linear line-derivative map at
`x` is continuous. -/
theorem differentiableAt_of_continuous_lineDeriv
    (h : LipschitzSmoothWith 𝕜 K f) (x : E)
    (hcont : Continuous (h.lineDerivLinearMap x)) : DifferentiableAt 𝕜 f x := by
  let L : E →L[𝕜] F := ⟨h.lineDerivLinearMap x, hcont⟩
  refine ⟨L, HasFDerivAt.of_isLittleO ?_⟩
  have hbigO : (fun y => f y - f x - L (y - x)) =O[𝓝 x]
      fun y => ‖y - x‖ ^ 2 := by
    refine IsBigO.of_bound (K / 2) (Eventually.of_forall fun y => ?_)
    simpa [L, dist_eq_norm, norm_sub_rev] using h.lineDeriv_norm_le x y
  exact hbigO.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

/-- A `K`-smooth function that is continuous at `x` is Fréchet differentiable at `x`. -/
theorem differentiableAt_of_continuousAt (h : LipschitzSmoothWith 𝕜 K f) {x : E}
    (hf : ContinuousAt f x) : DifferentiableAt 𝕜 f x := by
  let L := h.lineDerivLinearMap x
  let r := fun v : E => f (x + v) - f x - L v
  have hr_bound : ∀ v, ‖r v‖ ≤ K / 2 * ‖v‖ ^ 2 := by
    intro v
    simpa [r, L, dist_self_add_right] using h.lineDeriv_norm_le x (x + v)
  have hr : Tendsto r (𝓝 0) (𝓝 0) :=
    squeeze_zero_norm hr_bound (by
      have : ContinuousAt (fun v : E => K / 2 * ‖v‖ ^ 2) 0 := by fun_prop
      simpa using this.tendsto)
  have hf_inc : Tendsto (fun v : E => f (x + v) - f x) (𝓝 0) (𝓝 0) := by
    have hx : Tendsto (fun v : E => x + v) (𝓝 0) (𝓝 x) := by
      have : ContinuousAt (fun v : E => x + v) 0 := by fun_prop
      simpa using this.tendsto
    have hc : Tendsto (fun _ : E => f x) (𝓝 0) (𝓝 (f x)) := tendsto_const_nhds
    simpa using (hf.tendsto.comp hx).sub hc
  have hL_zero : Tendsto L (𝓝 0) (𝓝 0) := by
    have hlim := hf_inc.sub hr
    convert hlim using 1
    · funext v
      simp only [r]
      module
    · simp
  exact differentiableAt_of_continuous_lineDeriv h x <|
    continuous_of_tendsto_nhds_zero L hL_zero

/-- A continuous `K`-smooth function is Fréchet differentiable. -/
theorem differentiable_of_continuous (h : LipschitzSmoothWith 𝕜 K f)
    (hf : Continuous f) : Differentiable 𝕜 f :=
  fun x => h.differentiableAt_of_continuousAt (hf.continuousAt (x := x))

/-- A `K`-smooth function on a finite-dimensional space over a complete field is Fréchet
differentiable at every point. -/
theorem differentiableAt_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : LipschitzSmoothWith 𝕜 K f) (x : E) :
    DifferentiableAt 𝕜 f x :=
  differentiableAt_of_continuous_lineDeriv h x
    (h.lineDerivLinearMap x).continuous_of_finiteDimensional

/-- A `K`-smooth function on a finite-dimensional space over a complete field is Fréchet
differentiable. -/
theorem differentiable_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : LipschitzSmoothWith 𝕜 K f) : Differentiable 𝕜 f :=
  fun x => h.differentiableAt_of_finiteDimensional x

theorem fderiv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E)
    (hf : DifferentiableAt 𝕜 f x) :
    ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_norm_le x y

theorem fderiv_apply_sub_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E)
    (hfx : DifferentiableAt 𝕜 f x) (hfy : DifferentiableAt 𝕜 f y) :
    ‖fderiv 𝕜 f y (y - x) - fderiv 𝕜 f x (y - x)‖ ≤ K * (dist x y) ^ 2 := by
  rw [← hfy.lineDeriv_eq_fderiv, ← hfx.lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_norm_le x y

end NormedField

/-! ### Real-valued functions -/

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K : NNReal} {f : E → ℝ}

theorem fderiv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : E)
    (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + fderiv ℝ f x (y - x) + K / 2 * (dist x y) ^ 2 := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_descent_le x y

theorem fderiv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : E)
    (hf : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) - K / 2 * (dist x y) ^ 2 ≤ f y := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_descent_ge x y

theorem fderiv_apply_sub_le (h : LipschitzSmoothWith ℝ K f) (x y : E)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ K * (dist x y) ^ 2 := by
  rw [← hfy.lineDeriv_eq_fderiv, ← hfx.lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_le x y

theorem fderiv_sub_apply_le (h : LipschitzSmoothWith ℝ K f) (x y : E)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ K * (dist x y) ^ 2 := by
  rw [sub_apply]
  exact h.fderiv_apply_sub_le x y hfx hfy

end Real

end LipschitzSmoothWith
