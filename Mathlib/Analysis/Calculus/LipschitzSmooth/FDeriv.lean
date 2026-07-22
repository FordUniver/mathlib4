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
in `fderiv` form. Neighborhood-wise `K`-smoothness at a point makes continuity there
equivalent to Fréchet differentiability. In finite-dimensional spaces over a complete
field, the algebraic line-derivative map is automatically continuous, so no continuity
hypothesis is needed. The one-sided descent bounds require an order on the codomain and
are stated for real-valued `f` in a dedicated section.
-/

public section

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

namespace LipschitzSmoothWithAt

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F} {x : E}

/-- If the linear line-derivative map is continuous, then it is the Fréchet derivative. -/
theorem hasFDerivAt (h : LipschitzSmoothWithAt 𝕜 K f x)
    (hcont : Continuous h.lineDerivLinearMap) :
    HasFDerivAt f ⟨h.lineDerivLinearMap, hcont⟩ x :=
  h.hasQuadraticLineRemainderWithAt.hasFDerivAt hcont

/-- Under neighborhood-wise `K`-smoothness, Fréchet differentiability at `x` is equivalent to
continuity at `x`. -/
theorem differentiableAt_iff_continuousAt (h : LipschitzSmoothWithAt 𝕜 K f x) :
    DifferentiableAt 𝕜 f x ↔ ContinuousAt f x :=
  h.hasQuadraticLineRemainderWithAt.differentiableAt_iff_continuousAt

/-- A function that is `K`-smooth at `x` on a finite-dimensional space over a complete field is
Fréchet differentiable at `x`. -/
theorem differentiableAt_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : LipschitzSmoothWithAt 𝕜 K f x) :
    DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt h.lineDerivLinearMap.continuous_of_finiteDimensional).differentiableAt

end NormedField

end LipschitzSmoothWithAt

namespace LipschitzSmoothWith

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F}

/-- For a globally `K`-smooth function, Fréchet differentiability is equivalent to continuity. -/
theorem differentiable_iff_continuous (h : LipschitzSmoothWith 𝕜 K f) :
    Differentiable 𝕜 f ↔ Continuous f := by
  refine ⟨Differentiable.continuous, fun hf x ↦ ?_⟩
  exact (h.lipschitzSmoothWithAt x).differentiableAt_iff_continuousAt.mpr hf.continuousAt

/-- A `K`-smooth function on a finite-dimensional space over a complete field is Fréchet
differentiable. -/
theorem differentiable_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : LipschitzSmoothWith 𝕜 K f) : Differentiable 𝕜 f :=
  fun x => (h.lipschitzSmoothWithAt x).differentiableAt_of_finiteDimensional

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
