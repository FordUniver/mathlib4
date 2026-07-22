/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Lipschitz smoothness

A function `f : E → F` between normed vector spaces over a nontrivially normed field `𝕜` is
**`K`-smooth** if its first-order Taylor remainder is bounded quadratically:

`‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ (K / 2) * dist x y ^ 2`.

We define global and neighborhood-wise versions. Both imply the corresponding Fréchet
differentiability property. A setwise version is deliberately deferred: on a non-open set one
must first choose between ambient derivatives, within-set derivatives, and an extension property.
-/

public section

open scoped Topology

open Asymptotics Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜)

/-- `LipschitzSmoothWith 𝕜 K f` means that the first-order Taylor remainder from `fderiv` is
bounded by `K / 2 * dist x y ^ 2` for all `x` and `y`. -/
def LipschitzSmoothWith (K : NNReal) (f : E → F) : Prop :=
  ∀ x y, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2

/-- `LipschitzSmoothWithAt 𝕜 K f x` means that the first-order Taylor remainder from `fderiv`
is bounded by `K / 2 * dist y z ^ 2` for all `y` and `z` in some neighborhood of `x`. -/
def LipschitzSmoothWithAt (K : NNReal) (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, ∀ y ∈ s, ∀ z ∈ s,
    ‖f z - f y - fderiv 𝕜 f y (z - y)‖ ≤ K / 2 * dist y z ^ 2

theorem lipschitzSmoothWith_iff_fderiv {K : NNReal} {f : E → F} :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y, ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  Iff.rfl

theorem lipschitzSmoothWithAt_iff_fderiv {K : NNReal} {f : E → F} {x : E} :
    LipschitzSmoothWithAt 𝕜 K f x ↔
      ∃ s ∈ 𝓝 x, ∀ y ∈ s, ∀ z ∈ s,
        ‖f z - f y - fderiv 𝕜 f y (z - y)‖ ≤ K / 2 * dist y z ^ 2 :=
  Iff.rfl

variable {𝕜}

private theorem hasFDerivAt_of_eventually_fderiv_norm_le {K : NNReal} {f : E → F} {x : E}
    (h : ∀ᶠ y in 𝓝 x,
      ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2) :
    HasFDerivAt f (fderiv 𝕜 f x) x := by
  apply HasFDerivAt.of_isLittleO
  refine (IsBigO.of_bound (K / 2) ?_).trans_isLittleO
    (isLittleO_pow_sub_sub x one_lt_two)
  filter_upwards [h] with y hy
  simpa [dist_eq_norm, norm_sub_rev] using hy

namespace LipschitzSmoothWithAt

variable {K : NNReal} {f : E → F} {x : E}

/-- Extract a neighborhood carrying the defining quadratic bound. -/
theorem exists_fderiv_norm_le (h : LipschitzSmoothWithAt 𝕜 K f x) :
    ∃ s ∈ 𝓝 x, ∀ y ∈ s, ∀ z ∈ s,
      ‖f z - f y - fderiv 𝕜 f y (z - y)‖ ≤ K / 2 * dist y z ^ 2 :=
  h

/-- A function Lipschitz smooth near `x` is Fréchet differentiable throughout a possibly smaller
neighborhood of `x`. -/
theorem eventually_differentiableAt (h : LipschitzSmoothWithAt 𝕜 K f x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y := by
  obtain ⟨s, hs, hbound⟩ := h.exists_fderiv_norm_le
  obtain ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  filter_upwards [hu.mem_nhds hxu] with y hy
  apply (hasFDerivAt_of_eventually_fderiv_norm_le (K := K) ?_).differentiableAt
  filter_upwards [hu.mem_nhds hy] with z hz
  exact hbound y (hus hy) z (hus hz)

/-- A function Lipschitz smooth near `x` is Fréchet differentiable at `x`. -/
theorem differentiableAt (h : LipschitzSmoothWithAt 𝕜 K f x) :
    DifferentiableAt 𝕜 f x :=
  h.eventually_differentiableAt.self_of_nhds

end LipschitzSmoothWithAt

namespace LipschitzSmoothWith

variable {K : NNReal} {f : E → F}

/-- The defining quadratic bound on the first-order Taylor remainder. -/
theorem fderiv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : E) :
    ‖f y - f x - fderiv 𝕜 f x (y - x)‖ ≤ K / 2 * dist x y ^ 2 :=
  h x y

/-- A globally Lipschitz-smooth function is Lipschitz smooth near every point. -/
theorem lipschitzSmoothWithAt (h : LipschitzSmoothWith 𝕜 K f) (x : E) :
    LipschitzSmoothWithAt 𝕜 K f x :=
  ⟨Set.univ, univ_mem, fun y _ z _ ↦ h.fderiv_norm_le y z⟩

/-- A globally Lipschitz-smooth function is Fréchet differentiable. -/
theorem differentiable (h : LipschitzSmoothWith 𝕜 K f) :
    Differentiable 𝕜 f :=
  fun x ↦ (hasFDerivAt_of_eventually_fderiv_norm_le <|
    Eventually.of_forall fun y ↦ h.fderiv_norm_le x y).differentiableAt

end LipschitzSmoothWith
