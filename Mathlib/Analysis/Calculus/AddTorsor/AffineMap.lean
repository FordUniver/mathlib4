/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main definitions:

* `ContinuousAffineMap.contDiff`: a continuous affine map is smooth

-/

public section
namespace ContinuousAffineMap

variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
theorem contDiff {n : WithTop ℕ∞} (f : V →ᴬ[𝕜] W) : ContDiff 𝕜 n f := by
  rw [f.decomp]
  apply f.contLinear.contDiff.add
  exact contDiff_const

end ContinuousAffineMap

namespace AffineMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- `AffineMap.lineMap` is smooth as a function `𝕜 → V`. -/
theorem lineMap_contDiff (p₀ p₁ : V) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (AffineMap.lineMap p₀ p₁ : 𝕜 → V) := by
  have : (AffineMap.lineMap p₀ p₁ : 𝕜 → V) = fun c => c • (p₁ - p₀) + p₀ :=
    funext fun c => AffineMap.lineMap_apply_module' p₀ p₁ c
  rw [this]
  fun_prop

end AffineMap
