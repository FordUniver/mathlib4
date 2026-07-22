/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.QuadraticRemainder
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

/-!
# Line-derivative characterisations of Lipschitz smoothness

This file connects the textbook, Fréchet-derivative-based `LipschitzSmoothWith` and
`LipschitzSmoothWithAt` predicates to the technical quadratic line-remainder predicates. Once
Fréchet differentiability is available, `lineDeriv` agrees with `fderiv` and the two forms of the
quadratic remainder bound coincide.
-/

public section

open scoped NNReal Topology

open Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : E → F} {x : E}

/-- Global Lipschitz smoothness is global Fréchet differentiability together with the
corresponding quadratic line-remainder bound. -/
theorem lipschitzSmoothWith_iff_hasQuadraticLineRemainderWith :
    LipschitzSmoothWith 𝕜 K f ↔
      Differentiable 𝕜 f ∧ HasQuadraticLineRemainderWith 𝕜 (K / 2) f := by
  constructor
  · intro h
    refine ⟨h.differentiable, ?_⟩
    rw [hasQuadraticLineRemainderWith_iff]
    intro x y
    rw [(h.differentiable x).lineDeriv_eq_fderiv]
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using h.fderiv_norm_le x y
  · rintro ⟨hf, h⟩
    rw [lipschitzSmoothWith_iff_fderiv]
    intro x y
    rw [← (hf x).lineDeriv_eq_fderiv]
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using h.norm_le x y

/-- Neighborhood-wise Lipschitz smoothness is eventual Fréchet differentiability together with
the corresponding local quadratic line-remainder bound. -/
theorem lipschitzSmoothWithAt_iff_hasQuadraticLineRemainderWithAt :
    LipschitzSmoothWithAt 𝕜 K f x ↔
      (∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y) ∧
        HasQuadraticLineRemainderWithAt 𝕜 (K / 2) f x := by
  constructor
  · intro h
    refine ⟨h.eventually_differentiableAt, ?_⟩
    obtain ⟨s, hs, hbound⟩ := h.exists_fderiv_norm_le
    obtain ⟨t, ht, hf⟩ := eventually_iff_exists_mem.mp h.eventually_differentiableAt
    apply (hasQuadraticLineRemainderWithAt_iff 𝕜).mpr
    refine ⟨s ∩ t, inter_mem hs ht, fun y hy z hz ↦ ?_⟩
    rw [(hf y hy.2).lineDeriv_eq_fderiv]
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hbound y hy.1 z hz.1
  · rintro ⟨hfd, h⟩
    obtain ⟨t, ht, hf⟩ := eventually_iff_exists_mem.mp hfd
    obtain ⟨s, hs, hbound⟩ := h.exists_norm_le
    apply (lipschitzSmoothWithAt_iff_fderiv 𝕜).mpr
    refine ⟨s ∩ t, inter_mem hs ht, fun y hy z hz ↦ ?_⟩
    rw [← (hf y hy.2).lineDeriv_eq_fderiv]
    simpa only [NNReal.coe_div, NNReal.coe_ofNat] using hbound y hy.1 z hz.1

namespace LipschitzSmoothWith

/-- The quadratic line-remainder condition underlying global Lipschitz smoothness. -/
theorem hasQuadraticLineRemainderWith (h : LipschitzSmoothWith 𝕜 K f) :
    HasQuadraticLineRemainderWith 𝕜 (K / 2) f :=
  (lipschitzSmoothWith_iff_hasQuadraticLineRemainderWith.mp h).2

/-- A Lipschitz-smooth function has the expected line derivative in every direction. -/
theorem hasLineDerivAt (h : LipschitzSmoothWith 𝕜 K f) (x v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  (h.differentiable x).lineDifferentiableAt.hasLineDerivAt

/-- The line derivative of a Lipschitz-smooth function is additive in its direction. -/
theorem lineDeriv_add (h : LipschitzSmoothWith 𝕜 K f) (x u v : E) :
    lineDeriv 𝕜 f x (u + v) = lineDeriv 𝕜 f x u + lineDeriv 𝕜 f x v := by
  simpa only [(h.differentiable x).lineDeriv_eq_fderiv] using map_add (fderiv 𝕜 f x) u v

end LipschitzSmoothWith

namespace LipschitzSmoothWithAt

/-- The local quadratic line-remainder condition underlying neighborhood-wise Lipschitz
smoothness. -/
theorem hasQuadraticLineRemainderWithAt (h : LipschitzSmoothWithAt 𝕜 K f x) :
    HasQuadraticLineRemainderWithAt 𝕜 (K / 2) f x :=
  (lipschitzSmoothWithAt_iff_hasQuadraticLineRemainderWithAt.mp h).2

/-- A function Lipschitz smooth near `x` has the expected line derivative at `x` in every
direction. -/
theorem hasLineDerivAt (h : LipschitzSmoothWithAt 𝕜 K f x) (v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  h.differentiableAt.lineDifferentiableAt.hasLineDerivAt

/-- The line derivative of a function Lipschitz smooth near `x` is additive in its direction. -/
theorem lineDeriv_add (h : LipschitzSmoothWithAt 𝕜 K f x) (u v : E) :
    lineDeriv 𝕜 f x (u + v) = lineDeriv 𝕜 f x u + lineDeriv 𝕜 f x v := by
  simpa only [h.differentiableAt.lineDeriv_eq_fderiv] using map_add (fderiv 𝕜 f x) u v

end LipschitzSmoothWithAt
