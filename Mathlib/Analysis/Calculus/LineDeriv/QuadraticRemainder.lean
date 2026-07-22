/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Quadratic remainders from line derivatives

This file studies functions whose first-order remainder from `lineDeriv` is bounded quadratically.
The predicates make no continuity or Fréchet-differentiability assumption. Nevertheless, a local
bound ensures that the line derivative is algebraically linear in its direction. If the function
is continuous, this linear map is continuous and is the Fréchet derivative.

## Main definitions

* `HasQuadraticLineRemainderOnWith`: the remainder is quadratically bounded on a set.
* `HasQuadraticLineRemainderWith`: the corresponding global predicate.
* `HasQuadraticLineRemainderWithAt`: the corresponding predicate near a point.
-/

public section

noncomputable section

open scoped NNReal Topology

open AffineMap Asymptotics Filter

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {C : NNReal} {f : E → F} {x : E}

variable (𝕜)

/-- `HasQuadraticLineRemainderOnWith 𝕜 C f s` means that the first-order remainder from
`lineDeriv` is bounded by `C * dist x y ^ 2` for all `x`, `y` in `s`. -/
abbrev HasQuadraticLineRemainderOnWith (C : NNReal) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s,
    ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2

/-- `HasQuadraticLineRemainderWith 𝕜 C f` means that the first-order remainder from `lineDeriv`
is bounded by `C * dist x y ^ 2`, uniformly in `x` and `y`. -/
abbrev HasQuadraticLineRemainderWith (C : NNReal) (f : E → F) : Prop :=
  ∀ x y, ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2

/-- `HasQuadraticLineRemainderWithAt 𝕜 C f x` means that the first-order remainder from
`lineDeriv` is bounded by `C * dist y z ^ 2` for all `y`, `z` in some neighborhood of `x`. -/
abbrev HasQuadraticLineRemainderWithAt (C : NNReal) (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, HasQuadraticLineRemainderOnWith 𝕜 C f s

variable {𝕜}

namespace HasQuadraticLineRemainderOnWith

/-- Restricting a quadratic line-remainder bound to a smaller set. -/
theorem mono {s t : Set E} (h : HasQuadraticLineRemainderOnWith 𝕜 C f s) (hst : t ⊆ s) :
    HasQuadraticLineRemainderOnWith 𝕜 C f t :=
  fun x hx y hy ↦ h x (hst hx) y (hst hy)

/-- A quadratic line-remainder bound controls the failure of `f` to commute with affine
interpolation between points of the set. -/
theorem norm_image_lineMap_sub_lineMap_le {s : Set E}
    (h : HasQuadraticLineRemainderOnWith 𝕜 C f s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) (c : 𝕜) (hz : lineMap x y c ∈ s) :
    ‖f (lineMap x y c) - lineMap (f x) (f y) c‖ ≤
      C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by
  let z := lineMap x y c
  calc
    ‖f z - lineMap (f x) (f y) c‖ =
        ‖(f z - f x - lineDeriv 𝕜 f x (z - x)) -
          c • (f y - f x - lineDeriv 𝕜 f x (y - x))‖ := by
      congr 1
      rw [lineMap_apply_module]
      simp only [z, lineMap_apply_module', add_sub_cancel_right, lineDeriv_smul]
      module
    _ ≤ ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ +
        ‖c‖ * ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ := by
      rw [← norm_smul]; exact norm_sub_le _ _
    _ ≤ C * dist x z ^ 2 + ‖c‖ * (C * dist x y ^ 2) :=
      add_le_add (h x hx z hz)
        (mul_le_mul_of_nonneg_left (h x hx y hy) (norm_nonneg c))
    _ = C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by
      simp [z, lineMap_apply_module', dist_eq_norm, norm_smul, norm_sub_rev]
      ring

end HasQuadraticLineRemainderOnWith

namespace HasQuadraticLineRemainderWith

/-- A global quadratic line-remainder bound restricts to every set. -/
theorem hasQuadraticLineRemainderOnWith
    (h : HasQuadraticLineRemainderWith 𝕜 C f) (s : Set E) :
    HasQuadraticLineRemainderOnWith 𝕜 C f s :=
  fun x _ y _ ↦ h x y

/-- A global quadratic line-remainder bound holds in a neighborhood of every point. -/
theorem hasQuadraticLineRemainderWithAt
    (h : HasQuadraticLineRemainderWith 𝕜 C f) (x : E) :
    HasQuadraticLineRemainderWithAt 𝕜 C f x :=
  ⟨Set.univ, univ_mem, fun y _ z _ ↦ h y z⟩

end HasQuadraticLineRemainderWith


private theorem eventually_add_smul_mem {s : Set E} (hs : s ∈ 𝓝 x) (v : E) :
    ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v ∈ s := by
  have htendsto : Tendsto (fun t : 𝕜 ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using (show ContinuousAt (fun t : 𝕜 ↦ x + t • v) 0 by fun_prop).tendsto
  exact htendsto hs

namespace HasQuadraticLineRemainderWithAt

/-- A quadratic line remainder bound near a point ensures that `lineDeriv` is the actual line
derivative at that point. -/
theorem hasLineDerivAt (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v := by
  obtain ⟨s, hs, hbound⟩ := h
  have hx := mem_of_mem_nhds hs
  change HasDerivAt (fun t : 𝕜 ↦ f (x + t • v)) (lineDeriv 𝕜 f x v) 0
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (IsBigO.of_bound (C * ‖v‖ ^ 2) ?_).trans_isLittleO
    (isLittleO_pow_id one_lt_two)
  filter_upwards [eventually_add_smul_mem hs v] with t ht
  have ht_bound := hbound x hx (x + t • v) ht
  rw [show (x + t • v) - x = t • v by abel, lineDeriv_smul,
    dist_self_add_right, norm_smul, mul_pow] at ht_bound
  simpa only [zero_add, zero_smul, add_zero, norm_pow, mul_assoc, mul_left_comm, mul_comm]
    using ht_bound

private theorem image_lineMap_sub_lineMap_isBigO
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (u v : E) (c : 𝕜) :
    (fun t : 𝕜 ↦ f (lineMap (x + t • u) (x + t • v) c) -
      lineMap (f (x + t • u)) (f (x + t • v)) c) =O[𝓝 0] fun t : 𝕜 ↦ t ^ 2 := by
  obtain ⟨s, hs, hbound⟩ := h
  refine IsBigO.of_bound (C * (‖c‖ ^ 2 + ‖c‖) * ‖v - u‖ ^ 2) ?_
  filter_upwards [eventually_add_smul_mem (𝕜 := 𝕜) hs u,
    eventually_add_smul_mem (𝕜 := 𝕜) hs v,
    eventually_add_smul_mem (𝕜 := 𝕜) hs ((1 - c) • u + c • v)]
    with t hut hvt hlinet
  have hline_eq : lineMap (x + t • u) (x + t • v) c =
      x + t • ((1 - c) • u + c • v) := by
    simp only [lineMap_apply_module]
    module
  refine (hbound.norm_image_lineMap_sub_lineMap_le hut hvt c ?_).trans_eq ?_
  · rwa [hline_eq]
  · rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, mul_pow, norm_pow,
      norm_sub_rev u v]
    ring

/-- The line derivative at `x` preserves affine combinations of directions. -/
theorem lineDeriv_affineCombination (h : HasQuadraticLineRemainderWithAt 𝕜 C f x)
    (u v : E) (c : 𝕜) :
    lineDeriv 𝕜 f x ((1 - c) • u + c • v) =
      (1 - c) • lineDeriv 𝕜 f x u + c • lineDeriv 𝕜 f x v := by
  let q := (1 - c) • u + c • v
  let g := fun t : 𝕜 ↦
    f (x + t • q) - ((1 - c) • f (x + t • u) + c • f (x + t • v))
  have hg : HasDerivAt g
      (lineDeriv 𝕜 f x q -
        ((1 - c) • lineDeriv 𝕜 f x u + c • lineDeriv 𝕜 f x v)) 0 :=
    (h.hasLineDerivAt q).sub
      (((h.hasLineDerivAt u).const_smul (1 - c)).add
        ((h.hasLineDerivAt v).const_smul c))
  have hlineMap (t : 𝕜) : lineMap (x + t • u) (x + t • v) c = x + t • q := by
    simp only [q, lineMap_apply_module]
    module
  have hg_bigO : g =O[𝓝 0] fun t : 𝕜 ↦ t ^ 2 := by
    rw [show g = fun t : 𝕜 ↦ f (lineMap (x + t • u) (x + t • v) c) -
        lineMap (f (x + t • u)) (f (x + t • v)) c by
      funext t
      rw [hlineMap, lineMap_apply_module]]
    exact h.image_lineMap_sub_lineMap_isBigO u v c
  have hg_zero : HasDerivAt g 0 0 := by
    have : g =O[𝓝 0] fun t ↦ ‖t - 0‖ ^ 2 := by
      simpa only [sub_zero, norm_pow] using hg_bigO.norm_right
    exact this.hasDerivAt one_lt_two
  exact sub_eq_zero.mp (hg.unique hg_zero)

/-- If the remainder from `lineDeriv` is quadratically bounded near `x`, then the line derivative
at `x` is linear in its direction. -/
theorem isLinearMap_lineDeriv (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    IsLinearMap 𝕜 (lineDeriv 𝕜 f x) := by
  refine IsLinearMap.mk ?_ fun _ _ ↦ lineDeriv_smul
  obtain ⟨c : 𝕜, hc_pos, hc_lt⟩ := NormedField.exists_norm_lt_one 𝕜
  have hc : c ≠ 0 := norm_ne_zero_iff.mp hc_pos.ne'
  have h₁c : 1 - c ≠ 0 := by
    intro h
    have : c = 1 := (sub_eq_zero.mp h).symm
    simp [this] at hc_lt
  exact (AddMonoidHom.ofMapLineMap (lineDeriv 𝕜 f x) lineDeriv_zero c hc.isUnit h₁c.isUnit
    fun u v ↦ by
      simpa only [lineMap_apply_module] using h.lineDeriv_affineCombination u v c).map_add

/-- The line derivative at `x`, bundled as a linear map in its direction. -/
noncomputable def lineDerivLinearMap (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.isLinearMap_lineDeriv

@[simp]
theorem lineDerivLinearMap_apply (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (v : E) :
    h.lineDerivLinearMap v = lineDeriv 𝕜 f x v := by
    change IsLinearMap.mk' (lineDeriv 𝕜 f x) h.isLinearMap_lineDeriv v =
      lineDeriv 𝕜 f x v
    rfl

/-- The remainder from the linear line derivative is quadratically bounded near `x`. -/
theorem isBigO_sub_lineDerivLinearMap (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    (fun y ↦ f y - f x - h.lineDerivLinearMap (y - x)) =O[𝓝 x]
      fun y ↦ ‖y - x‖ ^ 2 := by
  obtain ⟨s, hs, hbound⟩ := h
  have hx := mem_of_mem_nhds hs
  refine IsBigO.of_bound C ?_
  filter_upwards [hs] with y hy
  simpa [dist_eq_norm, norm_sub_rev] using hbound x hx y hy

/-- A continuous linear line-derivative map is the Fréchet derivative. -/
theorem hasFDerivAt (h : HasQuadraticLineRemainderWithAt 𝕜 C f x)
    (hcont : Continuous h.lineDerivLinearMap) :
    HasFDerivAt f ⟨h.lineDerivLinearMap, hcont⟩ x :=
  HasFDerivAt.of_isLittleO <|
    h.isBigO_sub_lineDerivLinearMap.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

/-- If `f` is continuous at `x`, then its algebraically linear line derivative at `x` is
continuous. -/
theorem continuous_lineDerivLinearMap
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (hf : ContinuousAt f x) :
    Continuous h.lineDerivLinearMap :=
  h.lineDerivLinearMap.continuous_of_isLittleO_sub hf <|
    h.isBigO_sub_lineDerivLinearMap.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

/-- Under a quadratic line-remainder bound near `x`, Fréchet differentiability at `x` is
equivalent to continuity at `x`. -/
theorem differentiableAt_iff_continuousAt
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    DifferentiableAt 𝕜 f x ↔ ContinuousAt f x :=
  ⟨DifferentiableAt.continuousAt, fun hf ↦
    h.lineDerivLinearMap.differentiableAt_of_isLittleO_sub hf <|
      h.isBigO_sub_lineDerivLinearMap.trans_isLittleO
        (isLittleO_pow_sub_sub x one_lt_two)⟩

/-- A local quadratic line-remainder bound on a finite-dimensional space over a complete field
implies Fréchet differentiability at its center. -/
theorem differentiableAt_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt h.lineDerivLinearMap.continuous_of_finiteDimensional).differentiableAt

end HasQuadraticLineRemainderWithAt


namespace HasQuadraticLineRemainderWith

/-- A uniform quadratic remainder bound ensures that `lineDeriv` is the actual line derivative. -/
theorem hasLineDerivAt (h : HasQuadraticLineRemainderWith 𝕜 C f) (x v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  (h.hasQuadraticLineRemainderWithAt x).hasLineDerivAt v

/-- A quadratic line-remainder bound controls the failure of `f` to commute with affine
interpolation. -/
theorem norm_image_lineMap_sub_lineMap_le (h : HasQuadraticLineRemainderWith 𝕜 C f)
    (x y : E) (c : 𝕜) :
    ‖f (lineMap x y c) - lineMap (f x) (f y) c‖ ≤
      C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 :=
  (h.hasQuadraticLineRemainderOnWith Set.univ).norm_image_lineMap_sub_lineMap_le
    (Set.mem_univ x) (Set.mem_univ y) c (Set.mem_univ _)

/-- Under a global quadratic remainder bound, lineDeriv is linear in its direction. -/
theorem isLinearMap_lineDeriv (h : HasQuadraticLineRemainderWith 𝕜 C f) (x : E) :
    IsLinearMap 𝕜 (lineDeriv 𝕜 f x) :=
  (h.hasQuadraticLineRemainderWithAt x).isLinearMap_lineDeriv

/-- Under a global quadratic line-remainder bound, Fréchet differentiability is equivalent to
continuity. -/
theorem differentiable_iff_continuous (h : HasQuadraticLineRemainderWith 𝕜 C f) :
    Differentiable 𝕜 f ↔ Continuous f :=
  ⟨Differentiable.continuous, fun hf x ↦
    (h.hasQuadraticLineRemainderWithAt x).differentiableAt_iff_continuousAt.mpr
      hf.continuousAt⟩

/-- A global quadratic line-remainder bound on a finite-dimensional space over a complete field
implies Fréchet differentiability. -/
theorem differentiable_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : HasQuadraticLineRemainderWith 𝕜 C f) :
    Differentiable 𝕜 f :=
  fun x ↦ (h.hasQuadraticLineRemainderWithAt x).differentiableAt_of_finiteDimensional

end HasQuadraticLineRemainderWith
