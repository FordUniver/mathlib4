/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Lipschitz smoothness via line derivatives

We first study the technical predicates asserting that the first-order remainder from `lineDeriv`
is bounded quadratically. These predicates do not assume continuity or Fréchet differentiability,
but they ensure that the line derivative exists and is linear in its direction.

We then connect them to the textbook, Fréchet-derivative-based `LipschitzSmoothOnWith`,
`LipschitzSmoothWith`, and `LipschitzSmoothWithAt` predicates. Once the relevant Fréchet
differentiability hypotheses are supplied, `lineDeriv` agrees with `fderiv`, and the two forms of
the quadratic remainder bound coincide.

## Main definitions

* `HasQuadraticLineRemainderOnWith`: the first-order remainder from `lineDeriv` is uniformly
  bounded by a quadratic function on a set.
* `HasQuadraticLineRemainderWith`: the corresponding global predicate.
* `HasQuadraticLineRemainderWithAt`: the corresponding predicate in a neighborhood of a point.

## Main results

* `HasQuadraticLineRemainderWithAt.hasLineDerivAt`: the line derivative actually exists.
* `HasQuadraticLineRemainderWithAt.lineDerivLinearMap`: the line derivative bundled as a linear
  map in its direction.
* `HasQuadraticLineRemainderWithAt.differentiableAt_iff_continuousAt`: under a local quadratic
  remainder bound, Fréchet differentiability is equivalent to continuity.
* `lipschitzSmoothWith_iff_hasQuadraticLineRemainderWith`: the global line-derivative
  characterisation of Lipschitz smoothness.
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

/-- `HasQuadraticLineRemainderOnWith 𝕜 C f s` means that the first-order Taylor remainder from
`lineDeriv` is bounded by `C * dist x y ^ 2` for all `x`, `y` in `s`. -/
def HasQuadraticLineRemainderOnWith (C : NNReal) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s,
    ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2

/-- `HasQuadraticLineRemainderWith 𝕜 C f` means that the first-order Taylor remainder from
`lineDeriv` is bounded by `C * dist x y ^ 2`, uniformly in `x` and `y`. -/
def HasQuadraticLineRemainderWith (C : NNReal) (f : E → F) : Prop :=
  HasQuadraticLineRemainderOnWith 𝕜 C f Set.univ

/-- `HasQuadraticLineRemainderWithAt 𝕜 C f x` means that the first-order Taylor remainder from
`lineDeriv` is bounded by `C * dist y z ^ 2` for all pairs `y`, `z` in some neighborhood of `x`.
-/
def HasQuadraticLineRemainderWithAt (C : NNReal) (f : E → F) (x : E) : Prop :=
  ∃ s ∈ 𝓝 x, HasQuadraticLineRemainderOnWith 𝕜 C f s

theorem hasQuadraticLineRemainderOnWith_iff {s : Set E} :
    HasQuadraticLineRemainderOnWith 𝕜 C f s ↔
      ∀ x ∈ s, ∀ y ∈ s,
        ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2 :=
  Iff.rfl

theorem hasQuadraticLineRemainderWith_iff :
    HasQuadraticLineRemainderWith 𝕜 C f ↔
      ∀ x y, ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ ≤ C * dist x y ^ 2 := by
  simp [HasQuadraticLineRemainderWith, hasQuadraticLineRemainderOnWith_iff]

theorem hasQuadraticLineRemainderWithAt_iff :
    HasQuadraticLineRemainderWithAt 𝕜 C f x ↔
      ∃ s ∈ 𝓝 x, ∀ y ∈ s, ∀ z ∈ s,
        ‖f z - f y - lineDeriv 𝕜 f y (z - y)‖ ≤ C * dist y z ^ 2 :=
  Iff.rfl

variable {𝕜}

namespace HasQuadraticLineRemainderOnWith

/-- A quadratic line-remainder bound controls the failure of `f` to commute with affine
interpolation between points of the set. -/
theorem norm_image_lineMap_sub_lineMap_le {s : Set E}
    (h : HasQuadraticLineRemainderOnWith 𝕜 C f s)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) (c : 𝕜) (hz : lineMap x y c ∈ s) :
    ‖f (lineMap x y c) - lineMap (f x) (f y) c‖ ≤
      C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by
  let z := lineMap x y c
  have hzx : z - x = c • (y - x) := by simp [z, lineMap_apply_module']
  have hdist : dist x z = ‖c‖ * dist x y := by
    rw [dist_eq_norm, show x - z = c • (x - y) by
      simp [z, lineMap_apply_module]; module, norm_smul, dist_eq_norm]
  have hbound : ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ ≤
      C * (‖c‖ ^ 2 * dist x y ^ 2) := by
    calc
      _ ≤ C * dist x z ^ 2 := h x hx z hz
      _ = _ := by rw [hdist, mul_pow]
  calc
    ‖f z - lineMap (f x) (f y) c‖ =
        ‖(f z - f x - lineDeriv 𝕜 f x (z - x)) -
          c • (f y - f x - lineDeriv 𝕜 f x (y - x))‖ := by
      congr 1
      rw [lineMap_apply_module, hzx, lineDeriv_smul]
      module
    _ ≤ ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ +
        ‖c • (f y - f x - lineDeriv 𝕜 f x (y - x))‖ := norm_sub_le _ _
    _ = ‖f z - f x - lineDeriv 𝕜 f x (z - x)‖ +
        ‖c‖ * ‖f y - f x - lineDeriv 𝕜 f x (y - x)‖ := by rw [norm_smul]
    _ ≤ C * (‖c‖ ^ 2 * dist x y ^ 2) + ‖c‖ * (C * dist x y ^ 2) :=
      add_le_add hbound (mul_le_mul_of_nonneg_left (h x hx y hy) (norm_nonneg c))
    _ = C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 := by ring

/-- Restricting a quadratic line-remainder bound to a smaller set. -/
theorem mono {s t : Set E} (h : HasQuadraticLineRemainderOnWith 𝕜 C f s) (hst : t ⊆ s) :
    HasQuadraticLineRemainderOnWith 𝕜 C f t :=
  fun x hx y hy ↦ h x (hst hx) y (hst hy)

end HasQuadraticLineRemainderOnWith

private theorem eventually_add_smul_mem {s : Set E} (hs : s ∈ 𝓝 x) (v : E) :
    ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v ∈ s := by
  have htendsto : Tendsto (fun t : 𝕜 ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    have : ContinuousAt (fun t : 𝕜 ↦ x + t • v) 0 := by fun_prop
    simpa using this.tendsto
  exact htendsto hs

namespace HasQuadraticLineRemainderWithAt

/-- A quadratic line remainder bound in a neighborhood ensures that `lineDeriv` is the actual
line derivative at the center of the neighborhood. -/
theorem hasLineDerivAt (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v := by
  obtain ⟨s, hs, h⟩ := h
  have hx : x ∈ s := mem_of_mem_nhds hs
  have hmem : ∀ᶠ t : 𝕜 in 𝓝 0, x + t • v ∈ s := eventually_add_smul_mem hs v
  change HasDerivAt (fun t : 𝕜 ↦ f (x + t • v)) (lineDeriv 𝕜 f x v) 0
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  refine (IsBigO.of_bound (C * ‖v‖ ^ 2) ?_).trans_isLittleO
    (isLittleO_pow_id one_lt_two)
  filter_upwards [hmem] with t ht
  have ht_bound := h x hx (x + t • v) ht
  rw [show (x + t • v) - x = t • v by abel, lineDeriv_smul,
    dist_self_add_right, norm_smul, mul_pow] at ht_bound
  simpa only [zero_add, zero_smul, add_zero, norm_pow, mul_assoc, mul_left_comm, mul_comm]
    using ht_bound

private theorem image_lineMap_sub_lineMap_isBigO
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (u v : E) (c : 𝕜) :
    (fun t : 𝕜 ↦ f (lineMap (x + t • u) (x + t • v) c) -
      lineMap (f (x + t • u)) (f (x + t • v)) c) =O[𝓝 0] fun t : 𝕜 ↦ t ^ 2 := by
  obtain ⟨s, hs, hbound⟩ := h
  have hu := eventually_add_smul_mem (𝕜 := 𝕜) hs u
  have hv := eventually_add_smul_mem (𝕜 := 𝕜) hs v
  have hline := eventually_add_smul_mem (𝕜 := 𝕜) hs ((1 - c) • u + c • v)
  refine IsBigO.of_bound (C * (‖c‖ ^ 2 + ‖c‖) * ‖v - u‖ ^ 2) ?_
  filter_upwards [hu, hv, hline] with t hut hvt hlinet
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
  have hg_zero : g 0 = 0 := by
    simp only [g, zero_smul, add_zero]
    module
  have hg_zero' : HasDerivAt g 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    simpa [hg_zero] using hg_bigO.trans_isLittleO (isLittleO_pow_id one_lt_two)
  exact sub_eq_zero.mp (hg.unique hg_zero')

/-- If the remainder from `lineDeriv` is uniformly bounded by a quadratic function in a
neighborhood of `x`, then the line derivative at `x` is linear in the direction. -/
theorem isLinearMap_lineDeriv (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    IsLinearMap 𝕜 (lineDeriv 𝕜 f x) := by
  refine IsLinearMap.mk ?_ fun c v ↦ lineDeriv_smul
  intro u v
  obtain ⟨c : 𝕜, hc_pos, hc_lt⟩ := NormedField.exists_norm_lt_one 𝕜
  have hc : c ≠ 0 := norm_ne_zero_iff.mp hc_pos.ne'
  have h_one_sub_c : 1 - c ≠ 0 := by
    intro h
    have : c = 1 := (sub_eq_zero.mp h).symm
    simp [this] at hc_lt
  simpa [h_one_sub_c, hc, lineDeriv_smul] using
    h.lineDeriv_affineCombination ((1 - c)⁻¹ • u) (c⁻¹ • v) c

/-- The line derivative at `x`, bundled as a linear map in its direction. -/
@[expose]
noncomputable def lineDerivLinearMap (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.isLinearMap_lineDeriv

@[simp]
theorem lineDerivLinearMap_apply (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (v : E) :
    h.lineDerivLinearMap v = lineDeriv 𝕜 f x v :=
  rfl

/-- The remainder from the linear line derivative is quadratically bounded near `x`. -/
theorem isBigO_sub_lineDerivLinearMap (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    (fun y ↦ f y - f x - h.lineDerivLinearMap (y - x)) =O[𝓝 x]
      fun y ↦ ‖y - x‖ ^ 2 := by
  obtain ⟨s, hs, hbound⟩ := h
  have hx : x ∈ s := mem_of_mem_nhds hs
  refine IsBigO.of_bound C ?_
  filter_upwards [hs] with y hy
  simpa [dist_eq_norm, norm_sub_rev] using hbound x hx y hy

/-- A continuous linear line-derivative map is the Fréchet derivative. -/
theorem hasFDerivAt (h : HasQuadraticLineRemainderWithAt 𝕜 C f x)
    (hcont : Continuous h.lineDerivLinearMap) :
    HasFDerivAt f ⟨h.lineDerivLinearMap, hcont⟩ x :=
  HasFDerivAt.of_isLittleO <|
    h.isBigO_sub_lineDerivLinearMap.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

private theorem continuous_lineDerivLinearMap
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) (hf : ContinuousAt f x) :
    Continuous h.lineDerivLinearMap := by
  let L := h.lineDerivLinearMap
  have hsq : Tendsto (fun y : E ↦ ‖y - x‖ ^ 2) (𝓝 x) (𝓝 0) := by
    have : ContinuousAt (fun y : E ↦ ‖y - x‖ ^ 2) x := by fun_prop
    simpa using this.tendsto
  have hr : Tendsto (fun y ↦ f y - f x - L (y - x)) (𝓝 x) (𝓝 0) :=
    h.isBigO_sub_lineDerivLinearMap.trans_tendsto hsq
  have hf_inc : Tendsto (fun y ↦ f y - f x) (𝓝 x) (𝓝 0) := by
    simpa using hf.tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : E ↦ f x) (𝓝 x) (𝓝 (f x)))
  have hL : Tendsto (fun y ↦ L (y - x)) (𝓝 x) (𝓝 0) := by
    convert hf_inc.sub hr using 1
    · funext y
      module
    · simp
  apply continuous_of_tendsto_nhds_zero L
  have hadd : Tendsto (fun v : E ↦ x + v) (𝓝 0) (𝓝 x) := by
    have : ContinuousAt (fun v : E ↦ x + v) 0 := by fun_prop
    simpa using this.tendsto
  have hcomp := hL.comp hadd
  have heq : (fun y : E ↦ L (y - x)) ∘ (fun v ↦ x + v) = L := by
    funext v
    simp only [Function.comp_apply, add_sub_cancel_left]
  rw [heq] at hcomp
  exact hcomp

/-- Under a uniform quadratic line remainder bound in a neighborhood of `x`, Fréchet
differentiability at `x` is equivalent to continuity at `x`. -/
theorem differentiableAt_iff_continuousAt
    (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    DifferentiableAt 𝕜 f x ↔ ContinuousAt f x :=
  ⟨DifferentiableAt.continuousAt, fun hf ↦
    (h.hasFDerivAt (continuous_lineDerivLinearMap h hf)).differentiableAt⟩

/-- A local quadratic line-remainder bound on a finite-dimensional space over a complete field
implies Fréchet differentiability at the center. -/
theorem differentiableAt_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : HasQuadraticLineRemainderWithAt 𝕜 C f x) :
    DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt h.lineDerivLinearMap.continuous_of_finiteDimensional).differentiableAt

end HasQuadraticLineRemainderWithAt

namespace HasQuadraticLineRemainderWith

/-- A global quadratic line-remainder bound restricts to every set. -/
theorem hasQuadraticLineRemainderOnWith
    (h : HasQuadraticLineRemainderWith 𝕜 C f) (s : Set E) :
    HasQuadraticLineRemainderOnWith 𝕜 C f s :=
  (show HasQuadraticLineRemainderOnWith 𝕜 C f Set.univ from h).mono (Set.subset_univ s)

/-- A global quadratic line remainder bound holds in a neighborhood of every point. -/
theorem hasQuadraticLineRemainderWithAt
    (h : HasQuadraticLineRemainderWith 𝕜 C f) (x : E) :
    HasQuadraticLineRemainderWithAt 𝕜 C f x :=
  ⟨Set.univ, Filter.univ_mem,
    show HasQuadraticLineRemainderOnWith 𝕜 C f Set.univ from h⟩

/-- A uniform quadratic bound on the remainder from `lineDeriv` ensures that `lineDeriv` is the
actual line derivative. -/
theorem hasLineDerivAt (h : HasQuadraticLineRemainderWith 𝕜 C f) (x v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  (h.hasQuadraticLineRemainderWithAt x).hasLineDerivAt v

/-- A quadratic line remainder bound controls the failure of `f` to commute with affine
interpolation. -/
theorem norm_image_lineMap_sub_lineMap_le (h : HasQuadraticLineRemainderWith 𝕜 C f)
    (x y : E) (c : 𝕜) :
    ‖f (lineMap x y c) - lineMap (f x) (f y) c‖ ≤
      C * (‖c‖ ^ 2 + ‖c‖) * dist x y ^ 2 :=
  (h.hasQuadraticLineRemainderOnWith Set.univ).norm_image_lineMap_sub_lineMap_le
    (Set.mem_univ x) (Set.mem_univ y) c (Set.mem_univ _)

/-- If the remainder from `lineDeriv` is uniformly bounded by a quadratic function, then the line
derivative is linear in the direction. -/
theorem isLinearMap_lineDeriv (h : HasQuadraticLineRemainderWith 𝕜 C f) (x : E) :
    IsLinearMap 𝕜 (lineDeriv 𝕜 f x) :=
  (h.hasQuadraticLineRemainderWithAt x).isLinearMap_lineDeriv

/-- For a global quadratic line-remainder bound, Fréchet differentiability is equivalent to
continuity. -/
theorem differentiable_iff_continuous (h : HasQuadraticLineRemainderWith 𝕜 C f) :
    Differentiable 𝕜 f ↔ Continuous f := by
  refine ⟨Differentiable.continuous, fun hf x ↦ ?_⟩
  exact (h.hasQuadraticLineRemainderWithAt x).differentiableAt_iff_continuousAt.mpr
    hf.continuousAt

/-- A global quadratic line-remainder bound on a finite-dimensional space over a complete field
implies Fréchet differentiability. -/
theorem differentiable_of_finiteDimensional [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (h : HasQuadraticLineRemainderWith 𝕜 C f) :
    Differentiable 𝕜 f :=
  fun x ↦ (h.hasQuadraticLineRemainderWithAt x).differentiableAt_of_finiteDimensional

end HasQuadraticLineRemainderWith

/-! ## Relation to Lipschitz smoothness -/

variable {K : NNReal} {s : Set E}

/-- Setwise Lipschitz smoothness is setwise ambient differentiability together with the
corresponding quadratic line-remainder bound. -/
theorem lipschitzSmoothOnWith_iff_hasQuadraticLineRemainderOnWith :
    LipschitzSmoothOnWith 𝕜 K f s ↔
      (∀ x ∈ s, DifferentiableAt 𝕜 f x) ∧
        HasQuadraticLineRemainderOnWith 𝕜 (K / 2) f s := by
  rw [lipschitzSmoothOnWith_iff_fderiv]
  refine and_congr_right fun hf ↦ ?_
  rw [hasQuadraticLineRemainderOnWith_iff]
  refine forall_congr' fun x ↦ forall_congr' fun hx ↦
    forall_congr' fun y ↦ forall_congr' fun _ ↦ ?_
  rw [(hf x hx).lineDeriv_eq_fderiv]
  simp only [NNReal.coe_div, NNReal.coe_ofNat]

/-- Global Lipschitz smoothness is global Fréchet differentiability together with the
corresponding quadratic line-remainder bound. -/
theorem lipschitzSmoothWith_iff_hasQuadraticLineRemainderWith :
    LipschitzSmoothWith 𝕜 K f ↔
      Differentiable 𝕜 f ∧ HasQuadraticLineRemainderWith 𝕜 (K / 2) f := by
  rw [lipschitzSmoothWith_iff_fderiv, hasQuadraticLineRemainderWith_iff]
  refine and_congr_right fun hf ↦ ?_
  refine forall_congr' fun x ↦ forall_congr' fun y ↦ ?_
  rw [(hf x).lineDeriv_eq_fderiv]
  simp only [NNReal.coe_div, NNReal.coe_ofNat]

/-- Neighborhood-wise Lipschitz smoothness is eventual ambient Fréchet differentiability
together with the corresponding local quadratic line-remainder bound. -/
theorem lipschitzSmoothWithAt_iff_hasQuadraticLineRemainderWithAt :
    LipschitzSmoothWithAt 𝕜 K f x ↔
      (∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y) ∧
        HasQuadraticLineRemainderWithAt 𝕜 (K / 2) f x := by
  constructor
  · intro h
    obtain ⟨s, hs, hfs⟩ := h.exists_lipschitzSmoothOnWith
    refine ⟨?_, (hasQuadraticLineRemainderWithAt_iff 𝕜).mpr ⟨s, hs, ?_⟩⟩
    · filter_upwards [hs] with y hy
      exact hfs.differentiableAt hy
    · exact (hasQuadraticLineRemainderOnWith_iff 𝕜).mp
        (lipschitzSmoothOnWith_iff_hasQuadraticLineRemainderOnWith.mp hfs).2
  · rintro ⟨hf, hrem⟩
    obtain ⟨s, hs, hrem⟩ := (hasQuadraticLineRemainderWithAt_iff 𝕜).mp hrem
    let t := s ∩ {y | DifferentiableAt 𝕜 f y}
    apply (lipschitzSmoothWithAt_iff_fderiv 𝕜).mpr
    refine ⟨t, inter_mem hs hf, ?_⟩
    apply (lipschitzSmoothOnWith_iff_fderiv 𝕜).mp
    apply lipschitzSmoothOnWith_iff_hasQuadraticLineRemainderOnWith.mpr
    refine ⟨fun _ hy ↦ hy.2, ((hasQuadraticLineRemainderOnWith_iff 𝕜).mpr hrem).mono ?_⟩
    exact Set.inter_subset_left

namespace LipschitzSmoothOnWith

/-- The quadratic line-remainder condition underlying setwise Lipschitz smoothness. -/
theorem hasQuadraticLineRemainderOnWith (h : LipschitzSmoothOnWith 𝕜 K f s) :
    HasQuadraticLineRemainderOnWith 𝕜 (K / 2) f s :=
  (lipschitzSmoothOnWith_iff_hasQuadraticLineRemainderOnWith.mp h).2

end LipschitzSmoothOnWith

namespace LipschitzSmoothWith

/-- The quadratic line-remainder condition underlying global Lipschitz smoothness. -/
theorem hasQuadraticLineRemainderWith (h : LipschitzSmoothWith 𝕜 K f) :
    HasQuadraticLineRemainderWith 𝕜 (K / 2) f :=
  (lipschitzSmoothWith_iff_hasQuadraticLineRemainderWith.mp h).2

/-- A Lipschitz-smooth function has the expected line derivative in every direction. -/
theorem hasLineDerivAt (h : LipschitzSmoothWith 𝕜 K f) (x v : E) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  h.hasQuadraticLineRemainderWith.hasQuadraticLineRemainderWithAt x |>.hasLineDerivAt v

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
  h.hasQuadraticLineRemainderWithAt.hasLineDerivAt v

end LipschitzSmoothWithAt
