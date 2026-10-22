import SurfaceSpectralDisk
import Finsler.Geometry.PhaseNullity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The actual phase curve and a local transverse coordinate

The phase family is obtained by sampling the rotations of the original
closed geodesic. In one fixed polygon chart it is a smooth regular curve,
and its tangent lies in the actual Hessian kernel. Using the inverse
function theorem straightens this curve against the orthogonal phase hyperplane.
On the phase-zero slice, the actual restricted energy has the restricted
Hessian and admits the existing degenerate splitting construction.

Straightening the critical curve does not make the energy independent of
phase away from that curve. No reduced maximum or local-to-orbit homology
injection is assumed to follow from this coordinate construction.
-/

namespace Finsler.SurfacePhaseGeometry

open Set Filter Module
open Finsler.SurfaceSpectralDisk
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

section Straightening

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The derivative of the phase/transverse parametrization. -/
def axisEquiv (v : E) (hv : v ≠ 0) : (ℝ × phaseSlice v) ≃L[ℝ] E :=
  (((LinearEquiv.toSpanNonzeroSingleton ℝ E v hv).prodCongr
    (LinearEquiv.refl ℝ (phaseSlice v))).trans
      ((ℝ ∙ v).prodEquivOfIsCompl (phaseSlice v) (ℝ ∙ v).isCompl_orthogonal)).toContinuousLinearEquiv

theorem axisEquiv_apply (v : E) (hv : v ≠ 0) (t : ℝ) (w : phaseSlice v) :
    axisEquiv v hv (t, w) = t • v + (w : E) := rfl

/-- A smooth regular curve admits an actual local phase/transverse chart.
Its inverse is the explicit map `(t,w) ↦ c(t)+w`. The phase coordinate on
the original curve is exactly its given parameter near zero. -/
theorem exists_straightening (c : ℝ → E) (hc : ContDiffAt ℝ ∞ c 0)
    (hc0 : c 0 = 0) {v : E} (hd : HasDerivAt c v 0) (hv : v ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (ℝ × phaseSlice v),
      (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      (∀ y, e.symm y = c y.1 + (y.2 : E)) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ e.source ∧ e (c t) = (t, 0)) := by
  let f : ℝ × phaseSlice v → E := fun y => c y.1 + (y.2 : E)
  have hf0 : f 0 = 0 := by simp [f, hc0]
  have hf : ContDiffAt ℝ ∞ f 0 :=
    (hc.comp 0 contDiffAt_fst).add
      ((phaseSlice v).subtypeL.contDiff.contDiffAt.comp 0 contDiffAt_snd)
  have hdf : HasFDerivAt f (axisEquiv v hv : (ℝ × phaseSlice v) →L[ℝ] E) 0 := by
    have hdf' : HasFDerivAt f
        ((ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ (phaseSlice v)) +
          (phaseSlice v).subtypeL.comp (ContinuousLinearMap.snd ℝ ℝ (phaseSlice v))) 0 :=
      (hd.hasFDerivAt.comp 0 (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × phaseSlice v)))).add
      ((phaseSlice v).subtypeL.hasFDerivAt.comp 0
        (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × phaseSlice v))))
    have heq : (ContinuousLinearMap.toSpanSingleton ℝ v).comp (ContinuousLinearMap.fst ℝ ℝ (phaseSlice v)) +
        (phaseSlice v).subtypeL.comp (ContinuousLinearMap.snd ℝ ℝ (phaseSlice v)) =
        (axisEquiv v hv : (ℝ × phaseSlice v) →L[ℝ] E) := by
      apply ContinuousLinearMap.ext
      intro y
      rfl
    rwa [heq] at hdf'
  let h := hf.toOpenPartialHomeomorph f hdf (by simp)
  have h0 : (0 : ℝ × phaseSlice v) ∈ h.source := hf.mem_toOpenPartialHomeomorph_source hdf (by simp)
  have he0 : h 0 = 0 := hf0
  refine ⟨h.symm, ?_, ?_, fun _ => rfl, ?_⟩
  · exact he0 ▸ h.map_source h0
  · rw [← he0, h.left_inv h0]
  · have hn := (continuous_id.prodMk (continuous_const (y := (0 : phaseSlice v)))).continuousAt.eventually
      (h.open_source.mem_nhds h0)
    filter_upwards [hn] with t ht
    change (t, 0) ∈ h.source at ht
    have ht' : h (t, 0) = c t := by change c t + (0 : E) = c t; rw [add_zero]
    exact ⟨ht' ▸ h.map_source ht, by rw [← ht', h.left_inv ht]⟩

end Straightening

section Polygon

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops
open Finsler.SphereCoordinateEuler Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonModel Finsler.SamplePhase Finsler.PhaseNullity Finsler.SmoothSobolev
open scoped Manifold

variable {n : ℕ} (N : ℕ) [NeZero N]

/-- Sample the original smooth loop after shifting its phase. -/
def phasePolygon (γ : SmoothLoop n) (a : ℝ) : ZMod N → Sphere n :=
  fun i => γ ((i.val : ℝ) / N + a)

theorem phasePolygon_eq_sample (γ : SmoothLoop n) (a : ℝ) :
    phasePolygon N γ a = samplePoly N (ofSmooth (shift γ a)) := by
  funext i
  apply Subtype.ext
  exact (samplePoly_shift_apply γ a i).symm

omit [NeZero N] in
theorem phasePolygon_continuous (γ : SmoothLoop n) : Continuous (phasePolygon N γ) :=
  continuous_pi fun _ => γ.smooth.continuous.comp (continuous_const.add continuous_id)

/-- The phase curve in the fixed chart at phase zero, translated to the origin. -/
def phaseCoordinates (γ : SmoothLoop n) (a : ℝ) : Model n N :=
  PolygonChart.chart (phasePolygon N γ 0) (phasePolygon N γ a) - base (phasePolygon N γ 0)

theorem phaseCoordinates_zero (γ : SmoothLoop n) : phaseCoordinates N γ 0 = 0 := by
  change base (phasePolygon N γ 0) - base (phasePolygon N γ 0) = 0
  exact sub_self _

/-- The phase tangent is the tuple of actual derivatives in the sphere charts. -/
def phaseVector (γ : SmoothLoop n) : Model n N :=
  WithLp.toLp 2 (fun i => deriv (coordinateCurve (phasePolygon N γ 0 i) γ) ((i.val : ℝ) / N))

theorem phaseCoordinates_smooth (γ : SmoothLoop n) : ContDiffAt ℝ ∞ (phaseCoordinates N γ) 0 := by
  have hcoords : ContDiffAt ℝ ∞
      (fun a : ℝ => fun i : ZMod N => coordinateCurve (phasePolygon N γ 0 i) γ ((i.val : ℝ) / N + a)) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    have hi : γ ((i.val : ℝ) / N) ∈ (extChartAt (𝓡 n) (phasePolygon N γ 0 i)).source := by
      simpa only [phasePolygon, add_zero] using mem_extChartAt_source (γ ((i.val : ℝ) / N))
    have hi' : ContDiffAt ℝ ∞ (coordinateCurve (phasePolygon N γ 0 i) γ)
        ((i.val : ℝ) / N + (0 : ℝ)) := by simpa using coordinateCurve_smoothAt (phasePolygon N γ 0 i) γ hi
    exact hi'.comp (0 : ℝ)
      ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (i.val : ℝ) / N) 0).add contDiffAt_id)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ZMod N => Coordinates n)).symm.contDiff.contDiffAt.comp 0
    hcoords).sub contDiffAt_const

theorem phaseCoordinates_hasDerivAt (γ : SmoothLoop n) :
    HasDerivAt (phaseCoordinates N γ) (phaseVector N γ) 0 := by
  have hcoords : HasDerivAt
      (fun a : ℝ => fun i : ZMod N => coordinateCurve (phasePolygon N γ 0 i) γ ((i.val : ℝ) / N + a))
      (fun i : ZMod N => deriv (coordinateCurve (phasePolygon N γ 0 i) γ) ((i.val : ℝ) / N)) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have hi : γ ((i.val : ℝ) / N) ∈ (extChartAt (𝓡 n) (phasePolygon N γ 0 i)).source := by
      simpa only [phasePolygon, add_zero] using mem_extChartAt_source (γ ((i.val : ℝ) / N))
    have hd := ((coordinateCurve_smoothAt (phasePolygon N γ 0 i) γ hi).differentiableAt (by simp)).hasDerivAt
    simpa only [one_smul, Function.comp_def, id_eq] using hd.scomp_of_eq (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add ((i.val : ℝ) / N)) (by simp)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ZMod N => Coordinates n)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    hcoords).sub_const (base (phasePolygon N γ 0))

omit [NeZero N] in
theorem phaseVector_ne_zero (γ : SmoothLoop n) (hreg : Geodesics.Regular γ) : phaseVector N γ ≠ 0 := by
  intro hz
  have h := congrArg (fun v : Model n N => v 0) hz
  have hne := GeodesicArcs.deriv_coordinateCurve_ne_zero hreg (γ 0) (mem_extChartAt_source (γ 0))
  apply hne
  change deriv (coordinateCurve (phasePolygon N γ 0 0) γ) (((0 : ZMod N).val : ℝ) / N) = 0 at h
  simpa [phasePolygon] using h

theorem phaseCoordinates_eventually_source (γ : SmoothLoop n) :
    ∀ᶠ a in 𝓝 (0 : ℝ), phasePolygon N γ a ∈ (PolygonChart.chart (phasePolygon N γ 0)).source := by
  apply (phasePolygon_continuous N γ).continuousAt.eventually
  apply (PolygonChart.chart (phasePolygon N γ 0)).open_source.mem_nhds
  rw [PolygonChart.mem_chart_source]
  exact fun _ => mem_extChartAt_source _

variable {N} (F : ReversibleMetric n) (S : SegmentData F)

/-- A stationary polygon has zero coordinate gradient in any actual
polygon chart containing it, not only in its own centered chart. -/
theorem grad_eq_zero_in_chart (q r : ZMod N → Sphere n)
    (hr : r ∈ (PolygonChart.chart q).source)
    (hshort : ShortPolygon S.δ r) (hne : ∀ i, r (i + 1) ≠ r i)
    (hc : PolyCritical F N r) : grad F q (PolygonChart.chart q r) = 0 := by
  apply (Hessian.gradient_eq_zero_iff _ _).mpr
  have hy := (PolygonChart.chart q).map_source hr
  have hE := PolygonSmooth.polyEnergyN_contDiffAt F S.smooth hshort hne
  rw [← decode_chart q r hr] at hE
  have hd := (decode_contDiffAt q hy).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ (PolygonChart.energy F q) (PolygonChart.chart q r) :=
    (hE.comp _ ((decode_contDiffAt q hy).of_le (by simp))).differentiableAt (by norm_num)
  apply ContinuousLinearMap.ext
  intro v
  have hline : HasDerivAt (fun t : ℝ => PolygonChart.chart q r + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (PolygonChart.chart q r)
  have hcurve := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hstationary := hc _ _ (by simpa using decode_chart q r hr)
    (fun t i => norm_decode q _ i) hcurve
  have hf' := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have he : (fun t : ℝ => PolygonChart.energy F q (PolygonChart.chart q r + t • v)) =
      fun t => polyEnergy F N (decode q (PolygonChart.chart q r + t • v)) :=
    funext fun t => energy_eq F q _
  simp only [Function.comp_def] at hf'
  rw [he] at hf'
  exact hf'.unique hstationary

variable (g : Geodesics.ClosedGeodesic F)
  (hfacts : ∀ a : ℝ, SampleFacts S (ofSmooth (shift g.loop a)) N)

include hfacts in
theorem phaseCoordinates_gradient_zero :
    ∀ᶠ a in 𝓝 (0 : ℝ),
      grad F (phasePolygon N g.loop 0)
        (base (phasePolygon N g.loop 0) + phaseCoordinates N g.loop a) = 0 := by
  filter_upwards [phaseCoordinates_eventually_source N g.loop] with a ha
  obtain ⟨hs, hn, -, -, hc, -, -⟩ := hfacts a
  rw [← phasePolygon_eq_sample] at hs hn hc
  have h := grad_eq_zero_in_chart F S _ _ ha hs hn hc
  convert h using 2
  dsimp only [phaseCoordinates]
  abel

include hfacts in
/-- Differentiate the actual stationary phase curve: its explicit nonzero
phase vector belongs to the actual polygon Hessian kernel. -/
theorem phaseVector_mem_ker :
    hessian F (phasePolygon N g.loop 0) (phaseVector N g.loop) = 0 := by
  obtain ⟨hs, hn, -, -, -, -, -⟩ := hfacts 0
  rw [← phasePolygon_eq_sample] at hs hn
  have hd := (grad_hasFDerivAt F S.smooth hs hn).comp_hasDerivAt_of_eq 0
    ((phaseCoordinates_hasDerivAt N g.loop).const_add (base (phasePolygon N g.loop 0)))
    (by rw [phaseCoordinates_zero, add_zero])
  have hz : HasDerivAt
      (fun a : ℝ => grad F (phasePolygon N g.loop 0)
        (base (phasePolygon N g.loop 0) + phaseCoordinates N g.loop a)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : Model n N)).congr_of_eventuallyEq
      (phaseCoordinates_gradient_zero F S g hfacts)
  exact hd.unique hz

include hfacts in
/-- The parametrized polygon model has at least the phase null direction,
even when its other critical directions are degenerate. -/
theorem one_le_nullity : 1 ≤ nullity F (phasePolygon N g.loop 0) := by
  have hv := phaseVector_mem_ker F S g hfacts
  have hne := phaseVector_ne_zero N g.loop g.regular
  have hn : Nontrivial (LinearMap.ker (hessian F (phasePolygon N g.loop 0)).toLinearMap) :=
    nontrivial_of_ne (⟨phaseVector N g.loop, hv⟩ : LinearMap.ker (hessian F (phasePolygon N g.loop 0)).toLinearMap)
      (0 : LinearMap.ker (hessian F (phasePolygon N g.loop 0)).toLinearMap)
      (fun h => hne (congrArg Subtype.val h))
  let := hn
  exact Module.finrank_pos

end Polygon

section Model

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.IntervalSobolev
open Finsler.PolygonChart Finsler.PolygonHessian Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.PolygonSampling Finsler.PolygonModel Finsler.SamplePhase Finsler.PhaseNullity
open Finsler.SmoothSobolev Finsler.SurfacePolygonHomology Finsler.SurfaceMorseData

variable {n : ℕ}

/-- One sufficiently fine polygon model works for every rotation of the
given closed geodesic. The strict energy cut is the original loop's cut. -/
structure GeodesicPhaseModel (F : ReversibleMetric n) (g : Geodesics.ClosedGeodesic F) (a : ℝ) where
  vertices : ℕ
  [nonzero : NeZero vertices]
  model : PolygonModelData F a vertices
  facts : ∀ t : ℝ, SampleFacts model.toSegmentData (ofSmooth (shift g.loop t)) vertices
  below : SobolevEnergy.energy F (ofSmooth g.loop) < a ^ 2

attribute [instance] GeodesicPhaseModel.nonzero

/-- Uniform fine sampling constructs the complete phase model for every
closed geodesic, without a nondegeneracy or isolation hypothesis. -/
theorem nonempty_geodesicPhaseModel (F : ReversibleMetric n) (g : Geodesics.ClosedGeodesic F)
    {a : ℝ} (ha : SobolevEnergy.energy F (ofSmooth g.loop) < a ^ 2) :
    Nonempty (GeodesicPhaseModel F g a) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨N₁, hN₁⟩ := exists_sample_facts_all S g
  let N := max N₀ N₁ + 1
  have hN : 0 < N := by dsimp [N]; omega
  let : NeZero N := ⟨by omega⟩
  let M : PolygonModelData F a N := PolygonModelData.mk S (hN₀ N (by dsimp [N]; omega) hN)
  exact ⟨⟨N, M, fun t => hN₁ t N (by dsimp [N]; omega), ha⟩⟩

variable {F : ReversibleMetric n} {g : Geodesics.ClosedGeodesic F} {a : ℝ}
  (D : GeodesicPhaseModel F g a)

/-- The phase family in the actual open short-polygon space. -/
def phasePoint (t : ℝ) : Short D.model :=
  ⟨phasePolygon D.vertices g.loop t, by rw [phasePolygon_eq_sample]; exact (D.facts t).1⟩

theorem phasePoint_continuous : Continuous (phasePoint D) :=
  (phasePolygon_continuous D.vertices g.loop).subtype_mk _

theorem phasePoint_critical (t : ℝ) : PolyCritical F D.vertices (phasePoint D t).val := by
  change PolyCritical F D.vertices (phasePolygon D.vertices g.loop t)
  rw [phasePolygon_eq_sample]
  exact (D.facts t).2.2.2.2.1

theorem phasePoint_nonzero_edges (t : ℝ) :
    ∀ i, (phasePoint D t).val (i + 1) ≠ (phasePoint D t).val i := by
  change ∀ i, phasePolygon D.vertices g.loop t (i + 1) ≠ phasePolygon D.vertices g.loop t i
  rw [phasePolygon_eq_sample]
  exact (D.facts t).2.1

/-- The broken-geodesic family is exactly the rotation family, including
its parametrization. -/
theorem phasePoint_broken (t : ℝ) : broken D.model (phasePoint D t) = ofSmooth (shift g.loop t) := by
  obtain ⟨hs, -, -, -, -, -, hbr⟩ := D.facts t
  have hp : phasePoint D t = ⟨samplePoly D.vertices (ofSmooth (shift g.loop t)), hs⟩ :=
    Subtype.ext (phasePolygon_eq_sample D.vertices g.loop t)
  rw [hp]
  exact hbr hs

theorem phasePoint_energy (t : ℝ) :
    polygonEnergy D.model (phasePoint D t) = SobolevEnergy.energy F (ofSmooth g.loop) := by
  rw [← energy_broken_eq, phasePoint_broken, energy_ofSmooth_shift]

theorem phasePoint_below (t : ℝ) : polygonEnergy D.model (phasePoint D t) < a ^ 2 := by
  rw [phasePoint_energy]
  exact D.below

theorem phase_hessian_symmetric :
    (hessian F (phasePoint D 0).val).toLinearMap.IsSymmetric :=
  hessian_isSymmetric F D.model.smooth (phasePoint D 0).property (phasePoint_nonzero_edges D 0)

/-- The preceding nullity correction now applies to the actual sampled
geodesic's explicit phase vector, whose nonvanishing and kernel membership
are proved rather than supplied as hypotheses. -/
theorem actual_phase_nullity :
    finrank ℝ (LinearMap.ker
      (phaseRestriction (hT := phase_hessian_symmetric D) (phaseVector D.vertices g.loop)
        (phaseVector_mem_ker F D.model.toSegmentData g D.facts)).toLinearMap) + 1 =
      nullity F (phasePoint D 0).val :=
  phaseRestriction_nullity (hT := phase_hessian_symmetric D) _ _
    (phaseVector_ne_zero D.vertices g.loop g.regular)

/-- An actual phase/transverse chart on the short-polygon space. On its
phase axis it parametrizes precisely the original rotations. At phase zero
the transverse coordinate is the hyperplane perpendicular to the phase
tangent in the original Hilbert coordinates.
No phase independence of the energy off the axis is claimed. -/
theorem exists_phaseChart :
    ∃ e : OpenPartialHomeomorph (Short D.model) (ℝ × phaseSlice (phaseVector D.vertices g.loop)),
      phasePoint D 0 ∈ e.source ∧ e (phasePoint D 0) = 0 ∧
      (∀ x ∈ e.source, x ∈ (centeredChart D.model (phasePoint D 0)).source) ∧
      (∀ y ∈ e.target, centeredChart D.model (phasePoint D 0) (e.symm y) =
        phaseCoordinates D.vertices g.loop y.1 + (y.2 : Model n D.vertices)) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), phasePoint D t ∈ e.source ∧ e (phasePoint D t) = (t, 0)) := by
  let c := centeredChart D.model (phasePoint D 0)
  have hcoord : ∀ t, c (phasePoint D t) = phaseCoordinates D.vertices g.loop t := by
    intro t
    change PolygonChart.chart (phasePolygon D.vertices g.loop 0) (phasePolygon D.vertices g.loop t) +
      -base (phasePolygon D.vertices g.loop 0) = _
    rw [← sub_eq_add_neg]
    rfl
  obtain ⟨h, h0, hh0, hinv, hphase⟩ := exists_straightening
    (phaseCoordinates D.vertices g.loop) (phaseCoordinates_smooth D.vertices g.loop)
    (phaseCoordinates_zero D.vertices g.loop) (phaseCoordinates_hasDerivAt D.vertices g.loop)
    (phaseVector_ne_zero D.vertices g.loop g.regular)
  let e := c.trans h
  have hc0 : phasePoint D 0 ∈ c.source := centeredChart_center_mem _ _
  have hczero : c (phasePoint D 0) = 0 := centeredChart_center _ _
  refine ⟨e, ⟨hc0, ?_⟩, ?_, fun x hx => hx.1, ?_, ?_⟩
  · change c (phasePoint D 0) ∈ h.source
    rwa [hczero]
  · change h (c (phasePoint D 0)) = 0
    rw [hczero, hh0]
  · intro y hy
    change c (c.symm (h.symm y)) = _
    rw [c.right_inv hy.2, hinv]
  · have hn := (phasePoint_continuous D).continuousAt.eventually (c.open_source.mem_nhds hc0)
    filter_upwards [hn, hphase] with t ht htp
    exact ⟨⟨ht, by change c (phasePoint D t) ∈ h.source; rw [hcoord]; exact htp.1⟩,
      by change h (c (phasePoint D t)) = _; rw [hcoord]; exact htp.2⟩

end Model

section TransverseEnergy

set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency true

open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.SurfaceMorseData Finsler.SurfacePolygonHomology Finsler.LyapunovSchmidt

variable {n : ℕ} {F : ReversibleMetric n} {g : Geodesics.ClosedGeodesic F} {a : ℝ}
  (D : GeodesicPhaseModel F g a)

/-- The actual energy on the linear transverse slice in the centered chart. -/
def transverseEnergy (w : phaseSlice (phaseVector D.vertices g.loop)) : ℝ :=
  PolygonChart.energy F (phasePoint D 0).val (base (phasePoint D 0).val + (w : Model n D.vertices))

/-- Orthogonal projection of the actual coordinate gradient onto the slice. -/
def transverseGradient (w : phaseSlice (phaseVector D.vertices g.loop)) :
    phaseSlice (phaseVector D.vertices g.loop) :=
  (phaseSlice (phaseVector D.vertices g.loop)).orthogonalProjectionOnto
    (grad F (phasePoint D 0).val (base (phasePoint D 0).val + (w : Model n D.vertices)))

/-- The restriction of the actual Hessian to the transverse hyperplane. -/
def transverseHessian : phaseSlice (phaseVector D.vertices g.loop) →L[ℝ]
    phaseSlice (phaseVector D.vertices g.loop) :=
  phaseRestriction (hT := phase_hessian_symmetric D) (phaseVector D.vertices g.loop)
    (phaseVector_mem_ker F D.model.toSegmentData g D.facts)

/-- In the actual nonlinear phase chart, the phase-zero slice has precisely
the restricted energy above, both as a polygon and as its genuine H¹ loop. -/
theorem exists_phaseChart_energy :
    ∃ e : OpenPartialHomeomorph (Short D.model) (ℝ × phaseSlice (phaseVector D.vertices g.loop)),
      phasePoint D 0 ∈ e.source ∧ e (phasePoint D 0) = 0 ∧
      (∀ w, (0, w) ∈ e.target →
        polygonEnergy D.model (e.symm (0, w)) = transverseEnergy D w ∧
        SobolevEnergy.energy F (PolygonModel.broken D.model (e.symm (0, w))) = transverseEnergy D w) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), phasePoint D t ∈ e.source ∧ e (phasePoint D t) = (t, 0)) := by
  obtain ⟨e, hp, he0, hsource, hcoord, hphase⟩ := exists_phaseChart D
  refine ⟨e, hp, he0, ?_, hphase⟩
  intro w hw
  have hE : polygonEnergy D.model (e.symm (0, w)) = transverseEnergy D w := by
    rw [centeredChart_energy D.model (phasePoint D 0) _ (hsource _ (e.map_target hw)), hcoord _ hw]
    simp only [phaseCoordinates_zero, zero_add, transverseEnergy]
  exact ⟨hE, by rw [energy_broken_eq, hE]⟩

theorem transverseHessian_symmetric :
    LinearMap.IsSymmetric (E := phaseSlice (phaseVector D.vertices g.loop))
      (transverseHessian D).toLinearMap :=
  phaseRestriction_symmetric (hT := phase_hessian_symmetric D) (phaseVector D.vertices g.loop)
    (phaseVector_mem_ker F D.model.toSegmentData g D.facts)

theorem transverseHessian_nullity :
    finrank ℝ (LinearMap.ker (transverseHessian D).toLinearMap) + 1 =
      nullity F (phasePoint D 0).val := actual_phase_nullity D

theorem transverseEnergy_smooth : ContDiffAt ℝ 3 (transverseEnergy D) 0 := by
  have hf := energy_contDiffAt F D.model.smooth (phasePoint D 0).property (phasePoint_nonzero_edges D 0)
  have hf' : ContDiffAt ℝ 3 (PolygonChart.energy F (phasePoint D 0).val)
      (base (phasePoint D 0).val + ((0 : phaseSlice (phaseVector D.vertices g.loop)) : Model n D.vertices)) :=
    by simpa using hf
  exact hf'.comp (0 : phaseSlice (phaseVector D.vertices g.loop))
    (contDiffAt_const.add (phaseSlice (phaseVector D.vertices g.loop)).subtypeL.contDiff.contDiffAt)

theorem transverseGradient_smooth : ContDiffAt ℝ 2 (transverseGradient D) 0 := by
  have hf := grad_contDiffAt F D.model.smooth (phasePoint D 0).property (phasePoint_nonzero_edges D 0)
  have hf' : ContDiffAt ℝ 2 (grad F (phasePoint D 0).val)
      (base (phasePoint D 0).val + ((0 : phaseSlice (phaseVector D.vertices g.loop)) : Model n D.vertices)) :=
    by simpa using hf
  exact (phaseSlice (phaseVector D.vertices g.loop)).orthogonalProjectionOnto.contDiff.contDiffAt.comp
    (0 : phaseSlice (phaseVector D.vertices g.loop))
    (hf'.comp (0 : phaseSlice (phaseVector D.vertices g.loop))
      (contDiffAt_const.add (phaseSlice (phaseVector D.vertices g.loop)).subtypeL.contDiff.contDiffAt))

theorem transverseGradient_zero : transverseGradient D 0 = 0 := by
  have h := grad_eq_zero_of_polyCritical F D.model.smooth (phasePoint D 0).property
    (phasePoint_nonzero_edges D 0) (phasePoint_critical D 0)
  simp only [transverseGradient, Submodule.coe_zero, add_zero, h, map_zero]

theorem transverseGradient_hasFDerivAt :
    HasFDerivAt (transverseGradient D) (transverseHessian D) 0 := by
  let W := phaseSlice (phaseVector D.vertices g.loop)
  have hi : HasFDerivAt (fun w : W => base (phasePoint D 0).val + (w : Model n D.vertices))
      W.subtypeL 0 := W.subtypeL.hasFDerivAt.const_add _
  have hd' : HasFDerivAt (grad F (phasePoint D 0).val) (hessian F (phasePoint D 0).val)
      (base (phasePoint D 0).val + ((0 : W) : Model n D.vertices)) := by
    simpa only [Submodule.coe_zero, add_zero] using
      grad_hasFDerivAt F D.model.smooth (phasePoint D 0).property (phasePoint_nonzero_edges D 0)
  have hd := hd'.comp (0 : W) hi
  have hp := W.orthogonalProjectionOnto.hasFDerivAt.comp (0 : W) hd
  have he : W.orthogonalProjectionOnto.comp
      ((hessian F (phasePoint D 0).val).comp W.subtypeL) = transverseHessian D := by
    apply ContinuousLinearMap.ext
    intro w
    change W.orthogonalProjectionOnto ((transverseHessian D w : W) : Model n D.vertices) = _
    exact W.orthogonalProjectionOnto_mem_subspace_eq_self _
  rwa [he] at hp

/-- The projected gradient represents the derivative of the actual slice
energy on a whole neighborhood, not just at its center. -/
theorem transverseEnergy_eventually_hasFDerivAt :
    ∀ᶠ w in 𝓝 (0 : phaseSlice (phaseVector D.vertices g.loop)),
      HasFDerivAt (transverseEnergy D) (innerSL ℝ (transverseGradient D w)) w := by
  let W := phaseSlice (phaseVector D.vertices g.loop)
  have ht : Tendsto (fun w : W => base (phasePoint D 0).val + (w : Model n D.vertices))
      (𝓝 0) (𝓝 (base (phasePoint D 0).val)) := by
    have hc : Continuous (fun w : W => base (phasePoint D 0).val + (w : Model n D.vertices)) :=
      continuous_const.add W.subtypeL.continuous
    simpa only [Submodule.coe_zero, add_zero] using hc.continuousAt.tendsto (x := 0)
  filter_upwards [ht.eventually (eventually_hasFDerivAt F D.model.smooth
    (phasePoint D 0).property (phasePoint_nonzero_edges D 0))] with w hw
  change HasFDerivAt (PolygonChart.energy F (phasePoint D 0).val)
    (innerSL ℝ (grad F (phasePoint D 0).val (base (phasePoint D 0).val + (w : Model n D.vertices))))
      (base (phasePoint D 0).val + (w : Model n D.vertices)) at hw
  have hi : HasFDerivAt (fun w : W => base (phasePoint D 0).val + (w : Model n D.vertices))
      W.subtypeL w := W.subtypeL.hasFDerivAt.const_add _
  have hd := hw.comp w hi
  have he : (innerSL ℝ (grad F (phasePoint D 0).val
      (base (phasePoint D 0).val + (w : Model n D.vertices)))).comp W.subtypeL =
      innerSL ℝ (transverseGradient D w) := by
    apply ContinuousLinearMap.ext
    intro u
    exact (W.inner_orthogonalProjectionOnto_eq_of_mem_right u _).symm
  rwa [he] at hd

/-- The transverse operator is the genuine Hessian of the restricted
energy; no surrogate bilinear form is introduced. -/
theorem transverseHessian_eq_operator :
    transverseHessian D = Hessian.operator (E := phaseSlice (phaseVector D.vertices g.loop))
      (transverseEnergy D) 0 := by
  have hg : transverseGradient D =ᶠ[𝓝 0] Hessian.gradient (transverseEnergy D) := by
    filter_upwards [transverseEnergy_eventually_hasFDerivAt D] with w hw
    apply ext_inner_right ℝ
    intro u
    rw [Hessian.inner_gradient, hw.fderiv]
    rfl
  exact (transverseGradient_hasFDerivAt D).unique
    ((Hessian.gradient_hasFDerivAt (E := phaseSlice (phaseVector D.vertices g.loop)) (f := transverseEnergy D)
      ((transverseEnergy_smooth D).of_le (by norm_num))).congr_of_eventuallyEq hg)

/-- The actual transverse energy admits a degenerate splitting chart.
Its kernel has exactly one fewer dimension than the parametrized Hessian.
The reduced function is not asserted to be a strict maximum. -/
theorem exists_transverse_splitting :
    ∃ (σ : phaseSlice (phaseVector D.vertices g.loop) → phaseSlice (phaseVector D.vertices g.loop))
      (e : OpenPartialHomeomorph (phaseSlice (phaseVector D.vertices g.loop))
        (phaseSlice (phaseVector D.vertices g.loop))),
      ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧ 0 ∈ e.source ∧ e 0 = 0 ∧
      ∀ w ∈ e.source,
        transverseEnergy D w = transverseEnergy D (σ (kerProj (transverseHessian D) (e w))) +
          1 / 2 * ⟪transverseHessian D (e w), e w⟫ := by
  obtain ⟨σ, e, hσ, hσ0, h0, he0, hE⟩ :=
    SplittingLemma.exists_homeomorph (A := transverseHessian D) (G := transverseGradient D)
      (p := (0 : phaseSlice (phaseVector D.vertices g.loop))) (f := transverseEnergy D)
      (transverseHessian_symmetric D)
      (transverseGradient_smooth D) (transverseGradient_hasFDerivAt D)
      (transverseGradient_zero D) (transverseEnergy_eventually_hasFDerivAt D)
  refine ⟨σ, e, hσ, hσ0, h0, he0, ?_⟩
  intro w hw
  obtain ⟨hk, hf⟩ := hE w hw
  simpa only [zero_add, ← hk] using hf

end TransverseEnergy

end

end Finsler.SurfacePhaseGeometry
