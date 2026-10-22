import SurfacePolygonHomology
import Finsler.Geometry.PolygonSplitting
import Finsler.Geometry.SamplePhase

/-!
# Maximal disks in local Morse coordinates

A normal form on an open coordinate neighborhood gives an actual small
closed disk and a continuous left inverse. Radial clipping extends the
inverse coordinate to the whole neighborhood without identifying any
nonzero coordinate with the center. The maximal-disk and transverse-energy
conditions therefore imply the hypotheses of the local homology detector.

The reduced function's strict maximum is an explicit geometric hypothesis;
it is not asserted for arbitrary closed geodesics.
-/

namespace Finsler.SurfaceMorseData

open CategoryTheory Set Metric Filter
open Finsler.SurfaceLocalHomology Finsler.SurfacePolygonHomology
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

/-- Continuous radial clipping onto the standard closed disk. -/
def clip (q : ℕ) : C(EuclideanSpace ℝ (Fin q), Disk q) where
  toFun x := ⟨⟨(max 1 ‖x‖)⁻¹ • x, by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (le_trans zero_le_one (le_max_left _ _)))]
    have hpos : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    rw [inv_mul_le_iff₀ hpos]
    simp⟩⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply Continuous.subtype_mk
    exact ((continuous_const.max continuous_norm).inv₀
      (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))).smul continuous_id

theorem clip_coordinates (q : ℕ) (x : EuclideanSpace ℝ (Fin q)) :
    coordinates q (clip q x) = (max 1 ‖x‖)⁻¹ • x := rfl

theorem clip_of_mem (q : ℕ) (x : Disk q) : clip q (coordinates q x) = x := by
  have hx : ‖coordinates q x‖ ≤ 1 := mem_closedBall_zero_iff.mp x.down.property
  apply ULift.ext
  apply Subtype.ext
  change (max 1 ‖coordinates q x‖)⁻¹ • coordinates q x = coordinates q x
  rw [max_eq_left hx, inv_one, one_smul]

theorem clip_eq_center_iff (q : ℕ) (x : EuclideanSpace ℝ (Fin q)) :
    clip q x = center q ↔ x = 0 := by
  rw [← coordinates_eq_zero_iff, clip_coordinates]
  exact smul_eq_zero.trans (or_iff_right (inv_ne_zero
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))))

/-- Geometric disk data in an actual open neighborhood of the point. -/
structure MaximalDiskData {X : Type} [TopologicalSpace X] (E : X → ℝ) (p : X) (q : ℕ) where
  neighborhood : Set X
  isOpen : IsOpen neighborhood
  family : C(Disk q, neighborhood)
  center_eq : (family (center q)).val = p
  detector : C(neighborhood, Disk q)
  left_inverse : ∀ x, detector (family x) = x
  strict_max : ∀ x, x ≠ center q → E (family x).val < E p
  central_min : ∀ x : neighborhood, detector x = center q → E p ≤ E x.val

/-- Choose a small disk inside a genuine open coordinate chart. The energy
splits into a reduced strict maximum and a transverse minimum; a germ of
strict maximality suffices. The disk and its continuous detector are built,
including their exact center and left-inverse identities. -/
theorem nonempty_maximalDiskData_of_normalForm
    {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {q : ℕ}
    (E : X → ℝ) (p : X) (z₀ : Z)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin q) × Z))
    (hp : p ∈ e.source) (he : e p = (0, z₀))
    (R : EuclideanSpace ℝ (Fin q) → ℝ) (Q : Z → ℝ)
    (hE : ∀ x ∈ e.source, E x = R (e x).1 + Q (e x).2)
    (hmax : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin q)), v ≠ 0 → R v < R 0)
    (hmin : ∀ z, (0, z) ∈ e.target → Q z₀ ≤ Q z) :
    Nonempty (MaximalDiskData E p q) := by
  have htarget : (0, z₀) ∈ e.target := he ▸ e.map_source hp
  have hnear : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin q)),
      (v, z₀) ∈ e.target ∧ (v ≠ 0 → R v < R 0) :=
    ((continuous_id.prodMk continuous_const).continuousAt.eventually
      (e.open_target.mem_nhds htarget)).and hmax
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hscaled : ∀ x : Disk q, ρ • coordinates q x ∈ ball 0 ε := by
    intro x
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hx : ‖coordinates q x‖ ≤ 1 := mem_closedBall_zero_iff.mp x.down.property
    calc
      ρ * ‖coordinates q x‖ ≤ ρ := by nlinarith
      _ < ε := by dsimp [ρ]; linarith
  let v : C(Disk q, e.target) :=
    ⟨fun x => ⟨(ρ • coordinates q x, z₀), (hball (hscaled x)).1⟩,
      (((coordinates q).continuous.const_smul ρ).prodMk continuous_const).subtype_mk _⟩
  let f : C(Disk q, e.source) :=
    (⟨e.toHomeomorphSourceTarget.symm, e.toHomeomorphSourceTarget.symm.continuous⟩ :
      C(e.target, e.source)).comp v
  have hf : ∀ x, e (f x).val = (ρ • coordinates q x, z₀) := fun x =>
    e.right_inv (v x).property
  have hc : (f (center q)).val = p := by
    apply e.injOn (f (center q)).property hp
    rw [hf, he]
    simp [coordinates, SurfaceLocalHomology.center]
  let r : C(e.source, Disk q) := (clip q).comp
    ⟨fun x => ρ⁻¹ • (e x.val).1,
      by
        have ht : Continuous (fun x : e.source => e x.val) :=
          e.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property)
        exact (continuous_const : Continuous (fun _ : e.source => (ρ⁻¹ : ℝ))).smul ht.fst⟩
  have hr : ∀ x, r (f x) = x := by
    intro x
    change clip q (ρ⁻¹ • (e (f x).val).1) = x
    rw [hf, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, clip_of_mem]
  refine ⟨⟨e.source, e.open_source, f, hc, r, hr, ?_, ?_⟩⟩
  · intro x hx
    rw [hE _ (f x).property, hE p hp, hf, he]
    apply add_lt_add_of_lt_of_le _ le_rfl
    apply (hball (hscaled x)).2
    exact smul_ne_zero hρ.ne' ((coordinates_eq_zero_iff q x).not.mpr hx)
  · intro x hx
    change clip q (ρ⁻¹ • (e x.val).1) = center q at hx
    have hx0 : (e x.val).1 = 0 :=
      (smul_eq_zero.mp ((clip_eq_center_iff q _).mp hx)).resolve_left (inv_ne_zero hρ.ne')
    rw [hE p hp, hE x.val x.property, he, hx0]
    apply add_le_add le_rfl
    apply hmin
    simpa only [← hx0, Prod.eta] using e.map_source x.property

section Geodesic

open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.PolygonModel Finsler.PolygonSampling Finsler.PolygonLoop
open Finsler.PolygonCritical Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.LyapunovSchmidt

/-- An exact critical polygon model whose edges are all nonconstant. This
is the regularity required by the existing polygon splitting lemma. -/
structure RegularGeodesicModel {n : ℕ} (F : ReversibleMetric n)
    (g : Geodesics.ClosedGeodesic F) (a : ℝ) where
  data : GeodesicModel F g a
  nonzero_edges : ∀ i, data.point.val (i + 1) ≠ data.point.val i

/-- Fine sampling supplies the nonzero edges as well as exact reconstruction,
criticality and the prescribed strict energy cut. -/
theorem nonempty_regularGeodesicModel {n : ℕ} (F : ReversibleMetric n)
    (g : Geodesics.ClosedGeodesic F) {a : ℝ}
    (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    Nonempty (RegularGeodesicModel F g a) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨N₁, hN₁⟩ := SamplePhase.exists_sample_facts S g
  let N := max N₀ N₁ + 1
  have hN : 0 < N := by dsimp [N]; omega
  let : NeZero N := ⟨by omega⟩
  have hfacts := hN₁ 0 (by simp) N (by dsimp [N]; omega)
  rw [Loops.shift_zero] at hfacts
  obtain ⟨hs, hne, -, -, hc, -, hbr⟩ := hfacts
  let M : PolygonModelData F a N :=
    PolygonModelData.mk S (hN₀ N (by dsimp [N]; omega) hN)
  let p : Short M := ⟨samplePoly N (SmoothSobolev.ofSmooth g.loop), hs⟩
  have hb : broken M p = SmoothSobolev.ofSmooth g.loop := hbr hs
  have hE : polygonEnergy M p < a ^ 2 := by
    rw [← energy_broken_eq, hb]
    exact ha
  exact ⟨⟨⟨N, M, p, hc, hE, hb⟩, hne⟩⟩

variable {n N : ℕ} {F : ReversibleMetric n} {a : ℝ} [NeZero N]
  (M : PolygonModelData F a N) (p : Short M)

/-- The actual product sphere chart restricted to the open short-polygon
space. -/
def shortChart : OpenPartialHomeomorph (Short M) (Model n N) :=
  (PolygonChart.chart p.val).subtypeRestr
    (s := ⟨{q | ShortPolygon M.δ q}, shortPolygon_isOpen M.δ N⟩) ⟨p⟩

theorem shortChart_center_mem : p ∈ (shortChart M p).source := by
  rw [shortChart, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
  rw [PolygonChart.mem_chart_source]
  intro i
  exact mem_extChartAt_source (p.val i)

theorem shortChart_center : shortChart M p p = base p.val := rfl

theorem shortChart_energy (x : Short M) (hx : x ∈ (shortChart M p).source) :
    polygonEnergy M x = PolygonChart.energy F p.val (shortChart M p x) := by
  have hx' : x.val ∈ (PolygonChart.chart p.val).source := by
    simpa only [shortChart, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hx
  rw [energy_eq]
  change polygonEnergy M x = polyEnergy F N
    (decode p.val (PolygonChart.chart p.val x.val))
  rw [decode_chart p.val x.val hx']
  rfl

/-- Translate the center to zero before applying the splitting map. -/
def centeredChart : OpenPartialHomeomorph (Short M) (Model n N) :=
  (shortChart M p).trans (Homeomorph.addRight (-base p.val)).toOpenPartialHomeomorph

theorem centeredChart_center_mem : p ∈ (centeredChart M p).source := by
  exact ⟨shortChart_center_mem M p, Set.mem_univ _⟩

theorem centeredChart_center : centeredChart M p p = 0 := by
  change shortChart M p p + -base p.val = 0
  rw [shortChart_center, add_neg_cancel]

theorem centeredChart_energy (x : Short M) (hx : x ∈ (centeredChart M p).source) :
    polygonEnergy M x = PolygonChart.energy F p.val (base p.val + centeredChart M p x) := by
  have h := shortChart_energy M p x hx.1
  change polygonEnergy M x = PolygonChart.energy F p.val
    (base p.val + (shortChart M p x + -base p.val))
  convert h using 1
  abel_nf

/-- The existing analytic splitting lemma now gives a chart on the actual
open short-polygon space, rather than only on its Hilbert coordinates.
The reference polygon is sent to zero and the energy identity holds on the
whole chart source. -/
theorem exists_short_splitting (hne : ∀ i, p.val (i + 1) ≠ p.val i)
    (hc : PolyCritical F N p.val) :
    ∃ (σ : Model n N → Model n N)
      (e : OpenPartialHomeomorph (Short M) (Model n N)),
      ContDiffAt ℝ 2 σ 0 ∧ σ 0 = 0 ∧ p ∈ e.source ∧ e p = 0 ∧
      ∀ x ∈ e.source, polygonEnergy M x =
        PolygonChart.energy F p.val (base p.val + σ (kerProj (hessian F p.val) (e x))) +
          1 / 2 * ⟪hessian F p.val (e x), e x⟫ := by
  obtain ⟨σ, h, hσ, hσ0, hh0, hh, henergy⟩ :=
    PolygonSplitting.exists_homeomorph F M.smooth p.property hne hc
  let e := (centeredChart M p).trans h
  refine ⟨σ, e, hσ, hσ0, ?_, ?_, ?_⟩
  · refine ⟨centeredChart_center_mem M p, ?_⟩
    change centeredChart M p p ∈ h.source
    rw [centeredChart_center]
    exact hh0
  · change h (centeredChart M p p) = 0
    rw [centeredChart_center, hh]
  · intro x hx
    have hf := henergy (centeredChart M p x) hx.2
    rw [centeredChart_energy M p x hx.1, hf.2, ← hf.1]
    rfl

/-- Complete local splitting data for an actual parametrized geodesic. -/
structure GeodesicMorseModel (F : ReversibleMetric n) (g : Geodesics.ClosedGeodesic F)
    (a : ℝ) where
  regular : RegularGeodesicModel F g a
  reduction : Model n regular.data.vertices → Model n regular.data.vertices
  chart : OpenPartialHomeomorph (Short regular.data.model) (Model n regular.data.vertices)
  reduction_smooth : ContDiffAt ℝ 2 reduction 0
  reduction_zero : reduction 0 = 0
  center_mem : regular.data.point ∈ chart.source
  center_zero : chart regular.data.point = 0
  energy_eq : ∀ x ∈ chart.source, polygonEnergy regular.data.model x =
    PolygonChart.energy F regular.data.point.val
      (base regular.data.point.val + reduction (kerProj (hessian F regular.data.point.val) (chart x))) +
      1 / 2 * ⟪hessian F regular.data.point.val (chart x), chart x⟫

/-- Every closed geodesic admits actual local splitting coordinates inside
any strictly larger squared energy cut, including degenerate geodesics.
The reduced function's extremum type is not assumed or concluded. -/
theorem nonempty_geodesicMorseModel (F : ReversibleMetric n)
    (g : Geodesics.ClosedGeodesic F) {a : ℝ}
    (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    Nonempty (GeodesicMorseModel F g a) := by
  obtain ⟨D⟩ := nonempty_regularGeodesicModel F g ha
  obtain ⟨σ, e, hσ, hσ0, hp, he, hE⟩ :=
    exists_short_splitting D.data.model D.data.point D.nonzero_edges D.data.critical
  exact ⟨⟨D, σ, e, hσ, hσ0, hp, he, hE⟩⟩

section DiskToLoops

variable {q : ℕ} (D : MaximalDiskData (polygonEnergy M) p q)

/-- The disk becomes an actual H¹ family by the broken-geodesic map. -/
def diskLoopFamily : C(Disk q, SphereLoop n) :=
  ⟨fun x => broken M (D.family x).val,
    (broken_continuous M).comp (continuous_subtype_val.comp D.family.continuous)⟩

theorem diskLoopFamily_center : diskLoopFamily M p D (center q) = broken M p := by
  change broken M (D.family (center q)).val = broken M p
  rw [D.center_eq]

/-- The coordinate left inverse and sampling recover every disk parameter,
so the family is an actual closed embedding into the strong H¹ loop space. -/
theorem diskLoopFamily_isClosedEmbedding : Topology.IsClosedEmbedding (diskLoopFamily M p D) := by
  apply (diskLoopFamily M p D).continuous.isClosedEmbedding
  intro x y h
  have hs := congrArg (samplePoly N) h
  change samplePoly N (broken M (D.family x).val) = samplePoly N (broken M (D.family y).val) at hs
  rw [sample_broken, sample_broken] at hs
  have hf : D.family x = D.family y := Subtype.ext (Subtype.ext hs)
  exact (D.left_inverse x).symm.trans ((congrArg D.detector hf).trans (D.left_inverse y))

theorem diskLoopFamily_strict_max (x : Disk q) (hx : x ≠ center q) :
    SobolevEnergy.energy F (diskLoopFamily M p D x) < SobolevEnergy.energy F (broken M p) := by
  change SobolevEnergy.energy F (broken M (D.family x).val) < _
  rw [energy_broken_eq, energy_broken_eq]
  exact D.strict_max x hx

include D in
/-- The constructed maximal disk gives a nonzero class in the actual loop
critical pair, with the reference polygon fixed in the conclusion. -/
theorem exists_nonzero_loopClass (hp : polygonEnergy M p < a ^ 2)
    (K : Type) [Field K] :
    ∃ f : TauCeti.diskBoundaryPair q ⟶ loopPair M p,
      TopPair.singularHomologyMap f (ModuleCat.of K K) q (diskClass q K) ≠ 0 := by
  have hmax : ∀ x, x ≠ center q →
      polygonEnergy M (D.family x).val < polygonEnergy M (D.family (center q)).val := by
    simpa only [D.center_eq] using D.strict_max
  have hmin : ∀ x : D.neighborhood, D.detector x = center q →
      polygonEnergy M (D.family (center q)).val ≤ polygonEnergy M x.val := by
    simpa only [D.center_eq] using D.central_min
  have hp' : polygonEnergy M (D.family (center q)).val < a ^ 2 := by
    simpa only [D.center_eq] using hp
  have h : ∃ f : TauCeti.diskBoundaryPair q ⟶ loopPair M (D.family (center q)).val,
      TopPair.singularHomologyMap f (ModuleCat.of K K) q (diskClass q K) ≠ 0 :=
    ⟨localDiskToLoops M D.neighborhood D.family hmax,
      localDiskToLoops_class_ne_zero M D.neighborhood D.family hmax D.isOpen hp'
        D.detector hmin D.left_inverse K⟩
  exact Eq.mp (congrArg (fun x : Short M =>
    ∃ f : TauCeti.diskBoundaryPair q ⟶ loopPair M x,
      TopPair.singularHomologyMap f (ModuleCat.of K K) q (diskClass q K) ≠ 0) D.center_eq) h

end DiskToLoops

/-- A local product normal form on the polygon space suffices for a nonzero
loop class. The small disk, its detector, the neighborhood excision and the
polygon-to-loop injection are all constructed by the preceding theorems. -/
theorem exists_nonzero_loopClass_of_normalForm
    {Z : Type} [TopologicalSpace Z] {q : ℕ} (z₀ : Z)
    (e : OpenPartialHomeomorph (Short M) (EuclideanSpace ℝ (Fin q) × Z))
    (hp : p ∈ e.source) (he : e p = (0, z₀))
    (R : EuclideanSpace ℝ (Fin q) → ℝ) (Q : Z → ℝ)
    (hE : ∀ x ∈ e.source, polygonEnergy M x = R (e x).1 + Q (e x).2)
    (hmax : ∀ᶠ v in 𝓝 (0 : EuclideanSpace ℝ (Fin q)), v ≠ 0 → R v < R 0)
    (hmin : ∀ z, (0, z) ∈ e.target → Q z₀ ≤ Q z)
    (hcut : polygonEnergy M p < a ^ 2) (K : Type) [Field K] :
    ∃ f : TauCeti.diskBoundaryPair q ⟶ loopPair M p,
      TopPair.singularHomologyMap f (ModuleCat.of K K) q (diskClass q K) ≠ 0 := by
  obtain ⟨D⟩ := nonempty_maximalDiskData_of_normalForm (polygonEnergy M) p z₀ e hp he R Q hE hmax hmin
  exact exists_nonzero_loopClass M p D hcut K

end Geodesic

end
end Finsler.SurfaceMorseData
