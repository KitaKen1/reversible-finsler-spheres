module

public import Finsler.Analysis.EulerCovariance
public import Finsler.Geometry.EnergyConservation
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! The usual local-coordinate Euler--Lagrange equation of the actual F²
energy on the standard sphere. Every chart in the actual sphere atlas is
tested where it is defined. The coordinate Lagrangian uses the genuine
derivative of its inverse. H¹ critical-point regularity is separate. -/

@[expose] public section

namespace Finsler.SphereCoordinateEuler

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.AmbientLagrangian Finsler.SphereRetraction Function Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace

noncomputable section

variable {n : ℕ}

abbrev Coordinates (n : ℕ) := EuclideanSpace ℝ (Fin n)

def inverseSphere (p : Sphere n) (y : Coordinates n) : Sphere n :=
  (extChartAt (𝓡 n) p).symm y

def inverseAmbient (p : Sphere n) (y : Coordinates n) : Ambient n :=
  (inverseSphere p y : Ambient n)

def coordinateCurve (p : Sphere n) (γ : SmoothLoop n) (t : ℝ) : Coordinates n :=
  extChartAt (𝓡 n) p (γ t)

theorem inverseSphere_smoothAt (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    ContMDiffAt 𝓘(ℝ, Coordinates n) (𝓡 n) ∞ (inverseSphere p) y := by
  have h := contMDiffWithinAt_extChartAt_symm_range (I := 𝓡 n) (n := ∞) p hy
  rw [show Set.range (𝓡 n) = Set.univ by simp, contMDiffWithinAt_univ] at h
  exact h

theorem inverseAmbient_smoothAt (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    ContDiffAt ℝ ∞ (inverseAmbient p) y :=
  ((inclusion_smooth n).contMDiffAt.comp y (inverseSphere_smoothAt p hy)).contDiffAt

theorem coordinateCurve_smoothAt (p : Sphere n) (γ : SmoothLoop n) {t : ℝ}
    (ht : γ t ∈ (extChartAt (𝓡 n) p).source) :
    ContDiffAt ℝ ∞ (coordinateCurve p γ) t := by
  have hs : γ t ∈ (chartAt (Coordinates n) p).source := by
    simpa only [extChartAt_source] using ht
  exact ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hs).comp t γ.smooth.contMDiffAt).contDiffAt

theorem inverseSphere_coordinateCurve (p : Sphere n) (γ : SmoothLoop n) {t : ℝ}
    (ht : γ t ∈ (extChartAt (𝓡 n) p).source) :
    inverseSphere p (coordinateCurve p γ t) = γ t :=
  (extChartAt (𝓡 n) p).left_inv ht

theorem inverseAmbient_coordinateCurve_eventually (p : Sphere n) (γ : SmoothLoop n) {t : ℝ}
    (ht : γ t ∈ (extChartAt (𝓡 n) p).source) :
    inverseAmbient p ∘ coordinateCurve p γ =ᶠ[𝓝 t] Finsler.EnergyConservation.position γ := by
  have h := γ.smooth.continuous.continuousAt.preimage_mem_nhds
    (extChartAt_source_mem_nhds' (I := 𝓡 n) ht)
  filter_upwards [h] with u hu
  exact congrArg Subtype.val (inverseSphere_coordinateCurve p γ hu)

theorem inverseAmbient_fderiv (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    fderiv ℝ (inverseAmbient p) y = (ambientMap (inverseSphere p y)).comp
      (mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y) := by
  have h := mvfderiv_comp y ((inclusion_smooth n).mdifferentiableAt (by simp))
    ((inverseSphere_smoothAt p hy).mdifferentiableAt (by simp))
  rw [mvfderiv_eq_fderiv] at h
  apply ContinuousLinearMap.ext
  intro a
  have ha := congrArg (fun D : TangentSpace 𝓘(ℝ, Coordinates n) y →L[ℝ] Ambient n => D a) h
  change fderiv ℝ (inverseAmbient p) y a = ambientMap (inverseSphere p y)
    (mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y a) at ha
  exact ha

theorem inverseAmbient_jet (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) (w : Coordinates n) :
    Finsler.EulerCovariance.jetMap (inverseAmbient p) (y, w) =
      ambientPair ⟨inverseSphere p y,
        mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y w⟩ := by
  rw [Finsler.EulerCovariance.jetMap, inverseAmbient_fderiv p hy]
  rfl

def coordinateLagrangian (F : ReversibleMetric n) (p : Sphere n) :
    Coordinates n × Coordinates n → ℝ :=
  Finsler.EulerCovariance.pullback (lagrangian F) (inverseAmbient p)

theorem coordinateLagrangian_eq (F : ReversibleMetric n) (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) (w : Coordinates n) :
    coordinateLagrangian F p (y, w) =
      F.value ⟨inverseSphere p y,
        mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y w⟩ ^ 2 := by
  rw [coordinateLagrangian, Finsler.EulerCovariance.pullback, comp_apply,
    inverseAmbient_jet p hy w, lagrangian_ambientPair]

theorem inverseAmbient_fderiv_self (p : Sphere n) :
    fderiv ℝ (inverseAmbient p) (extChartAt (𝓡 n) p p) = ambientMap p := by
  rw [inverseAmbient_fderiv p ((extChartAt (𝓡 n) p).map_source (mem_extChartAt_source p))]
  have hi : inverseSphere p (extChartAt (𝓡 n) p p) = p :=
    (extChartAt (𝓡 n) p).left_inv (mem_extChartAt_source p)
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := p)
  have hd' : mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p)
      (extChartAt (𝓡 n) p p) = ContinuousLinearMap.id ℝ (Coordinates n) := by
    rw [show Set.range (𝓡 n) = Set.univ by simp, mfderivWithin_univ] at hd
    exact hd
  rw [hd']
  apply ContinuousLinearMap.ext
  intro a
  change ambientMap (inverseSphere p (extChartAt (𝓡 n) p p)) a = ambientMap p a
  rw [hi]

theorem loopJet_eq_curveJet (γ : SmoothLoop n) (t : ℝ) :
    loopJet γ t = Finsler.EulerCovariance.curveJet (Finsler.EnergyConservation.position γ) t := by
  rw [Finsler.EnergyConservation.loopJet_eq, Finsler.EnergyConservation.velocity_eq_deriv]
  rfl

theorem inverseAmbient_fderiv_tangent (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) (a : Coordinates n) :
    ⟪(inverseSphere p y : Ambient n), fderiv ℝ (inverseAmbient p) y a⟫ = 0 := by
  rw [inverseAmbient_fderiv p hy]
  change ⟪(inverseSphere p y : Ambient n), ambientMap (inverseSphere p y)
    (mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y a)⟫ = 0
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← ambientMap_range]
  exact ⟨_, rfl⟩

theorem ambient_residual_eq (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) :
    Finsler.EulerCovariance.residual (lagrangian F) (Finsler.EnergyConservation.position γ) t =
      Finsler.WeakEulerLagrange.residual F γ t := by
  have hm : Finsler.EulerCovariance.momentum (lagrangian F)
      (Finsler.EnergyConservation.position γ) = Finsler.WeakEulerLagrange.momentum F γ := by
    funext u
    rw [Finsler.EulerCovariance.momentum, ← loopJet_eq_curveJet γ u]
    rfl
  rw [Finsler.EulerCovariance.residual, hm, ← loopJet_eq_curveJet γ t]
  rfl

def coordinateResidual (F : ReversibleMetric n) (p : Sphere n) (γ : SmoothLoop n)
    (t : ℝ) : Coordinates n →L[ℝ] ℝ :=
  Finsler.EulerCovariance.residual (coordinateLagrangian F p) (coordinateCurve p γ) t

theorem coordinate_residual_eq (F : ReversibleMetric n) (p : Sphere n) (γ : SmoothLoop n)
    (hreg : Regular γ) {t : ℝ} (ht : γ t ∈ (extChartAt (𝓡 n) p).source) :
    coordinateResidual F p γ t = (Finsler.WeakEulerLagrange.residual F γ t).comp
      (fderiv ℝ (inverseAmbient p) (coordinateCurve p γ t)) := by
  have hy := (extChartAt (𝓡 n) p).map_source ht
  have hφ := (inverseAmbient_smoothAt p hy).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hx := (coordinateCurve_smoothAt p γ ht).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have he := inverseAmbient_coordinateCurve_eventually p γ ht
  have hj : Finsler.EulerCovariance.jetMap (inverseAmbient p)
      (Finsler.EulerCovariance.curveJet (coordinateCurve p γ) t) = loopJet γ t := by
    rw [Finsler.EulerCovariance.jetMap_curveJet (hφ.differentiableAt (by norm_num))
      (hx.differentiableAt (by norm_num)),
      (Finsler.EulerCovariance.curveJet_congr_eventually he).eq_of_nhds]
    exact (loopJet_eq_curveJet γ t).symm
  have hL : ContDiffAt ℝ 2 (lagrangian F)
      (Finsler.EulerCovariance.jetMap (inverseAmbient p)
        (Finsler.EulerCovariance.curveJet (coordinateCurve p γ) t)) := by
    rw [hj]
    exact (lagrangian_smoothAt F (loopJet_mem_slitDomain γ hreg t)).of_le (by simp)
  have h := Finsler.EulerCovariance.residual_pullback hφ hx hL
  rw [Finsler.EulerCovariance.residual_congr_eventually (lagrangian F) he,
    ambient_residual_eq F γ t] at h
  exact h

/-- The actual Euler--Lagrange equation in every standard sphere chart where
the loop lies in the chart source. The Lagrangian is the actual F² density. -/
def CoordinateEuler (F : ReversibleMetric n) (γ : SmoothLoop n) : Prop :=
  ∀ (p : Sphere n) (t : ℝ), γ t ∈ (extChartAt (𝓡 n) p).source →
    coordinateResidual F p γ t = 0

theorem constrainedEuler_coordinateEuler (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (he : Finsler.PointwiseEuler.ConstrainedEuler F γ) :
    CoordinateEuler F γ := by
  intro p t ht
  rw [coordinate_residual_eq F p γ hreg ht]
  ext a
  change Finsler.WeakEulerLagrange.residual F γ t
    (fderiv ℝ (inverseAmbient p) (coordinateCurve p γ t) a) = 0
  apply he t _
  have h := inverseAmbient_fderiv_tangent p ((extChartAt (𝓡 n) p).map_source ht) a
  change ⟪(inverseSphere p (coordinateCurve p γ t) : Ambient n),
    fderiv ℝ (inverseAmbient p) (coordinateCurve p γ t) a⟫ = 0 at h
  rwa [inverseSphere_coordinateCurve p γ ht] at h

theorem coordinateEuler_constrainedEuler (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (he : CoordinateEuler F γ) :
    Finsler.PointwiseEuler.ConstrainedEuler F γ := by
  intro t v hv
  have h := he (γ t) t (mem_extChartAt_source (γ t))
  rw [coordinate_residual_eq F (γ t) γ hreg (mem_extChartAt_source (γ t))] at h
  change (Finsler.WeakEulerLagrange.residual F γ t).comp
    (fderiv ℝ (inverseAmbient (γ t)) (extChartAt (𝓡 n) (γ t) (γ t))) = 0 at h
  rw [inverseAmbient_fderiv_self] at h
  have hm : v ∈ (ambientMap (γ t)).range := by
    rw [ambientMap_range]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
  obtain ⟨w, hw⟩ := hm
  have hz := congrArg (fun R : Coordinates n →L[ℝ] ℝ => R w) h
  change Finsler.WeakEulerLagrange.residual F γ t (ambientMap (γ t) w) = 0 at hz
  exact (congrArg (fun z : Ambient n => Finsler.WeakEulerLagrange.residual F γ t z) hw).symm.trans hz

theorem coordinateEuler_iff_constrainedEuler (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) : CoordinateEuler F γ ↔ Finsler.PointwiseEuler.ConstrainedEuler F γ :=
  ⟨coordinateEuler_constrainedEuler F hreg, constrainedEuler_coordinateEuler F hreg⟩

theorem stationary_iff_coordinateEuler (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) : Stationary F γ ↔ CoordinateEuler F γ :=
  (Finsler.GeneralVariation.stationary_iff_constrainedEuler F hreg).trans
    (coordinateEuler_iff_constrainedEuler F hreg).symm

end

end Finsler.SphereCoordinateEuler
