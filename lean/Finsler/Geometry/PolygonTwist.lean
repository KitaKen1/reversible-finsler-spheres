module

public import Finsler.Geometry.TwistCondition
public import Finsler.Geometry.PolygonNullity

/-! The twist condition for short polygons, and the uniform bound for the nullity. The pair
energy of two nearby distinct sphere points, in the charts centred at the two points, is the
joint energy of a chart package composed with the transition maps of the charts. The transition
maps have injective derivatives (the reverse transitions are left inverses), so the twist
condition of the joint energy passes to the pair energy. With the segment atlas this gives a
positive radius below which every polygon without zero edges satisfies the twist condition, and
hence has nullity at most 2 n in every number of vertices. -/

@[expose] public section

namespace Finsler.PolygonTwist

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.SphereCoordinateEuler Finsler.AmbientEnergyRegularity Finsler.AmbientCalibrator
open Finsler.SegmentAtlas Finsler.EnergySphereSmooth Finsler.SegmentMomentum
open Finsler.SegmentContinuity Finsler.EnergyMomentum Finsler.TwistCondition
open Finsler.EulerCovariance Finsler.EikonalChart Finsler.CoordinateExpInverse
open Finsler.EnergyJointSmooth
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n}

/-- The centre of the chart at a sphere point. -/
def ctr (X : Sphere n) : Coordinates n := extChartAt (𝓡 n) X X

theorem inverseAmbient_ctr (X : Sphere n) : inverseAmbient X (ctr X) = X :=
  congrArg Subtype.val ((extChartAt (𝓡 n) X).left_inv (mem_extChartAt_source X))

theorem inverseSphere_ctr (X : Sphere n) : inverseSphere X (ctr X) = X :=
  (extChartAt (𝓡 n) X).left_inv (mem_extChartAt_source X)

theorem ctr_mem_target (X : Sphere n) : ctr X ∈ (extChartAt (𝓡 n) X).target :=
  (extChartAt (𝓡 n) X).map_source (mem_extChartAt_source X)

/-- The transition from the chart centred at X to the chart of a package. -/
def trans (S : SegChart F) (X : Sphere n) (u : Coordinates n) : Coordinates n :=
  chartNormalize S.p (inverseAmbient X u)

theorem trans_ctr (S : SegChart F) (X : Sphere n) :
    trans S X (ctr X) = chartNormalize S.p (X : Ambient n) := by
  rw [trans, inverseAmbient_ctr]

theorem trans_contDiffAt (S : SegChart F) {X : Sphere n}
    (hX : X ∈ (extChartAt (𝓡 n) S.p).source) : ContDiffAt ℝ ∞ (trans S X) (ctr X) := by
  have h1 := inverseAmbient_smoothAt X (ctr_mem_target X)
  have h2 : ContDiffAt ℝ ∞ (chartNormalize S.p) (inverseAmbient X (ctr X)) := by
    rw [inverseAmbient_ctr]
    exact chartNormalize_smoothAt S.p (sphere_ne_zero X) (by rw [normalize_inclusion]; exact hX)
  exact ContDiffAt.comp (g := chartNormalize S.p) (f := inverseAmbient X) (ctr X) h2 h1

/-- The derivative of the transition map at the centre is injective. -/
theorem trans_fderiv_injective (S : SegChart F) {X : Sphere n}
    (hX : X ∈ (extChartAt (𝓡 n) S.p).source) :
    Function.Injective (fderiv ℝ (trans S X) (ctr X)) := by
  have hzt : chartNormalize S.p (X : Ambient n) ∈ (extChartAt (𝓡 n) S.p).target :=
    chartNormalize_mem_target S.p (by rw [normalize_inclusion]; exact hX)
  have hbackd : DifferentiableAt ℝ (fun w => chartNormalize X (inverseAmbient S.p w))
      (trans S X (ctr X)) := by
    rw [trans_ctr]
    have h1 := inverseAmbient_smoothAt S.p hzt
    have h2 : ContDiffAt ℝ ∞ (chartNormalize X)
        (inverseAmbient S.p (chartNormalize S.p (X : Ambient n))) := by
      rw [inverseAmbient_chartNormalize hX]
      exact chartNormalize_smoothAt X (sphere_ne_zero X)
        (by rw [normalize_inclusion]; exact mem_extChartAt_source X)
    exact (ContDiffAt.comp (g := chartNormalize X) (f := inverseAmbient S.p)
      (chartNormalize S.p (X : Ambient n)) h2 h1).differentiableAt (by simp)
  have hid : (fun u => chartNormalize X (inverseAmbient S.p (trans S X u))) =ᶠ[𝓝 (ctr X)]
      fun u => u := by
    have h1 : ∀ᶠ u in 𝓝 (ctr X), u ∈ (extChartAt (𝓡 n) X).target :=
      (isOpen_extChartAt_target X).mem_nhds (ctr_mem_target X)
    have h2 : ∀ᶠ u in 𝓝 (ctr X), inverseSphere X u ∈ (extChartAt (𝓡 n) S.p).source := by
      have hc : ContinuousAt (inverseSphere X) (ctr X) :=
        (inverseSphere_smoothAt X (ctr_mem_target X)).continuousAt
      refine hc.eventually ((isOpen_extChartAt_source S.p).mem_nhds ?_)
      rw [inverseSphere_ctr]
      exact hX
    filter_upwards [h1, h2] with u hu1 hu2
    change chartNormalize X (inverseAmbient S.p
      (chartNormalize S.p ((inverseSphere X u : Sphere n) : Ambient n))) = u
    rw [inverseAmbient_chartNormalize hu2]
    exact chartNormalize_inverseAmbient hu1
  have hφd : DifferentiableAt ℝ (trans S X) (ctr X) :=
    (trans_contDiffAt S hX).differentiableAt (by simp)
  have hcomp := hbackd.hasFDerivAt.comp (ctr X) hφd.hasFDerivAt
  have h1 := hcomp.unique ((hasFDerivAt_id (ctr X)).congr_of_eventuallyEq hid)
  intro a b hab
  have ha : fderiv ℝ (fun w => chartNormalize X (inverseAmbient S.p w)) (trans S X (ctr X))
      (fderiv ℝ (trans S X) (ctr X) a) = a :=
    congrArg (fun L : Coordinates n →L[ℝ] Coordinates n => L a) h1
  have hb : fderiv ℝ (fun w => chartNormalize X (inverseAmbient S.p w)) (trans S X (ctr X))
      (fderiv ℝ (trans S X) (ctr X) b) = b :=
    congrArg (fun L : Coordinates n →L[ℝ] Coordinates n => L b) h1
  rw [← ha, ← hb, hab]

/-- The energy of the segment between two sphere points, in the charts centred at them. -/
def pairEnergy (F : ReversibleMetric n) (P Q : Sphere n)
    (x : Coordinates n × Coordinates n) : ℝ :=
  ambientMinEnergy F (inverseAmbient P x.1, inverseAmbient Q x.2)

/-- Near the centres the pair energy is the joint energy of a chart package in the transition
coordinates. -/
theorem pairEnergy_eventually_eq (S : SegChart F) {P Q : Sphere n} (hP : P ∈ segDom S)
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) :
    pairEnergy F P Q =ᶠ[𝓝 (ctr P, ctr Q)]
      fun x => jointEnergy S.D (trans S P x.1, trans S Q x.2) := by
  have hc : ContinuousAt (fun x : Coordinates n × Coordinates n =>
      (inverseAmbient P x.1, inverseAmbient Q x.2)) (ctr P, ctr Q) :=
    (ContinuousAt.comp (g := inverseAmbient P)
      (f := fun x : Coordinates n × Coordinates n => x.1) (x := (ctr P, ctr Q))
      (inverseAmbient_smoothAt P (ctr_mem_target P)).continuousAt continuousAt_fst).prodMk
      (ContinuousAt.comp (g := inverseAmbient Q)
        (f := fun x : Coordinates n × Coordinates n => x.2) (x := (ctr P, ctr Q))
        (inverseAmbient_smoothAt Q (ctr_mem_target Q)).continuousAt continuousAt_snd)
  have ht : Tendsto (fun x : Coordinates n × Coordinates n =>
      (inverseAmbient P x.1, inverseAmbient Q x.2)) (𝓝 (ctr P, ctr Q))
      (𝓝 ((P : Ambient n), (Q : Ambient n))) := by
    have h := hc.tendsto
    rwa [inverseAmbient_ctr, inverseAmbient_ctr] at h
  exact ht.eventually (ambientMinEnergy_eventually_eq S hP hQ)

/-- **The twist condition for the pair energy** of two nearby distinct sphere points, in the
charts centred at the points. -/
theorem pair_twist (S : SegChart F) {P Q : Sphere n} (hP : P ∈ segDom S)
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) (hne : Q ≠ P) {v : Coordinates n}
    (h : ∀ η : Coordinates n,
      fderiv ℝ (fun x => fderiv ℝ (pairEnergy F P Q) x (η, 0)) (ctr P, ctr Q) (0, v) = 0) :
    v = 0 := by
  have hPs : P ∈ (extChartAt (𝓡 n) S.p).source := hP.1
  obtain ⟨-, hQs, -⟩ := good_of_dom S hP (hQ.trans_le S.hδη)
  have hQs' : Q ∈ (extChartAt (𝓡 n) S.p).source := by rwa [normalize_inclusion] at hQs
  -- the base pair in the chart of the package
  obtain ⟨y, hydef⟩ : ∃ y, y = extChartAt (𝓡 n) S.p P := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z, z = chartNormalize S.p (Q : Ambient n) := ⟨_, rfl⟩
  have hφ0 : trans S P (ctr P) = y := by rw [trans_ctr, chartNormalize_sphere S P, hydef]
  have hψ0 : trans S Q (ctr Q) = z := by rw [trans_ctr, hzdef]
  have hy : y ∈ ball S.y₀ S.r := by
    rw [hydef]
    exact ball_subset_ball S.hr'r hP.2
  have hyt : y ∈ (extChartAt (𝓡 n) S.p).target := S.hball (ball_subset_closedBall hy)
  have hz : ‖z - y‖ < S.D.ρ / 2 := by
    rw [hydef, hzdef]
    exact chart_dist_lt S hP hQ
  have hzy : z ≠ y := by
    intro hh
    apply hne
    have hQz : inverseAmbient S.p (chartNormalize S.p (Q : Ambient n)) = Q :=
      inverseAmbient_chartNormalize hQs'
    have hPz : inverseAmbient S.p (extChartAt (𝓡 n) S.p P) = P :=
      inverseAmbient_chart_of_dom S hP
    apply Subtype.ext
    rw [← hQz, ← hPz, ← hzdef, ← hydef, hh]
  have hJ3 : ContDiffAt ℝ 3 (jointEnergy S.D) (y, z) :=
    energy_contDiffAt_joint S.D hy hz hzy hyt
  have hφs := trans_contDiffAt S hPs
  have hψs := trans_contDiffAt S hQs'
  have hφd : DifferentiableAt ℝ (trans S P) (ctr P) := hφs.differentiableAt (by simp)
  have hψd : DifferentiableAt ℝ (trans S Q) (ctr Q) := hψs.differentiableAt (by simp)
  -- the composite and its regularity
  have hpair : ContDiffAt ℝ 3 (fun x : Coordinates n × Coordinates n =>
      (trans S P x.1, trans S Q x.2)) (ctr P, ctr Q) :=
    (ContDiffAt.comp (g := trans S P) (f := fun x : Coordinates n × Coordinates n => x.1)
      (ctr P, ctr Q) (hφs.of_le (by simp)) contDiffAt_fst).prodMk
      (ContDiffAt.comp (g := trans S Q) (f := fun x : Coordinates n × Coordinates n => x.2)
        (ctr P, ctr Q) (hψs.of_le (by simp)) contDiffAt_snd)
  have hJ3' : ContDiffAt ℝ 3 (jointEnergy S.D) (trans S P (ctr P), trans S Q (ctr Q)) := by
    rw [hφ0, hψ0]
    exact hJ3
  have hC3 : ContDiffAt ℝ 3 (fun x : Coordinates n × Coordinates n =>
      jointEnergy S.D (trans S P x.1, trans S Q x.2)) (ctr P, ctr Q) :=
    ContDiffAt.comp (g := jointEnergy S.D)
      (f := fun x : Coordinates n × Coordinates n => (trans S P x.1, trans S Q x.2))
      (ctr P, ctr Q) hJ3' hpair
  have hev := pairEnergy_eventually_eq S hP hQ
  have hE3 : ContDiffAt ℝ 3 (pairEnergy F P Q) (ctr P, ctr Q) := hC3.congr_of_eventuallyEq hev
  -- step 1: the derivative in the first variable near the base pair
  have hd1 : ∀ᶠ x in 𝓝 (ctr P, ctr Q), DifferentiableAt ℝ (trans S P) x.1 :=
    continuousAt_fst.eventually
      (((hφs.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono
        fun u hu => hu.differentiableAt (by simp))
  have hd2 : ∀ᶠ x in 𝓝 (ctr P, ctr Q), DifferentiableAt ℝ (trans S Q) x.2 :=
    continuousAt_snd.eventually
      (((hψs.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by simp)).mono
        fun u hu => hu.differentiableAt (by simp))
  have hd3 : ∀ᶠ x in 𝓝 (ctr P, ctr Q),
      DifferentiableAt ℝ (jointEnergy S.D) (trans S P x.1, trans S Q x.2) := by
    have ht : Tendsto (fun x : Coordinates n × Coordinates n =>
        (trans S P x.1, trans S Q x.2)) (𝓝 (ctr P, ctr Q)) (𝓝 (y, z)) := by
      have h' := hpair.continuousAt.tendsto
      rwa [hφ0, hψ0] at h'
    exact ht.eventually ((hJ3.eventually (by simp)).mono fun w hw =>
      hw.differentiableAt (by simp))
  have hstep1 : ∀ η : Coordinates n, ∀ᶠ x in 𝓝 (ctr P, ctr Q),
      fderiv ℝ (pairEnergy F P Q) x (η, 0) =
        fderiv ℝ (jointEnergy S.D) (trans S P x.1, trans S Q x.2)
          (fderiv ℝ (trans S P) x.1 η, 0) := by
    intro η
    filter_upwards [hev.eventually_nhds, hd1, hd2, hd3] with x hx h1 h2 h3
    rw [Filter.EventuallyEq.fderiv_eq hx]
    have hΦ : HasFDerivAt (fun x : Coordinates n × Coordinates n =>
        (trans S P x.1, trans S Q x.2))
        ((fderiv ℝ (trans S P) x.1).prodMap (fderiv ℝ (trans S Q) x.2)) x :=
      HasFDerivAt.prodMap x h1.hasFDerivAt h2.hasFDerivAt
    have hc : HasFDerivAt (fun x : Coordinates n × Coordinates n =>
        jointEnergy S.D (trans S P x.1, trans S Q x.2))
        ((fderiv ℝ (jointEnergy S.D) (trans S P x.1, trans S Q x.2)).comp
          ((fderiv ℝ (trans S P) x.1).prodMap (fderiv ℝ (trans S Q) x.2))) x :=
      HasFDerivAt.comp (g := jointEnergy S.D)
        (f := fun x : Coordinates n × Coordinates n => (trans S P x.1, trans S Q x.2)) x
        h3.hasFDerivAt hΦ
    rw [hc.fderiv]
    change fderiv ℝ (jointEnergy S.D) (trans S P x.1, trans S Q x.2)
      (fderiv ℝ (trans S P) x.1 η, fderiv ℝ (trans S Q) x.2 0) = _
    rw [map_zero]
  -- steps 2 and 3: the mixed second derivative in the chart of the package
  have hstep3 : ∀ η : Coordinates n,
      fderiv ℝ (fun z' => fderiv ℝ (jointEnergy S.D) (y, z') (fderiv ℝ (trans S P) (ctr P) η, 0))
        z (fderiv ℝ (trans S Q) (ctr Q) v) = 0 := by
    intro η
    have hslice : ContinuousAt (fun v' : Coordinates n => (ctr P, v')) (ctr Q) :=
      (Continuous.prodMk_right (ctr P)).continuousAt
    have hAB : (fun v' => fderiv ℝ (pairEnergy F P Q) (ctr P, v') (η, 0)) =ᶠ[𝓝 (ctr Q)]
        fun v' => fderiv ℝ (jointEnergy S.D) (y, trans S Q v')
          (fderiv ℝ (trans S P) (ctr P) η, 0) := by
      filter_upwards [hslice.eventually (hstep1 η)] with v' hv'
      rw [hv', hφ0]
    have hG : DifferentiableAt ℝ (fun x => fderiv ℝ (pairEnergy F P Q) x (η, 0))
        (ctr P, ctr Q) :=
      (ContinuousLinearMap.apply ℝ ℝ ((η, 0) : Coordinates n × Coordinates n)).differentiableAt.comp
        _ ((hE3.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
    have hA : HasFDerivAt (fun v' => fderiv ℝ (pairEnergy F P Q) (ctr P, v') (η, 0))
        ((fderiv ℝ (fun x => fderiv ℝ (pairEnergy F P Q) x (η, 0)) (ctr P, ctr Q)).comp
          (ContinuousLinearMap.inr ℝ (Coordinates n) (Coordinates n))) (ctr Q) :=
      hG.hasFDerivAt.comp (ctr Q) (hasFDerivAt_prodMk_right (ctr P) (ctr Q))
    have hK0 : DifferentiableAt ℝ (fun w => fderiv ℝ (jointEnergy S.D) w
        (fderiv ℝ (trans S P) (ctr P) η, 0)) (y, z) :=
      (ContinuousLinearMap.apply ℝ ℝ
        ((fderiv ℝ (trans S P) (ctr P) η, 0) : Coordinates n × Coordinates n)).differentiableAt.comp
        _ ((hJ3.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num))
    have hK : HasFDerivAt (fun z' => fderiv ℝ (jointEnergy S.D) (y, z')
        (fderiv ℝ (trans S P) (ctr P) η, 0))
        (fderiv ℝ (fun z' => fderiv ℝ (jointEnergy S.D) (y, z')
          (fderiv ℝ (trans S P) (ctr P) η, 0)) z) (trans S Q (ctr Q)) := by
      rw [hψ0]
      exact (hK0.comp z (hasFDerivAt_prodMk_right y z).differentiableAt).hasFDerivAt
    have hB : HasFDerivAt (fun v' => fderiv ℝ (jointEnergy S.D) (y, trans S Q v')
        (fderiv ℝ (trans S P) (ctr P) η, 0))
        ((fderiv ℝ (fun z' => fderiv ℝ (jointEnergy S.D) (y, z')
          (fderiv ℝ (trans S P) (ctr P) η, 0)) z).comp (fderiv ℝ (trans S Q) (ctr Q)))
        (ctr Q) :=
      HasFDerivAt.comp (g := fun z' => fderiv ℝ (jointEnergy S.D) (y, z')
        (fderiv ℝ (trans S P) (ctr P) η, 0)) (f := trans S Q) (ctr Q) hK hψd.hasFDerivAt
    have hval := h η
    have hAv : fderiv ℝ (fun v' => fderiv ℝ (pairEnergy F P Q) (ctr P, v') (η, 0)) (ctr Q) v =
        0 := by
      rw [hA.fderiv]
      exact hval
    rw [hAB.fderiv_eq, hB.fderiv] at hAv
    exact hAv
  -- step 4: the transition maps are local diffeomorphisms
  have hsurj : Function.Surjective (fderiv ℝ (trans S P) (ctr P)) :=
    LinearMap.injective_iff_surjective.mp (trans_fderiv_injective S hPs)
  have hzero : fderiv ℝ (trans S Q) (ctr Q) v = 0 :=
    joint_twist S.D hy hyt hz hzy fun η' => by
      obtain ⟨η, rfl⟩ := hsurj η'
      exact hstep3 η
  exact trans_fderiv_injective S hQs' (hzero.trans (map_zero _).symm)

/-- There is a positive radius below which every polygon without zero edges satisfies the twist
condition. -/
theorem exists_twist (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), PolygonLoop.ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) → PolygonNullity.Twist F q := by
  obtain ⟨δ, hδ, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  refine ⟨δ, hδ, fun N _ q hq hne j v hv => ?_⟩
  obtain ⟨P₀, hP₀, hP⟩ := hcover (q j)
  exact pair_twist (S P₀) hP ((hq j).trans_le (hδS P₀ hP₀)) (hne j) hv

/-- **A uniform bound for the nullity.** There is a positive radius below which every polygon
without zero edges, with any number of vertices, has nullity at most 2 n. -/
theorem exists_nullity_le (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), PolygonLoop.ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) → PolygonHessian.nullity F q ≤ 2 * n := by
  obtain ⟨δ₁, hδ₁, htw⟩ := exists_twist F
  obtain ⟨δ₂, hδ₂, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun N _ q hq hne => ?_⟩
  have hq₁ : PolygonLoop.ShortPolygon δ₁ q := fun i => (hq i).trans_le (min_le_left _ _)
  have hq₂ : PolygonLoop.ShortPolygon δ₂ q := fun i => (hq i).trans_le (min_le_right _ _)
  exact PolygonNullity.nullity_le F hs hq₂ hne (htw N q hq₁ hne)

end

end Finsler.PolygonTwist
