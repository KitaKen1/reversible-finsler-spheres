module

public import Finsler.Analysis.IntervalChainRule
public import Finsler.Analysis.IntervalH1CurveVariation
public import Finsler.Analysis.SmoothSobolev
public import Finsler.Analysis.IntervalH1GeodesicReadback
public import Finsler.Geometry.PointwiseEuler

/-! Smooth closed geodesics are tangent-critical. For a regular stationary smooth loop
the ambient Euler residual annihilates tangent vectors, so on every periodic H¹
tangent field the first-variation integrand is the derivative of the pairing of the
smooth momentum with the field; the one-dimensional chain rule integrates it to zero by
periodicity. With the readback this characterizes positive-energy tangent-critical
loops as the H¹ embeddings of smooth closed geodesics. -/

@[expose] public section

namespace Finsler.SobolevGeodesicCritical

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.IntervalSobolev
open Finsler.SobolevTangent Finsler.SobolevCurveVariation Finsler.AmbientLagrangian
open Finsler.IntervalChainRule Finsler.SmoothSobolev
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- Time and the continuous representative as one primitive. -/
def timePair (h : Space n) (t : ℝ) : ℝ × Ambient n := (t, continuousRepresentative h t)

/-- Its weak velocity. -/
def timeVel (h : Space n) (t : ℝ) : ℝ × Ambient n := (1, velocity h t)

theorem timeVel_intervalIntegrable (h : Space n) :
    IntervalIntegrable (timeVel h) volume 0 1 := by
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := intervalIntegrable_const
  have hv := velocity_intervalIntegrable h
  exact ⟨hc.1.prodMk hv.1, hc.2.prodMk hv.2⟩

theorem timePair_eq_add_integral (h : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    timePair h t = timePair h 0 + ∫ s in (0 : ℝ)..t, timeVel h s := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (timeVel_intervalIntegrable h).mono_set hsub
  have h1 : (∫ s in (0 : ℝ)..t, timeVel h s).1 = t := by
    have := (ContinuousLinearMap.fst ℝ ℝ (Ambient n)).intervalIntegral_comp_comm hint
    simpa [timeVel] using this.symm
  have h2 : (∫ s in (0 : ℝ)..t, timeVel h s).2 = ∫ s in (0 : ℝ)..t, velocity h s := by
    have := (ContinuousLinearMap.snd ℝ ℝ (Ambient n)).intervalIntegral_comp_comm hint
    simpa [timeVel] using this.symm
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, h1]
    simp [timePair]
  · rw [Prod.snd_add, h2, ← continuousRepresentative_sub h h0 ht]
    simp only [timePair]
    abel

theorem timePair_hasDerivAt_ae (h : Space n) :
    ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), HasDerivAt (timePair h) (timeVel h s) s := by
  have hh := continuousRepresentative_hasDerivAt_ae h
  change ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at hh
  filter_upwards [hh] with s hs
  exact (hasDerivAt_id s).prodMk hs

theorem pairing_contDiff {P : ℝ → Ambient n →L[ℝ] ℝ} (hP : ContDiff ℝ 1 P) :
    ContDiff ℝ 1 (fun z : ℝ × Ambient n => P z.1 z.2) :=
  (hP.comp contDiff_fst).clm_apply contDiff_snd

theorem pairing_fderiv {P : ℝ → Ambient n →L[ℝ] ℝ} (hP : Differentiable ℝ P) (s : ℝ)
    (x y : Ambient n) :
    fderiv ℝ (fun z : ℝ × Ambient n => P z.1 z.2) (s, x) (1, y) = deriv P s x + P s y := by
  have hc : HasFDerivAt (fun z : ℝ × Ambient n => P z.1)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv P s)).comp
        (ContinuousLinearMap.fst ℝ ℝ (Ambient n))) (s, x) :=
    (hP s).hasDerivAt.hasFDerivAt.comp (s, x) hasFDerivAt_fst
  have hu : HasFDerivAt (fun z : ℝ × Ambient n => z.2)
      (ContinuousLinearMap.snd ℝ ℝ (Ambient n)) (s, x) := hasFDerivAt_snd
  rw [(hc.clm_apply hu).fderiv]
  simp [add_comm]

/-- The derivative of the pairing of a C¹ periodic covector with a periodic H¹ field
integrates to zero. -/
theorem pairing_integral_eq_zero {P : ℝ → Ambient n →L[ℝ] ℝ} (hP : ContDiff ℝ 1 P)
    (hper : P 1 = P 0) {h : Space n} (hh : h ∈ periodicSubmodule n) :
    ∫ t, (deriv P t (continuousRepresentative h t) + P t (velocity h t)) ∂intervalMeasure =
      0 := by
  have hc := comp_sub_eq_integral (pairing_contDiff hP) (timeVel_intervalIntegrable h)
    (fun t ht => timePair_eq_add_integral h ht) (timePair_hasDerivAt_ae h)
    (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have hd : Differentiable ℝ P := hP.differentiable (by norm_num)
  have hrep : continuousRepresentative h 1 = continuousRepresentative h 0 :=
    (mem_periodicSubmodule_iff h).mp hh
  simp only [timePair, timeVel, pairing_fderiv hd, hper, hrep, sub_self] at hc
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hc
  exact hc.symm

/-- The full differential of the Lagrangian against a pair, from the momentum identity and
the Euler identity in the position slot. -/
theorem differential_eq_of_momentum (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    {P : ℝ → Ambient n →L[ℝ] ℝ} {t : ℝ} {a b : Ambient n}
    (hvel : velocityDifferential F z = P t) (heul : positionDifferential F z a = deriv P t a) :
    fderiv ℝ (lagrangian F) z (a, b) = deriv P t a + P t b := by
  rw [differential_split, hvel, heul]

/-- Tangent criticality from a jet with a C¹ periodic momentum satisfying the constrained
Euler equation on tangent vectors. -/
theorem tangentCritical_of_momentum (F : ReversibleMetric n) (u : SphereLoop n)
    {j : ℝ → Ambient n × Ambient n} {P : ℝ → Ambient n →L[ℝ] ℝ}
    (hj : weakJet u =ᵐ[intervalMeasure] j) (hP : ContDiff ℝ 1 P) (hper : P 1 = P 0)
    (hrep : ∀ t ∈ Ioo (0 : ℝ) 1, continuousRepresentative (u.data : Space n) t = (j t).1)
    (hvel : ∀ t ∈ Ioo (0 : ℝ) 1, velocityDifferential F (j t) = P t)
    (heul : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ v : Ambient n, ⟪(j t).1, v⟫ = 0 →
      positionDifferential F (j t) v = deriv P t v) :
    TangentCritical F u := by
  apply (tangentCritical_iff F u).mpr
  intro h
  have hh := (mem_tangentSubmodule_iff u (h : Space n)).mp h.property
  have hae : (fun t => fderiv ℝ (lagrangian F) (weakJet u t)
      (continuousRepresentative (h : Space n) t, velocity (h : Space n) t)) =ᵐ[intervalMeasure]
      fun t => deriv P t (continuousRepresentative (h : Space n) t) +
        P t (velocity (h : Space n) t) := by
    filter_upwards [hj, ae_restrict_mem measurableSet_Ioo] with t hjt ht
    have htan : ⟪(j t).1, continuousRepresentative (h : Space n) t⟫ = 0 :=
      (congrArg (fun y => ⟪y, continuousRepresentative (h : Space n) t⟫) (hrep t ht)).symm.trans
        (hh.2 ⟨t, Ioo_subset_Icc_self ht⟩)
    exact (congrArg (fun z => fderiv ℝ (lagrangian F) z
      (continuousRepresentative (h : Space n) t, velocity (h : Space n) t)) hjt).trans
      (differential_eq_of_momentum F (hvel t ht) (heul t ht _ htan))
  have h2 := (integral_congr_ae hae).trans (pairing_integral_eq_zero hP hper hh.1)
  exact (tangentVariationL_apply F u h).symm.trans
    ((tangentVariationL_eq_full_differential F u h).trans h2)

/-- The H¹ embedding of a regular stationary smooth loop is tangent-critical. -/
theorem tangentCritical_ofSmooth (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Finsler.Geodesics.Regular γ) (hstat : Finsler.Geodesics.Stationary F γ) :
    TangentCritical F (ofSmooth γ) := by
  have hE := Finsler.PointwiseEuler.stationary_constrainedEuler F hreg hstat
  refine tangentCritical_of_momentum F (ofSmooth γ) (weakJet_ofSmooth_ae γ)
    ((Finsler.WeakEulerLagrange.momentum_smooth F hreg).of_le (by norm_num)) ?_ ?_ ?_ ?_
  · simpa using Finsler.WeakEulerLagrange.momentum_periodic F γ 0
  · intro t ht
    rw [Finsler.EnergyConservation.loopJet_eq]
    exact representative_graphData γ (Ioo_subset_Icc_self ht)
  · intro t _
    rfl
  · intro t _ v hv
    have hv' : ⟪(γ t : Ambient n), v⟫ = 0 := by
      rw [Finsler.EnergyConservation.loopJet_eq] at hv
      exact hv
    have h0 := hE t v hv'
    simp only [Finsler.WeakEulerLagrange.residual, sub_apply,
      sub_eq_zero] at h0
    exact h0

/-- Every smooth closed geodesic is a tangent-critical actual H¹ sphere loop. -/
theorem tangentCritical_of_closedGeodesic (F : ReversibleMetric n)
    (g : Finsler.Geodesics.ClosedGeodesic F) : TangentCritical F (ofSmooth g.loop) :=
  tangentCritical_ofSmooth F g.regular g.stationary

/-- Positive-energy tangent-critical actual H¹ sphere loops are exactly the H¹ embeddings
of smooth closed geodesics. -/
theorem tangentCritical_iff_closedGeodesic (F : ReversibleMetric n) (u : SphereLoop n)
    (hE : 0 < Finsler.SobolevEnergy.energy F u) :
    TangentCritical F u ↔ ∃ g : Finsler.Geodesics.ClosedGeodesic F, ofSmooth g.loop = u := by
  constructor
  · intro hc
    obtain ⟨g, hg⟩ :=
      Finsler.SobolevGeodesicReadback.exists_closedGeodesic_of_tangentCritical F u hc hE
    refine ⟨g, Finsler.SobolevEnergy.sphereLoop_eq_of_representative_eq fun t => ?_⟩
    rw [sphereRepresentative_ofSmooth]
    apply Subtype.ext
    change ((g.loop t : Sphere n) : Ambient n) = continuousRepresentative (u.data : Space n) t
    rw [hg t]
    exact Finsler.SobolevCircleRepresentative.realMap_eqOn u.data t.property
  · rintro ⟨g, rfl⟩
    exact tangentCritical_of_closedGeodesic F g

end

end Finsler.SobolevGeodesicCritical
