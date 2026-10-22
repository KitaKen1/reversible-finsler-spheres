module

public import Finsler.Analysis.IntervalH1ZeroExclusion
public import Finsler.Geometry.FiberLegendre

/-! C¹ regularity of actual tangent-critical H¹ sphere loops.
The tangent Legendre map z ↦ (z.1, tangent part of D_vL(z)) is continuous and
injective on the compact set of unit positions with bounded tangent velocity.
A continuous injection from a compact space is a closed embedding, so its
inverse is continuous on the range. The recovered covector is continuous and
equals the Legendre image of the weak jet almost everywhere; a continuous
distance function vanishing almost everywhere places the whole path in the
range. The inverse then gives a continuous periodic representative of the weak
velocity, and the continuous loop representative has it as derivative.
Positive energy makes this velocity nonvanishing. No inverse function theorem,
dual metric or smoothness at zero velocity is used. -/

@[expose] public section

namespace Finsler.SobolevVelocityContinuity

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevRotationalVariation Finsler.SobolevRotationalRecovery
open Finsler.SobolevRotationalBounds Finsler.SobolevZeroExclusion
open Finsler.SobolevCurveVariation Finsler.SobolevEnergyDifferential Finsler.SobolevEnergy
open Finsler.AmbientLagrangian Finsler.FiberLegendre
open MeasureTheory Set Filter Topology Metric
open scoped RealInnerProductSpace Interval

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The actual tangent Legendre covector of an ambient position--velocity pair. -/
def legendre (F : ReversibleMetric n) (z : Ambient n × Ambient n) : Ambient n →L[ℝ] ℝ :=
  tangentCovector z.1 (velocityDifferential F z)

theorem legendre_injective (F : ReversibleMetric n) {q v w : Ambient n} (hq : ‖q‖ = 1)
    (hv : ⟪q, v⟫ = 0) (hw : ⟪q, w⟫ = 0) (h : legendre F (q, v) = legendre F (q, w)) :
    v = w := by
  apply tangent_eq_of_velocityDifferential_eq F hq hv hw
  intro k hk
  have hk' := congrArg (fun p : Ambient n →L[ℝ] ℝ => p k) h
  change tangentCovector q (velocityDifferential F (q, v)) k =
    tangentCovector q (velocityDifferential F (q, w)) k at hk'
  rwa [tangentCovector_apply_of_orthogonal _ _ _ hk,
    tangentCovector_apply_of_orthogonal _ _ _ hk] at hk'

theorem velocityDifferential_continuousAt (F : ReversibleMetric n)
    {z : Ambient n × Ambient n} (hz : z.1 ≠ 0) : ContinuousAt (velocityDifferential F) z := by
  have h := (Finsler.AmbientEnergyRegularity.lagrangian_fderiv_continuousAt F hz).clm_comp
    (continuousAt_const (y := ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n)))
  exact h

theorem legendre_continuousAt (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z.1 ≠ 0) : ContinuousAt (legendre F) z := by
  have hvd := velocityDifferential_continuousAt F hz
  have hq : ContinuousAt (fun z : Ambient n × Ambient n => z.1) z := continuousAt_fst
  have hi : ContinuousAt (fun z : Ambient n × Ambient n => innerSL ℝ z.1) z :=
    (innerSL ℝ).continuous.continuousAt.comp hq
  show ContinuousAt (fun z : Ambient n × Ambient n =>
    velocityDifferential F z - velocityDifferential F z z.1 • innerSL ℝ z.1) z
  exact hvd.sub ((hvd.clm_apply hq).smul hi)

/-- Unit positions with tangent velocity of norm at most B. -/
def tangentBall (n : ℕ) (B : ℝ) : Set (Ambient n × Ambient n) :=
  {z | ‖z.1‖ = 1 ∧ ⟪z.1, z.2⟫ = 0 ∧ ‖z.2‖ ≤ B}

theorem tangentBall_isCompact (n : ℕ) (B : ℝ) : IsCompact (tangentBall n B) := by
  apply isCompact_of_isClosed_isBounded
  · have h1 : IsClosed {z : Ambient n × Ambient n | ‖z.1‖ = 1} :=
      isClosed_eq (continuous_norm.comp continuous_fst) continuous_const
    have h2 : IsClosed {z : Ambient n × Ambient n | ⟪z.1, z.2⟫ = 0} :=
      isClosed_eq (continuous_fst.inner continuous_snd) continuous_const
    have h3 : IsClosed {z : Ambient n × Ambient n | ‖z.2‖ ≤ B} :=
      isClosed_le (continuous_norm.comp continuous_snd) continuous_const
    exact h1.inter (h2.inter h3)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨max 1 B, fun z hz => ?_⟩
    obtain ⟨h1, _h2, h3⟩ := hz
    rw [Prod.norm_def]
    exact max_le_max h1.le h3

theorem ne_zero_of_mem_tangentBall {B : ℝ} {z : Ambient n × Ambient n}
    (hz : z ∈ tangentBall n B) : z.1 ≠ 0 := by
  intro h
  have h1 := hz.1
  rw [h, norm_zero] at h1
  norm_num at h1

def legendrePair (F : ReversibleMetric n) (z : Ambient n × Ambient n) :
    Ambient n × (Ambient n →L[ℝ] ℝ) := (z.1, legendre F z)

theorem legendrePair_continuousOn (F : ReversibleMetric n) (B : ℝ) :
    ContinuousOn (legendrePair F) (tangentBall n B) := fun _ hz =>
  (continuousAt_fst.prodMk (legendre_continuousAt F (ne_zero_of_mem_tangentBall hz))).continuousWithinAt

theorem legendrePair_injOn (F : ReversibleMetric n) (B : ℝ) :
    InjOn (legendrePair F) (tangentBall n B) := by
  rintro ⟨q, v⟩ hz ⟨q', v'⟩ hz' h
  have h1 : q = q' := congrArg Prod.fst h
  subst h1
  have h2 : legendre F (q, v) = legendre F (q, v') := congrArg Prod.snd h
  exact Prod.ext rfl (legendre_injective F hz.1 hz.2.1 hz'.2.1 h2)

theorem legendrePair_isEmbedding (F : ReversibleMetric n) (B : ℝ) :
    IsEmbedding ((tangentBall n B).domRestrict (legendrePair F)) := by
  have : CompactSpace (tangentBall n B) :=
    isCompact_iff_compactSpace.mp (tangentBall_isCompact n B)
  exact ((legendrePair_continuousOn F B).domRestrict.isClosedEmbedding
    (legendrePair_injOn F B).injective).toIsEmbedding

/-- The compact range of the tangent Legendre pair map. -/
abbrev legendreRange (F : ReversibleMetric n) (B : ℝ) :
    Set (Ambient n × (Ambient n →L[ℝ] ℝ)) :=
  range ((tangentBall n B).domRestrict (legendrePair F))

theorem legendreRange_isCompact (F : ReversibleMetric n) (B : ℝ) :
    IsCompact (legendreRange F B) := by
  have : CompactSpace (tangentBall n B) :=
    isCompact_iff_compactSpace.mp (tangentBall_isCompact n B)
  exact isCompact_range (legendrePair_continuousOn F B).domRestrict

/-- The continuous inverse of the Legendre pair map on its range. -/
def legendreInverse (F : ReversibleMetric n) (B : ℝ) (y : legendreRange F B) :
    Ambient n × Ambient n :=
  (((legendrePair_isEmbedding F B).toHomeomorph.symm y : tangentBall n B) :
    Ambient n × Ambient n)

theorem legendreInverse_continuous (F : ReversibleMetric n) (B : ℝ) :
    Continuous (legendreInverse F B) :=
  continuous_subtype_val.comp (legendrePair_isEmbedding F B).toHomeomorph.symm.continuous

theorem legendreInverse_mem (F : ReversibleMetric n) (B : ℝ) (y : legendreRange F B) :
    legendreInverse F B y ∈ tangentBall n B :=
  ((legendrePair_isEmbedding F B).toHomeomorph.symm y).property

theorem legendrePair_legendreInverse (F : ReversibleMetric n) (B : ℝ)
    (y : legendreRange F B) : legendrePair F (legendreInverse F B y) = y := by
  have h := congrArg Subtype.val
    ((legendrePair_isEmbedding F B).toHomeomorph.apply_symm_apply y)
  rw [IsEmbedding.toHomeomorph_apply_coe] at h
  exact h

theorem legendreInverse_legendrePair (F : ReversibleMetric n) (B : ℝ)
    {z : Ambient n × Ambient n} (hz : z ∈ tangentBall n B) :
    legendreInverse F B ⟨legendrePair F z, ⟨⟨z, hz⟩, rfl⟩⟩ = z := by
  have h := IsEmbedding.toHomeomorph_symm_apply (legendrePair_isEmbedding F B) ⟨z, hz⟩
  exact congrArg Subtype.val h

/-! ### Application to tangent-critical loops -/

/-- A uniform a.e. bound for the actual weak velocity, chosen once. -/
def velocityBound (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) : ℝ :=
  (exists_weakVelocity_ae_bound b F u hc).choose

theorem velocityBound_pos (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) : 0 < velocityBound b F u hc :=
  (exists_weakVelocity_ae_bound b F u hc).choose_spec.1

theorem velocity_le_velocityBound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    ∀ᵐ t ∂intervalMeasure, ‖velocity (u.data : Space n) t‖ ≤ velocityBound b F u hc :=
  (exists_weakVelocity_ae_bound b F u hc).choose_spec.2

/-- The continuous position--covector path of a tangent-critical loop. -/
def legendrePath (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) :
    Ambient n × (Ambient n →L[ℝ] ℝ) :=
  (continuousRepresentative (u.data : Space n) t, recoveredCovector b F u hc t)

theorem legendrePath_continuousOn (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    ContinuousOn (legendrePath b F u hc) (Icc 0 1) :=
  (continuousRepresentative_continuousOn (u.data : Space n)).prodMk
    (recoveredCovector_continuousOn b F u hc)

theorem legendrePath_ae (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) :
    ∀ᵐ t ∂intervalMeasure, weakJet u t ∈ tangentBall n (velocityBound b F u hc) ∧
      legendrePath b F u hc t = legendrePair F (weakJet u t) := by
  filter_upwards [velocity_le_velocityBound b F u hc, weakVelocity_orthogonal_ae u,
    recoveredCovector_ae b F u hc, ae_restrict_mem measurableSet_Ioo] with t hB ho hQ hmem
  exact ⟨⟨u.sphere_constraint ⟨t, Ioo_subset_Icc_self hmem⟩, ho, hB⟩, Prod.ext rfl hQ⟩

theorem legendrePath_mem_range (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    legendrePath b F u hc t ∈ legendreRange F (velocityBound b F u hc) := by
  set B := velocityBound b F u hc
  have hRc : IsClosed (legendreRange F B) := (legendreRange_isCompact F B).isClosed
  have h0 : ((continuousRepresentative (u.data : Space n) 0, (0 : Ambient n)) :
      Ambient n × Ambient n) ∈ tangentBall n B :=
    ⟨u.sphere_constraint ⟨0, by norm_num⟩, inner_zero_right _,
      by rw [norm_zero]; exact (velocityBound_pos b F u hc).le⟩
  have hne : (legendreRange F B).Nonempty := ⟨_, ⟨⟨_, h0⟩, rfl⟩⟩
  rw [hRc.mem_iff_infDist_zero hne]
  have hcont : ContinuousOn (fun s => infDist (legendrePath b F u hc s) (legendreRange F B))
      (Icc 0 1) :=
    (continuous_infDist_pt (legendreRange F B)).comp_continuousOn
      (legendrePath_continuousOn b F u hc)
  have hae : (fun s => infDist (legendrePath b F u hc s) (legendreRange F B))
      =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ => 0 := by
    have h := legendrePath_ae b F u hc
    change ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at h
    rw [restrict_Ioo_eq_restrict_Icc] at h
    filter_upwards [h] with s hs
    rw [hs.2]
    exact infDist_zero_of_mem ⟨⟨weakJet u s, hs.1⟩, rfl⟩
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae hcont
    continuousOn_const ht

/-- The path, clamped to [0,1], as a point of the Legendre range. -/
def legendrePathRange (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) :
    legendreRange F (velocityBound b F u hc) :=
  ⟨legendrePath b F u hc (projIcc 0 1 zero_le_one t),
    legendrePath_mem_range b F u hc (projIcc 0 1 zero_le_one t).property⟩

theorem legendrePathRange_continuous (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    Continuous (legendrePathRange b F u hc) :=
  ((legendrePath_continuousOn b F u hc).comp_continuous
    (continuous_subtype_val.comp continuous_projIcc)
    (fun t => (projIcc 0 1 zero_le_one t).property)).subtype_mk _

/-- The continuous representative of the actual weak velocity. -/
def velocityRep (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) : Ambient n :=
  (legendreInverse F (velocityBound b F u hc) (legendrePathRange b F u hc t)).2

theorem velocityRep_continuous (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    Continuous (velocityRep b F u hc) :=
  continuous_snd.comp ((legendreInverse_continuous F _).comp
    (legendrePathRange_continuous b F u hc))

theorem legendreInverse_path_fst (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (legendreInverse F (velocityBound b F u hc) (legendrePathRange b F u hc t)).1 =
      continuousRepresentative (u.data : Space n) t := by
  have h := congrArg Prod.fst
    (legendrePair_legendreInverse F (velocityBound b F u hc) (legendrePathRange b F u hc t))
  simpa only [legendrePair, legendrePathRange, legendrePath, projIcc_of_mem _ ht] using h

/-- The representative is tangent, bounded, and has the recovered covector as
its Legendre image at every time of [0,1]. -/
theorem velocityRep_spec (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (continuousRepresentative (u.data : Space n) t, velocityRep b F u hc t) ∈
        tangentBall n (velocityBound b F u hc) ∧
      legendre F (continuousRepresentative (u.data : Space n) t, velocityRep b F u hc t) =
        recoveredCovector b F u hc t := by
  set z := legendreInverse F (velocityBound b F u hc) (legendrePathRange b F u hc t)
  have hz : z = (continuousRepresentative (u.data : Space n) t, velocityRep b F u hc t) :=
    Prod.ext (legendreInverse_path_fst b F u hc ht) rfl
  have hmem := legendreInverse_mem F (velocityBound b F u hc) (legendrePathRange b F u hc t)
  have hpair : legendrePair F z = (legendrePathRange b F u hc t : _) :=
    legendrePair_legendreInverse F _ _
  have h2 := congrArg Prod.snd hpair
  change legendre F z = (legendrePath b F u hc (projIcc 0 1 zero_le_one t)).2 at h2
  rw [projIcc_of_mem _ ht] at h2
  rw [← hz]
  exact ⟨hmem, h2⟩

theorem velocityRep_eq_of_mem (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hK : weakJet u t ∈ tangentBall n (velocityBound b F u hc))
    (hP : legendrePath b F u hc t = legendrePair F (weakJet u t)) :
    velocityRep b F u hc t = velocity (u.data : Space n) t := by
  have harg : legendrePathRange b F u hc t = ⟨legendrePair F (weakJet u t), ⟨⟨_, hK⟩, rfl⟩⟩ := by
    apply Subtype.ext
    change legendrePath b F u hc (projIcc 0 1 zero_le_one t) = _
    rw [projIcc_of_mem _ ht]
    exact hP
  unfold velocityRep
  rw [harg, legendreInverse_legendrePair F _ hK]
  rfl

theorem velocityRep_ae (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) :
    velocityRep b F u hc =ᵐ[intervalMeasure] (velocity (u.data : Space n) : ℝ → Ambient n) := by
  filter_upwards [legendrePath_ae b F u hc, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  exact velocityRep_eq_of_mem b F u hc (Ioo_subset_Icc_self hmem) ht.1 ht.2

theorem velocityRep_tangent (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ⟪continuousRepresentative (u.data : Space n) t, velocityRep b F u hc t⟫ = 0 :=
  (velocityRep_spec b F u hc ht).1.2.1

theorem velocityRep_periodic (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    velocityRep b F u hc 1 = velocityRep b F u hc 0 := by
  have hq : continuousRepresentative (u.data : Space n) 1 =
      continuousRepresentative (u.data : Space n) 0 :=
    (mem_periodicSubmodule_iff (u.data : Space n)).mp u.data.property
  have hr : legendrePathRange b F u hc 1 = legendrePathRange b F u hc 0 := by
    apply Subtype.ext
    simp only [legendrePathRange, projIcc_right, projIcc_left, legendrePath, hq,
      recoveredCovector_periodic_trace b F u hc]
  unfold velocityRep
  rw [hr]

theorem representative_eq_integral (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (u.data : Space n) t =
      continuousRepresentative (u.data : Space n) 0 +
        ∫ x in (0 : ℝ)..t, velocityRep b F u hc x := by
  have h := continuousRepresentative_sub (u.data : Space n)
    (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ht
  have hcongr : (∫ x in (0 : ℝ)..t, (velocity (u.data : Space n) : ℝ → Ambient n) x) =
      ∫ x in (0 : ℝ)..t, velocityRep b F u hc x := by
    apply intervalIntegral.integral_congr_ae
    have h1 := velocityRep_ae b F u hc
    change ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at h1
    rw [restrict_Ioo_eq_restrict_Icc] at h1
    have hsub : Ι (0 : ℝ) t ⊆ Icc 0 1 := by
      rw [uIoc_of_le ht.1]
      exact fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub h1
    filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp h2] with x hx hxI
    exact (hx hxI).symm
  rw [← hcongr, ← h]
  abel

/-- C¹ regularity: the continuous loop representative has the continuous
velocity representative as its derivative within [0,1]. -/
theorem representative_hasDerivWithinAt (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (continuousRepresentative (u.data : Space n))
      (velocityRep b F u hc t) (Icc 0 1) t := by
  have hG : HasDerivAt (fun s => continuousRepresentative (u.data : Space n) 0 +
      ∫ x in (0 : ℝ)..s, velocityRep b F u hc x) (velocityRep b F u hc t) t :=
    ((velocityRep_continuous b F u hc).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _
  exact hG.hasDerivWithinAt.congr (fun s hs => representative_eq_integral b F u hc hs)
    (representative_eq_integral b F u hc ht)

theorem representative_hasDerivAt (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (continuousRepresentative (u.data : Space n)) (velocityRep b F u hc t) t := by
  have hG : HasDerivAt (fun s => continuousRepresentative (u.data : Space n) 0 +
      ∫ x in (0 : ℝ)..s, velocityRep b F u hc x) (velocityRep b F u hc t) t :=
    ((velocityRep_continuous b F u hc).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _
  apply hG.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact representative_eq_integral b F u hc (Ioo_subset_Icc_self hs)

/-- Positive energy: the continuous velocity is bounded below on all of [0,1]. -/
theorem exists_velocityRep_lower_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc (0 : ℝ) 1, c ≤ ‖velocityRep b F u hc t‖ := by
  obtain ⟨c, hc0, hv⟩ := exists_weakVelocity_lower_bound b F u hc hE
  refine ⟨c, hc0, fun t ht => ?_⟩
  have hae : (fun s => min ‖velocityRep b F u hc s‖ c)
      =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] fun _ => c := by
    have h := velocityRep_ae b F u hc
    have h' := hv
    change ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at h h'
    rw [restrict_Ioo_eq_restrict_Icc] at h h'
    filter_upwards [h, h'] with s hs hs'
    rw [hs]
    exact min_eq_right hs'
  have heq := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hae
    ((velocityRep_continuous b F u hc).norm.min continuous_const).continuousOn
    continuousOn_const ht
  exact min_eq_right_iff.mp heq

theorem velocityRep_ne_zero (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : velocityRep b F u hc t ≠ 0 := by
  obtain ⟨c, hc0, hle⟩ := exists_velocityRep_lower_bound b F u hc hE
  intro h0
  have h := hle t ht
  rw [h0, norm_zero] at h
  linarith

/-- Basis-free summary: every positive-energy tangent-critical actual H¹ sphere
loop has a C¹ representative on [0,1] whose derivative is continuous, periodic,
tangent and nowhere zero, and agrees with the weak velocity almost everywhere. -/
theorem tangentCritical_regular_C1 (F : ReversibleMetric n) (u : SphereLoop n)
    (hc : TangentCritical F u) (hE : 0 < energy F u) :
    ∃ v : ℝ → Ambient n, Continuous v ∧ v 1 = v 0 ∧
      v =ᵐ[intervalMeasure] (velocity (u.data : Space n) : ℝ → Ambient n) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (continuousRepresentative (u.data : Space n)) (v t) (Icc 0 1) t ∧
        ⟪continuousRepresentative (u.data : Space n) t, v t⟫ = 0 ∧ v t ≠ 0 := by
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  exact ⟨velocityRep b F u hc, velocityRep_continuous b F u hc,
    velocityRep_periodic b F u hc, velocityRep_ae b F u hc, fun t ht =>
      ⟨representative_hasDerivWithinAt b F u hc ht, velocityRep_tangent b F u hc ht,
        velocityRep_ne_zero b F u hc hE ht⟩⟩

end

end Finsler.SobolevVelocityContinuity
