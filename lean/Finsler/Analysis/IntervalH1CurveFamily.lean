module

public import Finsler.Analysis.IntervalChainRule
public import Finsler.Geometry.RationalSphereCurve
public import Finsler.Analysis.IntervalH1CurveVariation
public import Finsler.Analysis.IntervalH1EnergyZero
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Asymptotics.Lemmas

/-! The actual H¹ sphere curve through a loop in a periodic tangent direction. The
curve applies the rational sphere curve pointwise to the continuous representatives
of the base loop and the direction; its weak velocity is certified by the
one-dimensional chain rule and packaged in the original weak-derivative graph. It is
periodic, satisfies the genuine sphere constraint and passes through the base loop
at r = 0. Its derivative at r = 0 is proved separately. -/

@[expose] public section

namespace Finsler.SobolevCurveFamily

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevTangent
open Finsler.SobolevCurveVariation Finsler.RationalSphereCurve Finsler.IntervalChainRule
open MeasureTheory Set Filter Asymptotics
open scoped Topology RealInnerProductSpace ENNReal NNReal

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

/-- The pair of continuous representatives of a base loop and a direction. -/
def pairRep (u h : Space n) (t : ℝ) : Ambient n × Ambient n :=
  (continuousRepresentative u t, continuousRepresentative h t)

/-- The pair of weak velocities. -/
def pairVel (u h : Space n) (t : ℝ) : Ambient n × Ambient n :=
  (velocity u t, velocity h t)

theorem pairRep_continuousOn (u h : Space n) : ContinuousOn (pairRep u h) (Icc 0 1) :=
  (continuousRepresentative_continuousOn u).prodMk (continuousRepresentative_continuousOn h)

theorem pairVel_intervalIntegrable (u h : Space n) :
    IntervalIntegrable (pairVel u h) volume 0 1 := by
  have hu := velocity_intervalIntegrable u
  have hh := velocity_intervalIntegrable h
  exact ⟨hu.1.prodMk hh.1, hu.2.prodMk hh.2⟩

theorem pairRep_eq_add_integral (u h : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pairRep u h t = pairRep u h 0 + ∫ s in (0 : ℝ)..t, pairVel u h s := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (pairVel_intervalIntegrable u h).mono_set hsub
  have h1 : (∫ s in (0 : ℝ)..t, pairVel u h s).1 = ∫ s in (0 : ℝ)..t, velocity u s := by
    have := (ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).intervalIntegral_comp_comm hint
    simpa [pairVel] using this.symm
  have h2 : (∫ s in (0 : ℝ)..t, pairVel u h s).2 = ∫ s in (0 : ℝ)..t, velocity h s := by
    have := (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)).intervalIntegral_comp_comm hint
    simpa [pairVel] using this.symm
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, h1, ← continuousRepresentative_sub u h0 ht]
    simp only [pairRep]
    abel
  · rw [Prod.snd_add, h2, ← continuousRepresentative_sub h h0 ht]
    simp only [pairRep]
    abel

theorem pairRep_hasDerivAt_ae (u h : Space n) :
    ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), HasDerivAt (pairRep u h) (pairVel u h s) s := by
  have hu := continuousRepresentative_hasDerivAt_ae u
  have hh := continuousRepresentative_hasDerivAt_ae h
  change ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at hu hh
  filter_upwards [hu, hh] with s h1 h2
  exact h1.prodMk h2

theorem ratMap_pairRep_sub (r : ℝ) (u h : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ratMap r (pairRep u h t) - ratMap r (pairRep u h 0) =
      ∫ s in (0 : ℝ)..t, ratDeriv r (pairRep u h s) (pairVel u h s) := by
  have hc := comp_sub_eq_integral (ratMap_contDiff r) (pairVel_intervalIntegrable u h)
    (fun t ht => pairRep_eq_add_integral u h ht) (pairRep_hasDerivAt_ae u h) ht
  simpa only [ratMap_fderiv] using hc

/-- The value of the realizing curve. -/
def curveValueFun (r : ℝ) (u h : Space n) (t : ℝ) : Ambient n := ratMap r (pairRep u h t)

/-- The weak velocity of the realizing curve. -/
def curveVelocityFun (r : ℝ) (u h : Space n) (t : ℝ) : Ambient n :=
  ratDeriv r (pairRep u h t) (pairVel u h t)

theorem curveValue_continuousOn (r : ℝ) (u h : Space n) :
    ContinuousOn (curveValueFun r u h) (Icc 0 1) :=
  (ratMap_contDiff r).continuous.comp_continuousOn (pairRep_continuousOn u h)

theorem memLp_of_continuousOn {f : ℝ → Ambient n} (hf : ContinuousOn f (Icc 0 1)) :
    MemLp f 2 intervalMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC t (Ioo_subset_Icc_self ht)

theorem curveValue_memLp (r : ℝ) (u h : Space n) :
    MemLp (curveValueFun r u h) 2 intervalMeasure :=
  memLp_of_continuousOn (curveValue_continuousOn r u h)

theorem ratDeriv_continuous (r : ℝ) : Continuous (ratDeriv (n := n) r) := by
  have hc := (ratMap_contDiff (n := n) r).continuous_fderiv (by norm_num)
  have hfun : fderiv ℝ (ratMap (n := n) r) = ratDeriv r := funext (ratMap_fderiv r)
  rwa [hfun] at hc

theorem velocitySum_memLp (u h : Space n) :
    MemLp (fun s => ‖velocity u s‖ + ‖velocity h s‖) 2 intervalMeasure :=
  (Lp.memLp (velocity u)).norm.add (Lp.memLp (velocity h)).norm

theorem norm_pairVel_le (u h : Space n) (s : ℝ) :
    ‖pairVel u h s‖ ≤ ‖velocity u s‖ + ‖velocity h s‖ :=
  norm_prod_le_iff.mpr ⟨le_add_of_nonneg_right (norm_nonneg _),
    le_add_of_nonneg_left (norm_nonneg _)⟩

theorem curveVelocity_aestronglyMeasurable (r : ℝ) (u h : Space n) :
    AEStronglyMeasurable (curveVelocityFun r u h) intervalMeasure := by
  have hD : ContinuousOn (fun s => ratDeriv r (pairRep u h s)) (Icc 0 1) :=
    (ratDeriv_continuous r).comp_continuousOn (pairRep_continuousOn u h)
  have he : Continuous (fun p : (Ambient n × Ambient n →L[ℝ] Ambient n) ×
      (Ambient n × Ambient n) => p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have hD' : AEStronglyMeasurable (fun s => ratDeriv r (pairRep u h s)) intervalMeasure :=
    (hD.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hV : AEStronglyMeasurable (pairVel u h) intervalMeasure :=
    (Lp.aestronglyMeasurable (velocity u)).prodMk (Lp.aestronglyMeasurable (velocity h))
  exact he.comp_aestronglyMeasurable (hD'.prodMk hV)

theorem curveVelocity_memLp (r : ℝ) (u h : Space n) :
    MemLp (curveVelocityFun r u h) 2 intervalMeasure := by
  have hD : ContinuousOn (fun s => ratDeriv r (pairRep u h s)) (Icc 0 1) :=
    (ratDeriv_continuous r).comp_continuousOn (pairRep_continuousOn u h)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  refine (velocitySum_memLp u h).of_le_mul (c := C)
    (curveVelocity_aestronglyMeasurable r u h) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have h2 := hC s (Ioo_subset_Icc_self hs)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    ‖curveVelocityFun r u h s‖ ≤ ‖ratDeriv r (pairRep u h s)‖ * ‖pairVel u h s‖ :=
      (ratDeriv r (pairRep u h s)).le_opNorm (pairVel u h s)
    _ ≤ C * (‖velocity u s‖ + ‖velocity h s‖) :=
      mul_le_mul h2 (norm_pairVel_le u h s) (norm_nonneg _) ((norm_nonneg _).trans h2)

theorem curveValue_eq_add_primitive (r : ℝ) (u h : Space n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    curveValueFun r u h t = curveValueFun r u h 0 +
      Finsler.IntervalPrimitive.primitive (curveVelocityFun r u h) t := by
  have hsub := ratMap_pairRep_sub r u h ht
  unfold curveValueFun Finsler.IntervalPrimitive.primitive curveVelocityFun
  rw [← hsub]
  abel

theorem curveValue_hasWeakLineVelocity (r : ℝ) (u h : Space n) :
    TauCeti.HasWeakLineDerivOn volume unitInterval (curveValueFun r u h)
      (curveVelocityFun r u h) 1 := by
  have hint : IntervalIntegrable (curveVelocityFun r u h) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact (curveVelocity_memLp r u h).integrable (by norm_num)
  have hP := Finsler.IntervalPrimitive.primitive_hasWeakLineDeriv hint
  have hc := TauCeti.hasWeakLineDerivOn_const (μ := volume) (Ω := Finsler.IntervalSobolev.unitInterval)
    (v := (1 : ℝ)) (curveValueFun r u h 0)
  have hs := hc.add hP
  have hv : (fun _ => curveValueFun r u h 0) +
      Finsler.IntervalPrimitive.primitive (curveVelocityFun r u h)
        =ᵐ[volume.restrict (Finsler.IntervalSobolev.unitInterval : Set ℝ)] curveValueFun r u h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (curveValue_eq_add_primitive r u h (Ioo_subset_Icc_self ht)).symm
  have hd : (fun _ : ℝ => (0 : Ambient n)) + curveVelocityFun r u h
      =ᵐ[volume.restrict (Finsler.IntervalSobolev.unitInterval : Set ℝ)] curveVelocityFun r u h :=
    Eventually.of_forall fun t => zero_add _
  exact (hs.congr_ae hv).congr_ae_deriv hd

def curveValueLp (r : ℝ) (u h : Space n) : ValueLp n :=
  (curveValue_memLp r u h).toLp (curveValueFun r u h)

def curveVelocityLp (r : ℝ) (u h : Space n) : ValueLp n :=
  (curveVelocity_memLp r u h).toLp (curveVelocityFun r u h)

theorem curveValueLp_ae (r : ℝ) (u h : Space n) :
    curveValueLp r u h =ᵐ[intervalMeasure] curveValueFun r u h :=
  (curveValue_memLp r u h).coeFn_toLp

theorem curveVelocityLp_ae (r : ℝ) (u h : Space n) :
    curveVelocityLp r u h =ᵐ[intervalMeasure] curveVelocityFun r u h :=
  (curveVelocity_memLp r u h).coeFn_toLp

def curveDerivativeLp (r : ℝ) (u h : Space n) : DerivativeLp n :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 intervalMeasure (curveVelocityLp r u h)

theorem curveDerivativeLp_apply_ae (r : ℝ) (u h : Space n) (d : ℝ) :
    (fun t => curveDerivativeLp r u h t d) =ᵐ[intervalMeasure]
      fun t => d • curveVelocityFun r u h t := by
  let L : Ambient n →L[ℝ] (ℝ →L[ℝ] Ambient n) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap
  have hL := L.coeFn_compLpL (p := 2) (μ := intervalMeasure) (curveVelocityLp r u h)
  filter_upwards [hL, curveVelocityLp_ae r u h] with t hD hv
  change (L.compLpL 2 intervalMeasure (curveVelocityLp r u h)) t d = _
  rw [hD, hv]
  rfl

theorem curveValue_hasWeakFDeriv (r : ℝ) (u h : Space n) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (curveValueLp r u h))
      (curveDerivativeLp r u h) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have hs := (curveValue_hasWeakLineVelocity r u h).smul_direction d
  change TauCeti.HasWeakLineDerivOn volume unitInterval (curveValueFun r u h)
    (fun t => d • curveVelocityFun r u h t) (d • (1 : ℝ)) at hs
  have hs' : TauCeti.HasWeakLineDerivOn volume unitInterval (curveValueFun r u h)
      (fun t => d • curveVelocityFun r u h t) d := by
    simpa only [smul_eq_mul, mul_one] using hs
  exact (hs'.congr_ae (curveValueLp_ae r u h).symm).congr_ae_deriv
    (curveDerivativeLp_apply_ae r u h d).symm

/-- The realizing curve as an element of the original weak H¹ graph. -/
def curveData (r : ℝ) (u h : Space n) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (curveValueLp r u h) (curveDerivativeLp r u h)
    (curveValue_hasWeakFDeriv r u h)

theorem value_curveData (r : ℝ) (u h : Space n) :
    value (curveData r u h) = curveValueLp r u h := by
  change TauCeti.WeakDerivStep.prevL (base n) (curveData r u h) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_curveData (r : ℝ) (u h : Space n) :
    derivative (curveData r u h) = curveDerivativeLp r u h := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (curveData r u h) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem value_curveData_ae (r : ℝ) (u h : Space n) :
    value (curveData r u h) =ᵐ[intervalMeasure] curveValueFun r u h := by
  rw [value_curveData]
  exact curveValueLp_ae r u h

theorem velocity_curveData_ae (r : ℝ) (u h : Space n) :
    velocity (curveData r u h) =ᵐ[intervalMeasure] curveVelocityFun r u h := by
  have hD := curveDerivativeLp_apply_ae r u h 1
  rw [← derivative_curveData] at hD
  filter_upwards [velocity_apply_ae (curveData r u h), hD] with t hv hd
  rw [hv, hd, one_smul]

theorem representative_curveData (r : ℝ) (u h : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (curveData r u h) t = ratMap r (pairRep u h t) :=
  continuous_representative_unique (continuousRepresentative_continuousOn _)
    (curveValue_continuousOn r u h) (value_ae_continuousRepresentative _)
    (value_curveData_ae r u h) ht

theorem curveData_periodic (r : ℝ) {u h : Space n} (hu : u ∈ periodicSubmodule n)
    (hh : h ∈ periodicSubmodule n) : curveData r u h ∈ periodicSubmodule n := by
  rw [mem_periodicSubmodule_iff] at hu hh ⊢
  change continuousRepresentative u 1 = continuousRepresentative u 0 at hu
  change continuousRepresentative h 1 = continuousRepresentative h 0 at hh
  change continuousRepresentative _ 1 = continuousRepresentative _ 0
  rw [representative_curveData r u h (by norm_num), representative_curveData r u h (by norm_num)]
  simp only [pairRep, hu, hh]

theorem curveData_sphere (r : ℝ) (u : SphereLoop n) {h : Space n}
    (hh : h ∈ tangentSubmodule u) (t : ClosedInterval) :
    ‖continuousRepresentative (curveData r (u.data : Space n) h) t‖ = 1 := by
  rw [representative_curveData r _ h t.property]
  exact norm_ratMap (u.sphere_constraint t) (((mem_tangentSubmodule_iff u h).mp hh).2 t)

/-- The sphere loop realizing a tangent field to first order. -/
def curveLoop (u : SphereLoop n) (h : TangentSpace u) (r : ℝ) : SphereLoop n where
  data := ⟨curveData r (u.data : Space n) (h : Space n),
    curveData_periodic r u.data.property ((mem_tangentSubmodule_iff u h).mp h.property).1⟩
  sphere_constraint := curveData_sphere r u h.property

theorem curveData_zero (u h : Space n) : curveData 0 u h = u := by
  apply Finsler.SobolevEnergy.h1_value_injective
  apply Lp.ext
  filter_upwards [value_curveData_ae 0 u h, value_ae_continuousRepresentative u]
    with t h1 h2
  rw [h1, h2]
  simp only [curveValueFun, ratMap_zero, pairRep]

theorem curveLoop_zero (u : SphereLoop n) (h : TangentSpace u) : curveLoop u h 0 = u := by
  apply sphereLoop_data_injective
  exact curveData_zero (u.data : Space n) (h : Space n)

end

end Finsler.SobolevCurveFamily
