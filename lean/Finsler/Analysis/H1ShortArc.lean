module

public import Finsler.Analysis.H1PathLength
public import Finsler.Analysis.SphereDistance
public import Finsler.Analysis.SobolevC1Continuity

/-! Explicit short round closing arcs using the existing rational stereographic
parametrization. They depend continuously in the original strong H1 topology,
are constant at equal endpoints, and have uniformly small Finsler length when
the endpoints are close. Constant-speed parametrization is not asserted. -/

@[expose] public section
namespace Finsler.H1ShortArc

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSpherePath Finsler.SobolevSphereChart Finsler.SobolevOfPrimitive
open Finsler.RationalSphereCurve Finsler.SobolevCurveFamily
open Finsler.SobolevC1Continuity Finsler.AmbientLagrangian
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000
variable {n : ℕ}

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

def pairs (n : ℕ) : Set (Sphere n × Sphere n) :=
  {z | ‖(z.2 : Ambient n) - z.1‖ < 1}

def arc (P Q : Sphere n) : Space n := SphereDistance.segPath (P : Ambient n) Q

theorem pairs_open : IsOpen (pairs n) :=
  isOpen_lt ((continuous_subtype_val.comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).norm continuous_const

theorem arc_mem (z : pairs n) : arc z.val.1 z.val.2 ∈
    SphereDistance.pathsBetween n z.val.1 z.val.2 :=
  SphereDistance.segPath_mem (by simpa using z.val.1.property)
    (by simpa using z.val.2.property) z.property.le

theorem representative_arc (P Q : Sphere n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (arc P Q) t = SphereDistance.segCurve (P : Ambient n) Q t :=
  representative_ofPrimitive _ _ (fun t _ => SphereDistance.segCurve_eq_add_integral
    (P : Ambient n) Q t) ht

theorem velocity_arc_ae (P Q : Sphere n) : velocity (arc P Q) =ᵐ[intervalMeasure]
    SphereDistance.segVel (P : Ambient n) Q := velocity_ofPrimitive_ae _ _
      (fun t _ => SphereDistance.segCurve_eq_add_integral (P : Ambient n) Q t)

theorem value_arc_ae (P Q : Sphere n) : value (arc P Q) =ᵐ[intervalMeasure]
    SphereDistance.segCurve (P : Ambient n) Q := value_ofPrimitive_ae _ _
      (fun t _ => SphereDistance.segCurve_eq_add_integral (P : Ambient n) Q t)

theorem inner_nonneg (z : pairs n) : 0 ≤ ⟪(z.val.2 : Ambient n), (z.val.1 : Ambient n)⟫ := by
  have hp : ‖(z.val.1 : Ambient n)‖ = 1 := by simpa using z.val.1.property
  have hq : ‖(z.val.2 : Ambient n)‖ = 1 := by simpa using z.val.2.property
  have he := norm_sub_sq_real (z.val.2 : Ambient n) (z.val.1 : Ambient n)
  rw [hp, hq] at he
  have hz : ‖(z.val.2 : Ambient n) - z.val.1‖ < 1 := z.property
  nlinarith [norm_nonneg ((z.val.2 : Ambient n) - z.val.1)]

theorem continuous_stereo : Continuous (fun z : pairs n =>
    stereo (z.val.1 : Ambient n) z.val.2) := by
  have hp : Continuous (fun z : pairs n => (z.val.1 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hq : Continuous (fun z : pairs n => (z.val.2 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hi := hq.inner (𝕜 := ℝ) hp
  exact (continuous_const.div (continuous_const.add hi)
    (fun z => show 1 + ⟪(z.val.2 : Ambient n), (z.val.1 : Ambient n)⟫ ≠ 0 from
      ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (inner_nonneg z)))).smul
        (hq.sub (hi.smul hp))

theorem continuous_curve : Continuous (fun z : pairs n × ℝ =>
    SphereDistance.segCurve (z.1.val.1 : Ambient n) z.1.val.2 z.2) := by
  exact (ratMap_contDiff (n := n) 1).continuous.comp
    ((continuous_subtype_val.comp (continuous_fst.comp
      (continuous_subtype_val.comp continuous_fst))).prodMk
      (continuous_snd.smul (continuous_stereo.comp continuous_fst)))

theorem continuous_velocity : Continuous (fun z : pairs n × ℝ =>
    SphereDistance.segVel (z.1.val.1 : Ambient n) z.1.val.2 z.2) := by
  have hp : Continuous (fun z : pairs n × ℝ => (z.1.val.1 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_fst.comp
      (continuous_subtype_val.comp continuous_fst))
  have hs := continuous_stereo.comp (continuous_fst : Continuous (Prod.fst : pairs n × ℝ → _))
  exact ((ratDeriv_continuous (n := n) 1).comp
    (hp.prodMk (continuous_snd.smul hs))).clm_apply (continuous_const.prodMk hs)

theorem continuous_arc : Continuous (fun z : pairs n => arc z.val.1 z.val.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_of_uniform
    (c := fun z t => SphereDistance.segCurve (z.val.1 : Ambient n) z.val.2 t)
    (c' := fun z t => SphereDistance.segVel (z.val.1 : Ambient n) z.val.2 t)
  · exact Eventually.of_forall fun z => value_arc_ae z.val.1 z.val.2
  · exact Eventually.of_forall fun z => velocity_arc_ae z.val.1 z.val.2
  · exact value_arc_ae z.val.1 z.val.2
  · exact velocity_arc_ae z.val.1 z.val.2
  · intro ε hε
    have h1 := eventually_uniform (x₀ := z)
      (f := fun z t => SphereDistance.segCurve (z.val.1 : Ambient n) z.val.2 t)
      (fun t _ => (continuous_curve (n := n)).continuousAt (x := (z, t))) hε
    have h2 := eventually_uniform (x₀ := z)
      (f := fun z t => SphereDistance.segVel (z.val.1 : Ambient n) z.val.2 t)
      (fun t _ => (continuous_velocity (n := n)).continuousAt (x := (z, t))) hε
    filter_upwards [h1, h2] with w hw1 hw2 t ht
    exact ⟨(hw1 t (Ioo_subset_Icc_self ht)).le, (hw2 t (Ioo_subset_Icc_self ht)).le⟩

theorem arc_self (P : Sphere n) : arc P P = constantData (P : Ambient n) := by
  apply eq_of_representative_eqOn
  intro t ht
  rw [representative_arc P P ht, continuousRepresentative_constantData _ ht]
  have hp : ⟪(P : Ambient n), (P : Ambient n)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, show ‖(P : Ambient n)‖ = 1 by simpa using P.property]
    norm_num
  simp [SphereDistance.segCurve, stereo, hp, ratMap, aFun]

theorem exists_energy_bound (F : ReversibleMetric n) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : pairs n,
      pathEnergy F (arc z.val.1 z.val.2) ≤ K * ‖(z.val.2 : Ambient n) - z.val.1‖ ^ 2 := by
  obtain ⟨c, C, _hc, hC, hb⟩ := exists_pathEnergy_bounds F
  refine ⟨32 * C, by positivity, fun z => ?_⟩
  have hvel : (∫ t, ‖velocity (arc z.val.1 z.val.2) t‖ ^ 2 ∂intervalMeasure) ≤
      32 * ‖(z.val.2 : Ambient n) - z.val.1‖ ^ 2 := by
    have hae : ∀ᵐ t ∂intervalMeasure, ‖velocity (arc z.val.1 z.val.2) t‖ ^ 2 ≤
        32 * ‖(z.val.2 : Ambient n) - z.val.1‖ ^ 2 := by
      filter_upwards [velocity_arc_ae z.val.1 z.val.2,
        ae_restrict_mem measurableSet_Ioo] with t hv ht
      rw [hv]
      exact SphereDistance.segVel_sq_le (by simpa using z.val.1.property)
        (by simpa using z.val.2.property) z.property.le (Ioo_subset_Icc_self ht)
    calc
      _ ≤ ∫ _ : ℝ, 32 * ‖(z.val.2 : Ambient n) - z.val.1‖ ^ 2 ∂intervalMeasure :=
        integral_mono_ae (integrable_velocity_sq _) (integrable_const _) hae
      _ = _ := by
        rw [integral_const, Measure.real, SobolevLength.intervalMeasure_univ,
          ENNReal.toReal_one, one_smul]
  calc
    pathEnergy F (arc z.val.1 z.val.2) ≤ C *
        ∫ t, ‖velocity (arc z.val.1 z.val.2) t‖ ^ 2 ∂intervalMeasure :=
      (hb _ (arc_mem z).1).2
    _ ≤ C * (32 * ‖(z.val.2 : Ambient n) - z.val.1‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hvel hC.le
    _ = _ := by ring

theorem exists_length_radius (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z : pairs n,
      ‖(z.val.2 : Ambient n) - z.val.1‖ < ρ →
        H1PathLength.length F (arc z.val.1 z.val.2) < ε := by
  obtain ⟨K, hK, hb⟩ := exists_energy_bound F
  refine ⟨min 1 (ε / Real.sqrt K), lt_min zero_lt_one
    (div_pos hε (Real.sqrt_pos.mpr hK)), min_le_left _ _, fun z hz => ?_⟩
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hprod : Real.sqrt K * ‖(z.val.2 : Ambient n) - z.val.1‖ < ε := by
    have h := (lt_div_iff₀ hs).mp (hz.trans_le (min_le_right _ _))
    nlinarith
  have hlen := H1PathLength.length_sq_le_energy F (arc_mem z).1
  have hb' := hb z
  have hsq := Real.sq_sqrt hK.le
  have h0 := H1PathLength.length_nonneg F (arc z.val.1 z.val.2)
  have hprod0 : 0 ≤ Real.sqrt K * ‖(z.val.2 : Ambient n) - z.val.1‖ :=
    mul_nonneg hs.le (norm_nonneg _)
  have hprod2 := (sq_lt_sq₀ hprod0 hε.le).mpr hprod
  rw [mul_pow, hsq] at hprod2
  nlinarith

end
end Finsler.H1ShortArc
