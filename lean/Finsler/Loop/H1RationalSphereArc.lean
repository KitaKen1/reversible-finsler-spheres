module

public import Finsler.Loop.RationalSphereArcCoordinates
public import Finsler.Analysis.H1ShortArc

/-! The SAME rational quarter arcs are actual elements of the
original strong-H1 graph, with exact representatives and genuine
joint parameter continuity. Orthogonal endpoints need no short
chord hypothesis. -/
@[expose] public section
namespace Finsler.H1RationalSphereArc
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.RationalSphereArc
open Finsler.RationalSphereCurve Finsler.SobolevSphereChart
open Finsler.SobolevCurveFamily
open Finsler.SobolevC1Continuity MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem ratMap_scale {n : ℕ} (r : ℝ) (x y : Ambient n) :
    ratMap 1 (x, r • y) = ratMap r (x, y) := by
  have ha : aFun 1 (r • y) = aFun r y := by
    simp only [aFun, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp only [ratMap, ha, one_smul]

theorem stereo_pair {n : ℕ} (z : orthogonalPairs n) :
    stereo (z.val.1 : Ambient n) (z.val.2 : Ambient n) = (2 : ℝ) • (z.val.2 : Ambient n) := by
  have hz : ⟪(z.val.2 : Ambient n), (z.val.1 : Ambient n)⟫ = 0 :=
    (real_inner_comm _ _).trans z.property
  simp only [stereo, hz, add_zero, div_one, zero_smul, sub_zero]

def data {n : ℕ} (z : orthogonalPairs n) : Space n := H1ShortArc.arc z.val.1 z.val.2

theorem curve_eq {n : ℕ} (z : orthogonalPairs n) (t : ℝ) :
    SphereDistance.segCurve (z.val.1 : Ambient n) (z.val.2 : Ambient n) t =
      ratMap (2 * t) ((z.val.1 : Ambient n), (z.val.2 : Ambient n)) := by
  rw [SphereDistance.segCurve, stereo_pair, smul_smul, ratMap_scale]
  congr 1
  ring

theorem representative {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    continuousRepresentative (data z) (t : ℝ) = (point z t : Ambient n) :=
  (H1ShortArc.representative_arc _ _ t.property).trans (curve_eq z (t : ℝ))

theorem continuous_curve (n : ℕ) : Continuous (fun z : orthogonalPairs n × ℝ =>
    SphereDistance.segCurve (z.1.val.1 : Ambient n) (z.1.val.2 : Ambient n) z.2) := by
  simp only [SphereDistance.segCurve, stereo_pair]
  have hc := (ratMap_contDiff (n := n) 1).continuous.comp
    ((show Continuous (fun z : orthogonalPairs n × ℝ => (z.1.val.1 : Ambient n)) by fun_prop).prodMk
      (show Continuous (fun z : orthogonalPairs n × ℝ => z.2 • ((2 : ℝ) • (z.1.val.2 : Ambient n))) by fun_prop))
  exact hc

theorem continuous_velocity (n : ℕ) : Continuous (fun z : orthogonalPairs n × ℝ =>
    SphereDistance.segVel (z.1.val.1 : Ambient n) (z.1.val.2 : Ambient n) z.2) := by
  simp only [SphereDistance.segVel, stereo_pair]
  have hp : Continuous (fun z : orthogonalPairs n × ℝ => (z.1.val.1 : Ambient n)) := by fun_prop
  have hs : Continuous (fun z : orthogonalPairs n × ℝ => (2 : ℝ) • (z.1.val.2 : Ambient n)) := by fun_prop
  have hz : Continuous (fun _ : orthogonalPairs n × ℝ => (0 : Ambient n)) := continuous_const
  have hc := ((ratDeriv_continuous (n := n) 1).comp
    (hp.prodMk (continuous_snd.smul hs))).clm_apply (hz.prodMk hs)
  exact hc

theorem continuous_data (n : ℕ) : Continuous (data : orthogonalPairs n → Space n) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_of_uniform
    (c := fun z t => SphereDistance.segCurve (z.val.1 : Ambient n) (z.val.2 : Ambient n) t)
    (c' := fun z t => SphereDistance.segVel (z.val.1 : Ambient n) (z.val.2 : Ambient n) t)
  · exact Eventually.of_forall fun z => H1ShortArc.value_arc_ae z.val.1 z.val.2
  · exact Eventually.of_forall fun z => H1ShortArc.velocity_arc_ae z.val.1 z.val.2
  · exact H1ShortArc.value_arc_ae z.val.1 z.val.2
  · exact H1ShortArc.velocity_arc_ae z.val.1 z.val.2
  · intro ε hε
    have h₀ := eventually_uniform (x₀ := z)
      (f := fun z t => SphereDistance.segCurve (z.val.1 : Ambient n) (z.val.2 : Ambient n) t)
      (fun t _ => (continuous_curve n).continuousAt (x := (z, t))) hε
    have h₁ := eventually_uniform (x₀ := z)
      (f := fun z t => SphereDistance.segVel (z.val.1 : Ambient n) (z.val.2 : Ambient n) t)
      (fun t _ => (continuous_velocity n).continuousAt (x := (z, t))) hε
    filter_upwards [h₀, h₁] with w hw₀ hw₁ t ht
    exact ⟨(hw₀ t (Ioo_subset_Icc_self ht)).le, (hw₁ t (Ioo_subset_Icc_self ht)).le⟩

theorem source {n : ℕ} (z : orthogonalPairs n) : continuousRepresentative (data z) 0 = (z.val.1 : Ambient n) := by
  simpa only [Set.Icc.coe_zero, point_zero] using representative z 0

theorem target {n : ℕ} (z : orthogonalPairs n) : continuousRepresentative (data z) 1 = (z.val.2 : Ambient n) := by
  simpa only [Set.Icc.coe_one, point_one] using representative z 1

end
end Finsler.H1RationalSphereArc
