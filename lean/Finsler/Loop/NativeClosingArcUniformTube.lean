module

public import Finsler.Loop.ShortArcUniformEndpoint
public import Finsler.Loop.NativeClosingArcNestedCut
public import Finsler.Loop.NativeClosingArcRetainedCut
public import Mathlib.Topology.Category.TopCat.Basic

/-! ONE actual near-tube radius works for EVERY inner arc time in
BOTH original closed-self-cut branches. The two small output loops
have length <2epsilon. The radius is chosen before all cochains,
degrees and powers; inner-tube membership is proved, not supplied. -/
@[expose] public section
namespace Finsler.NativeClosingArcUniformTube
open CategoryTheory
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.SobolevSpherePath Finsler.H1SelfCutNeighborhood Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
variable {n : ℕ}

def arcRadius (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) : ℝ :=
  (H1ShortArc.exists_length_radius F hε).choose

theorem arcRadius_spec (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    0 < arcRadius F hε ∧ arcRadius F hε ≤ 1 ∧ ∀ z : H1ShortArc.pairs n,
      ‖(z.val.2 : Ambient n) - z.val.1‖ < arcRadius F hε →
        H1PathLength.length F (H1ShortArc.arc z.val.1 z.val.2) < ε :=
  (H1ShortArc.exists_length_radius F hε).choose_spec

def radius (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) : ℝ := arcRadius F hε / 8

theorem radius_pos (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) : 0 < radius F hε :=
  div_pos (arcRadius_spec F hε).1 (by norm_num)

theorem radius_le_eighth (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) : radius F hε ≤ 1 / 8 := by
  have h := (arcRadius_spec F hε).2.1
  dsimp only [radius]
  linarith

abbrev domain (n : ℕ) (δ : ℝ) := TopCat.of
  ({z : tube n | ‖(endpoint z.val : Ambient n) - point z.val.2‖ < δ} × ClosedInterval)

variable (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε)

theorem outer_distance_lt (z : domain n (radius F hε)) :
    ‖(endpoint z.1.val.val : Ambient n) - point z.1.val.val.2‖ < arcRadius F hε := by
  have hz := z.1.property
  have hr := (arcRadius_spec F hε).1
  change ‖(endpoint z.1.val.val : Ambient n) - point z.1.val.val.2‖ < arcRadius F hε / 8 at hz
  linarith

theorem right_distance_lt (z : domain n (radius F hε)) :
    ‖(endpoint (NativeSelfCutSegmentClocks.firstHalf z.2, right z.1.val) : Ambient n) -
      point (right z.1.val)‖ < arcRadius F hε := by
  have h := ShortArcUniformEndpoint.right_arc_distance z.1.val z.2
  have hz := z.1.property
  have hr := (arcRadius_spec F hε).1
  change ‖(endpoint z.1.val.val : Ambient n) - point z.1.val.val.2‖ < arcRadius F hε / 8 at hz
  linarith

theorem left_distance_lt (z : domain n (radius F hε)) :
    ‖(endpoint (NativeSelfCutSegmentClocks.secondHalf z.2, left z.1.val) : Ambient n) -
      point (left z.1.val)‖ < arcRadius F hε := by
  have h := ShortArcUniformEndpoint.left_arc_distance z.1.val z.2
  have hz := z.1.property
  have hr := (arcRadius_spec F hε).1
  change ‖(endpoint z.1.val.val : Ambient n) - point z.1.val.val.2‖ < arcRadius F hε / 8 at hz
  linarith

def rightInput (z : domain n (radius F hε)) : tube n :=
  ⟨(NativeSelfCutSegmentClocks.firstHalf z.2, right z.1.val),
    (right_distance_lt F hε z).trans_le (arcRadius_spec F hε).2.1⟩

def leftInput (z : domain n (radius F hε)) : tube n :=
  ⟨(NativeSelfCutSegmentClocks.secondHalf z.2, left z.1.val),
    (left_distance_lt F hε z).trans_le (arcRadius_spec F hε).2.1⟩

theorem continuous_rightInput : Continuous (rightInput F hε) := by
  exact ((NativeSelfCutSegmentClocks.continuous_firstHalf.comp continuous_snd).prodMk
    (continuous_right.comp (continuous_subtype_val.comp continuous_fst))).subtype_mk _

theorem continuous_leftInput : Continuous (leftInput F hε) := by
  exact ((NativeSelfCutSegmentClocks.continuous_secondHalf.comp continuous_snd).prodMk
    (continuous_left.comp (continuous_subtype_val.comp continuous_fst))).subtype_mk _

theorem right_tested_short (z : domain n (radius F hε)) :
    SobolevLength.length F (left (rightInput F hε z)) < 2 * ε := by
  let w : NativeClosingArcNestedCut.domain n := ⟨(z.1.val, z.2), (rightInput F hε z).property⟩
  have h₀ := (arcRadius_spec F hε).2.2 (forward z.1.val) (outer_distance_lt F hε z)
  have hdist : ‖(point (rightInput F hε z).val.2 : Ambient n) - endpoint (rightInput F hε z).val‖ <
      arcRadius F hε := by
    rw [norm_sub_rev]
    exact right_distance_lt F hε z
  have h₁ := (arcRadius_spec F hε).2.2 (backward (rightInput F hε z)) hdist
  exact NativeClosingArcNestedCut.tested_length_lt F w h₀ h₁

theorem left_retained_short (z : domain n (radius F hε)) :
    SobolevLength.length F (right (leftInput F hε z)) < 2 * ε := by
  let w : NativeClosingArcRetainedCut.domain n := ⟨(z.1.val, z.2), (leftInput F hε z).property⟩
  have h₀ := (arcRadius_spec F hε).2.2 (forward (leftInput F hε z)) (left_distance_lt F hε z)
  have hdist : ‖(point z.1.val.val.2 : Ambient n) - endpoint z.1.val.val‖ < arcRadius F hε := by
    rw [norm_sub_rev]
    exact outer_distance_lt F hε z
  have h₁ := (arcRadius_spec F hε).2.2 (backward z.1.val) hdist
  exact NativeClosingArcRetainedCut.retained_length_lt F w h₀ h₁

end
end Finsler.NativeClosingArcUniformTube
