module

public import Finsler.Loop.NativeOrderedDoubleCutGeometry
public import Finsler.Loop.NativeClosingArcPowerVanishing

/-! On the ACTUAL ordered-time diagonal the common middle loop
is two short closing arcs with a collapsed original restriction.
Use the SAME Stage94 radius, SAME positive support cut and SAME
closed normalized GH-power representatives: no new test class. -/
@[expose] public section
namespace Finsler.NativeOrderedDoubleCutDiagonal
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.H1SelfCutNeighborhood Finsler.NativeOrderedDoubleCutGeometry
open Finsler.BorelLoop Finsler.StrictLengthEnergyBridge Finsler.SmallChainCarrier
open Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def diagonal (n : ℕ) (r : ℝ) : Set (NativeOrderedDoubleCutGeometry.domain n r) :=
  {z | z.val.2.val.1.down = z.val.2.val.2.down}

abbrev diagonalDomain (n : ℕ) (r : ℝ) := TopCat.of (diagonal n r)

def inclusion (n : ℕ) (r : ℝ) : diagonalDomain n r ⟶ NativeOrderedDoubleCutGeometry.domain n r :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem rawMiddle_length_zero {n : ℕ} {r : ℝ} (F : ReversibleMetric n) (z : diagonalDomain n r) :
    H1PathLength.length F (NativeOrderedDoubleCutGeometry.rawMiddle z.val) = 0 := by
  rw [NativeOrderedDoubleCutGeometry.rawMiddle, H1PathLength.length_restrict]
  have ht : ((z.val.val.2.val.1.down : ClosedInterval) : ℝ) = z.val.val.2.val.2.down :=
    congrArg Subtype.val z.property
  rw [ht, intervalIntegral.integral_same]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

theorem radius_le_one : NativeClosingArcPowerVanishing.radius m hm F ≤ 1 :=
  (NativeClosingArcUniformTube.radius_le_eighth F _).trans (by norm_num)

theorem radius_lt_arc : NativeClosingArcPowerVanishing.radius m hm F <
    NativeClosingArcUniformTube.arcRadius F
      (show 0 < NativeClosingArcPowerVanishing.supportScale m hm F / 2 from
        div_pos (NativeClosingArcPowerVanishing.support_pos m hm F) (by norm_num)) := by
  have h := (NativeClosingArcUniformTube.arcRadius_spec F
    (show 0 < NativeClosingArcPowerVanishing.supportScale m hm F / 2 from
      div_pos (NativeClosingArcPowerVanishing.support_pos m hm F) (by norm_num))).1
  change NativeClosingArcUniformTube.arcRadius F _ / 8 < NativeClosingArcUniformTube.arcRadius F _
  linarith

def middleMap : NativeOrderedDoubleCutGeometry.domain (m + 1)
    (NativeClosingArcPowerVanishing.radius m hm F) ⟶ Loops (m + 1) :=
  TopCat.ofHom ⟨NativeOrderedDoubleCutGeometry.middle (radius_le_one m hm F),
    NativeOrderedDoubleCutGeometry.continuous_middle _⟩

theorem middle_short (z : diagonalDomain (m + 1) (NativeClosingArcPowerVanishing.radius m hm F)) :
    SobolevLength.length F (middleMap m hm F z.val) < NativeClosingArcPowerVanishing.supportScale m hm F := by
  let hr := radius_le_one m hm F
  let hε : 0 < NativeClosingArcPowerVanishing.supportScale m hm F / 2 :=
    div_pos (NativeClosingArcPowerVanishing.support_pos m hm F) (by norm_num)
  have h₀ := (NativeClosingArcUniformTube.arcRadius_spec F hε).2.2 (forward (firstCut hr z.val))
    (z.val.property.1.trans (radius_lt_arc m hm F))
  have hdist : ‖(point z.val.val.1 : Ambient (m + 1)) - endpoint (lastCut hr z.val).val‖ <
      NativeClosingArcUniformTube.arcRadius F hε := by
    rw [norm_sub_rev]
    exact z.val.property.2.trans (radius_lt_arc m hm F)
  have h₁ := (NativeClosingArcUniformTube.arcRadius_spec F hε).2.2 (backward (lastCut hr z.val)) hdist
  have he := NativeOrderedDoubleCutGeometry.middle_length hr F z.val
  rw [rawMiddle_length_zero F z, add_zero] at he
  change SobolevLength.length F (NativeOrderedDoubleCutGeometry.middle hr z.val) < _
  change H1PathLength.length F (firstArc hr z.val) < _ at h₀
  change H1PathLength.length F (lastArc hr z.val) < _ at h₁
  linarith

def middleLength : diagonalDomain (m + 1) (NativeClosingArcPowerVanishing.radius m hm F) ⟶
    lengthSpace F (NativeClosingArcPowerVanishing.supportScale m hm F) := TopCat.ofHom
  ⟨fun z => ⟨middleMap m hm F z.val, middle_short m hm F z⟩,
    ((middleMap m hm F).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem middle_factor : middleLength m hm F ≫
    LengthFilteredLoopRotation.full F (NativeClosingArcPowerVanishing.supportScale m hm F) =
      inclusion (m + 1) (NativeClosingArcPowerVanishing.radius m hm F) ≫ middleMap m hm F := rfl

theorem middle_power_zero (r : ℕ) :
    (cohPullback (inclusion (m + 1) (NativeClosingArcPowerVanishing.radius m hm F) ≫ middleMap m hm F)
      (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 := by
  rw [← middle_factor, Cup.pullback_comp, NativeClosingArcPowerVanishing.small_power_zero, map_zero]

theorem middle_literal_zero (r : ℕ) :
    cochainPullback (inclusion (m + 1) (NativeClosingArcPowerVanishing.radius m hm F) ≫ middleMap m hm F)
      (NativeGHPowers.degree m r) (NativeClosingArcPowerVanishing.powerCocycle m hm F r) = 0 := by
  rw [← middle_factor, pullback_comp, NativeClosingArcPowerVanishing.powerCocycle_supported]
  change (push (middleLength m hm F)).f (NativeGHPowers.degree m r) ≫ 0 = 0
  exact comp_zero

end
end Finsler.NativeOrderedDoubleCutDiagonal
