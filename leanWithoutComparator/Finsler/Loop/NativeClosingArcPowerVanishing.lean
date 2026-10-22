module

public import Finsler.Loop.NativeClosingArcUniformTube
public import Finsler.Loop.NativeGHPowerPositiveSupport

/-! ONE genuine near-tube, selected BEFORE all powers, makes BOTH
actual short closed-cut outputs invisible to EVERY original GH power.
Actual normalized representatives of those SAME powers pull back to
ZERO literally on the entire time-parametrized arc-cut families. -/
@[expose] public section
namespace Finsler.NativeClosingArcPowerVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.IntervalSobolev Finsler.H1SelfCutNeighborhood Finsler.StrictLengthEnergyBridge
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def supportScale : ℝ := (NativeGHPowerPositiveSupport.exists_linear_power_zero m hm F).choose

theorem support_pos : 0 < supportScale m hm F :=
  (NativeGHPowerPositiveSupport.exists_linear_power_zero m hm F).choose_spec.1

theorem small_power_zero (r : ℕ) :
    (cohPullback (LengthFilteredLoopRotation.full F (supportScale m hm F))
      (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 := by
  apply CanonicalGHLengthSupport.restriction_zero_mono F (NativeGHPowers.degree m r)
    (NativeGHPowers.power m r)
    (show supportScale m hm F ≤ ((r : ℝ) + 1) * supportScale m hm F from by
      nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r), support_pos m hm F])
  exact (NativeGHPowerPositiveSupport.exists_linear_power_zero m hm F).choose_spec.2 r

def radius : ℝ := NativeClosingArcUniformTube.radius F
  (show 0 < supportScale m hm F / 2 from div_pos (support_pos m hm F) (by norm_num))

theorem radius_pos : 0 < radius m hm F := NativeClosingArcUniformTube.radius_pos F _

abbrev domain := NativeClosingArcUniformTube.domain (m + 1) (radius m hm F)

def rightTested : domain m hm F ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => left (NativeClosingArcUniformTube.rightInput F
    (show 0 < supportScale m hm F / 2 from div_pos (support_pos m hm F) (by norm_num)) z),
    continuous_left.comp (NativeClosingArcUniformTube.continuous_rightInput F _)⟩

def leftRetained : domain m hm F ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => right (NativeClosingArcUniformTube.leftInput F
    (show 0 < supportScale m hm F / 2 from div_pos (support_pos m hm F) (by norm_num)) z),
    continuous_right.comp (NativeClosingArcUniformTube.continuous_leftInput F _)⟩

theorem right_short (z : domain m hm F) :
    SobolevLength.length F (rightTested m hm F z) < supportScale m hm F := by
  have h := NativeClosingArcUniformTube.right_tested_short F
    (show 0 < supportScale m hm F / 2 from div_pos (support_pos m hm F) (by norm_num)) z
  exact h.trans_eq (by ring)

theorem left_short (z : domain m hm F) :
    SobolevLength.length F (leftRetained m hm F z) < supportScale m hm F := by
  have h := NativeClosingArcUniformTube.left_retained_short F
    (show 0 < supportScale m hm F / 2 from div_pos (support_pos m hm F) (by norm_num)) z
  exact h.trans_eq (by ring)

def rightLength : domain m hm F ⟶ lengthSpace F (supportScale m hm F) := TopCat.ofHom
  ⟨fun z => ⟨rightTested m hm F z, right_short m hm F z⟩,
    (rightTested m hm F).hom.continuous.subtype_mk _⟩

def leftLength : domain m hm F ⟶ lengthSpace F (supportScale m hm F) := TopCat.ofHom
  ⟨fun z => ⟨leftRetained m hm F z, left_short m hm F z⟩,
    (leftRetained m hm F).hom.continuous.subtype_mk _⟩

theorem right_factor : rightLength m hm F ≫ LengthFilteredLoopRotation.full F (supportScale m hm F) =
    rightTested m hm F := rfl

theorem left_factor : leftLength m hm F ≫ LengthFilteredLoopRotation.full F (supportScale m hm F) =
    leftRetained m hm F := rfl

theorem right_power_zero (r : ℕ) :
    (cohPullback (rightTested m hm F) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 := by
  rw [← right_factor, Cup.pullback_comp, small_power_zero, map_zero]

theorem left_power_zero (r : ℕ) :
    (cohPullback (leftRetained m hm F) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 := by
  rw [← left_factor, Cup.pullback_comp, small_power_zero, map_zero]

def powerCocycle (r : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m r) :=
  NormalizedRelativeRepresentative.cocycle (Loops (m + 1))
    (SelfCutOscillation.short F (supportScale m hm F)) (NativeGHPowers.degree m r)
    (NativeGHPowers.power m r) (small_power_zero m hm F r)

theorem powerCocycle_closed (r : ℕ) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m r) (powerCocycle m hm F r) = 0 :=
  NormalizedRelativeRepresentative.cocycle_closed _ _ _ _ _

theorem powerCocycle_normalized (r : ℕ) :
    AlgebraicTopology.DoldKan.DegeneraciesVanish
      (X := SingularNormalization.linearization (Loops (m + 1))) (powerCocycle m hm F r) :=
  NormalizedRelativeRepresentative.cocycle_normalized _ _ _ _ _

theorem powerCocycle_class (r : ℕ) :
    CochainClass.classOf (cochainCxZMod2 (Loops (m + 1))) (NativeGHPowers.degree m r)
      (powerCocycle m hm F r) (powerCocycle_closed m hm F r) = NativeGHPowers.power m r :=
  NormalizedRelativeRepresentative.cocycle_class _ _ _ _ _
    (by have h := NativeGHPowers.degree_ge m r; omega)

theorem powerCocycle_supported (r : ℕ) :
    cochainPullback (LengthFilteredLoopRotation.full F (supportScale m hm F)) (NativeGHPowers.degree m r)
      (powerCocycle m hm F r) = 0 :=
  NormalizedRelativeRepresentative.cocycle_supported _ _ _ _ _

theorem right_literal_zero (r : ℕ) :
    cochainPullback (rightTested m hm F) (NativeGHPowers.degree m r) (powerCocycle m hm F r) = 0 := by
  rw [← right_factor, pullback_comp, powerCocycle_supported]
  change (push (rightLength m hm F)).f (NativeGHPowers.degree m r) ≫ 0 = 0
  exact comp_zero

theorem left_literal_zero (r : ℕ) :
    cochainPullback (leftRetained m hm F) (NativeGHPowers.degree m r) (powerCocycle m hm F r) = 0 := by
  rw [← left_factor, pullback_comp, powerCocycle_supported]
  change (push (leftLength m hm F)).f (NativeGHPowers.degree m r) ≫ 0 = 0
  exact comp_zero

end
end Finsler.NativeClosingArcPowerVanishing
