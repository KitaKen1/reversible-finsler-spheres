module

public import Finsler.Loop.NativeGHPowerPositiveSupport
public import Finsler.Loop.NativeHighPowerFilteredCut

/-! Keep the FULL primitive support scale. Arbitrarily small slack at
each finite induction step gives vanishing below every R<(r+1)*L;
no factor-of-two loss and no linearly accumulated safety gap. -/
@[expose] public section
namespace Finsler.NativeGHPowerSharpSupport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) {L : ℝ}
  (hL : (cohPullback (LengthFilteredLoopRotation.full F L) m).hom
    (MeridianLoopClass.H1TransgressionClass m) = 0)
include hm hL

theorem power_below (r : ℕ) {R : ℝ} (hR : R < ((r : ℝ) + 1) * L) :
    (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r) = 0 := by
  induction r generalizing R with
  | zero =>
    exact CanonicalGHLengthSupport.restriction_zero_mono F m
      (MeridianLoopClass.H1TransgressionClass m) (by simpa using hR.le) hL
  | succ r ih =>
    let M := (R - L + ((r : ℝ) + 1) * L) / 2
    have hM : M < ((r : ℝ) + 1) * L := by dsimp [M]; push_cast at hR; nlinarith
    have hRM : R < L + M := by dsimp [M]; push_cast at hR; nlinarith
    exact CanonicalGHLengthSupport.product_restriction_zero (by omega) F m
      (NativeGHPowers.degree m r) (MeridianLoopClass.H1TransgressionClass m)
      (NativeGHPowers.power m r) hL (ih hM) hRM

theorem power_with_slack (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (cohPullback (LengthFilteredLoopRotation.full F (((r : ℝ) + 1) * L - δ))
      (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) = 0 :=
  power_below m hm F hL r (by linarith)

theorem theta_lift_lower (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) {a : ℝ}
    (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m r)).hom z = NativeThetaPowers.fullPower m hm F P v₀ r) :
    ((r : ℝ) + 1) * L ≤ a := by
  by_contra h
  let R := (a + ((r : ℝ) + 1) * L) / 2
  have hR : R < ((r : ℝ) + 1) * L := by dsimp [R]; linarith
  have ha := NativeHighPowerFilteredCut.support_le_input m F r (power_below m hm F hL r hR)
    hm P v₀ z hz
  dsimp [R] at ha
  linarith

omit hL in
theorem exists_full_positive_scale : ∃ L : ℝ, 0 < L ∧ ∀ (r : ℕ) (R : ℝ),
    R < ((r : ℝ) + 1) * L →
    (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r) = 0 := by
  obtain ⟨L, hLpos, hLzero⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
  exact ⟨L, hLpos, fun r R hR => power_below m hm F hLzero r hR⟩

end
end Finsler.NativeGHPowerSharpSupport
