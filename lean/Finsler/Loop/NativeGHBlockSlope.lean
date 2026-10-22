module

public import Finsler.Loop.NativeGHBlockSupport
public import Finsler.Loop.NativeThetaTightRepresentatives

/-! A fixed supported GH block gives its full average slope with only one
power-independent remainder constant. Any lift of the SAME primitive Theta
bounds this average from above. The inequality need not be an equality. -/
@[expose] public section
namespace Finsler.NativeGHBlockSlope
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def slope (b : ℕ) (B : ℝ) : ℝ := B / ((b : ℝ) + 1)
def remainder (b : ℕ) (B L : ℝ) : ℝ := ((b : ℝ) + 1) * |slope b B - L|

theorem remainder_nonneg (b : ℕ) (B L : ℝ) : 0 ≤ remainder b B L := by
  unfold remainder
  positivity

theorem slope_positive (b : ℕ) {B : ℝ} (hB : 0 < B) : 0 < slope b B := by
  unfold slope
  positivity

theorem quotient_lower (b r : ℕ) (B L : ℝ) :
    ((r : ℝ) + 1) * slope b B - remainder b B L ≤
      (r / (b + 1) : ℕ) * B + ((r % (b + 1) : ℕ) + 1 : ℝ) * L := by
  have hd : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have hμ : ((b : ℝ) + 1) * slope b B = B := by
    unfold slope
    field_simp
  have hs : (r : ℝ) = (r / (b + 1) : ℕ) * ((b : ℝ) + 1) + (r % (b + 1) : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' r (b + 1)).symm
  have ht : ((r % (b + 1) : ℕ) : ℝ) + 1 ≤ (b : ℝ) + 1 := by
    have h : r % (b + 1) + 1 ≤ b + 1 := Nat.succ_le_of_lt (Nat.mod_lt r (Nat.succ_pos b))
    exact_mod_cast h
  have ht0 : (0 : ℝ) ≤ ((r % (b + 1) : ℕ) : ℝ) + 1 := by positivity
  have he : ((r : ℝ) + 1) * slope b B =
      (r / (b + 1) : ℕ) * B + (((r % (b + 1) : ℕ) : ℝ) + 1) * slope b B := by
    rw [hs]
    calc
      _ = (r / (b + 1) : ℕ) * (((b : ℝ) + 1) * slope b B) +
        (((r % (b + 1) : ℕ) : ℝ) + 1) * slope b B := by ring
      _ = _ := by rw [hμ]
  have h1 := mul_le_mul_of_nonneg_left (le_abs_self (slope b B - L)) ht0
  have h2 := mul_le_mul_of_nonneg_right ht (abs_nonneg (slope b B - L))
  dsimp [remainder]
  rw [he]
  nlinarith

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (b : ℕ) {B L : ℝ}
  (hB : (cohPullback (LengthFilteredLoopRotation.full F B) (NativeGHPowers.degree m b)).hom
    (NativeGHPowers.power m b) = 0)
  (hL : (cohPullback (LengthFilteredLoopRotation.full F L) m).hom
    (MeridianLoopClass.H1TransgressionClass m) = 0)

include hm hB hL in
theorem power_below (r : ℕ) {R : ℝ}
    (hR : R < ((r : ℝ) + 1) * slope b B - remainder b B L) :
    (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r) = 0 :=
  NativeGHBlockSupport.quotient_below m hm F b hB hL r
    (lt_of_lt_of_le hR (quotient_lower b r B L))

include hm hB hL in
theorem power_with_slack (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (cohPullback (LengthFilteredLoopRotation.full F
      (((r : ℝ) + 1) * slope b B - remainder b B L - δ)) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r) = 0 :=
  power_below m hm F b hB hL r (by linarith)

include hB in
theorem block_support_le_primitive_lift (P : Sphere (m + 1)) (v₀ : equator P)
    {a : ℝ} (ha : 0 < a)
    (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m 0))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m 0)).hom z = NativeThetaPowers.fullPower m hm F P v₀ 0) :
    B ≤ ((b : ℝ) + 1) * a := by
  by_contra h
  have hδ : 0 < (B - ((b : ℝ) + 1) * a) / 2 := by linarith
  obtain ⟨w, hw⟩ := NativeThetaTightRepresentatives.exists_tight_lift m F z hm P v₀ ha hz b hδ
  have hbound := NativeHighPowerFilteredCut.support_le_input m F b hB hm P v₀ w hw
  linarith

include hB in
theorem slope_le_primitive_lift (P : Sphere (m + 1)) (v₀ : equator P)
    {a : ℝ} (ha : 0 < a)
    (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m 0))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m 0)).hom z = NativeThetaPowers.fullPower m hm F P v₀ 0) :
    slope b B ≤ a := by
  unfold slope
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (b : ℝ) + 1)).2
  have h := block_support_le_primitive_lift m hm F b hB P v₀ ha z hz
  nlinarith

end
end Finsler.NativeGHBlockSlope
