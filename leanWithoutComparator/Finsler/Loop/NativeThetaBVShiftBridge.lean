module

public import Finsler.Loop.NativeGHNearOptimalDetection
public import Finsler.Loop.NativeThetaGHShiftShortcut

/-! Feed ACTUAL near-optimal GH detectors into ACTUAL filtered BV
without increasing length. A generator-identification premise at one
of every two consecutive powers implies the fixed shift d=2, hence
uniform same-cut bounds. That BV premise is NOT asserted proved. -/
@[expose] public section
namespace Finsler.NativeThetaBVShiftBridge
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

theorem degree_match (m r : ℕ) : NativeGHPowers.degree m (r + 1) + 1 = NativeThetaPowers.degree m r := by
  rw [NativeGHPowers.degree_formula, NativeThetaPowers.degree_formula]
  ring

private theorem push_cast {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (z : homologyZMod2 X i) :
    (homologyPushZMod2 f j).hom ((eqToHom (congrArg (homologyZMod2 X) h)).hom z) =
      (eqToHom (congrArg (homologyZMod2 Y) h)).hom ((homologyPushZMod2 f i).hom z) := by
  subst j
  rfl

def alignedBV (m r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))) :
    homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) :=
  (eqToHom (congrArg (homologyZMod2 (Loops (m + 1))) (degree_match m r))).hom
    ((H1LoopRotation.BV (m + 1) (NativeGHPowers.degree m (r + 1))).hom z)

def filteredBV (m : ℕ) (F : ReversibleMetric (m + 1)) (r : ℕ) (a : ℝ)
    (z : homologyZMod2 (lengthSpace F a) (NativeGHPowers.degree m (r + 1))) :
    homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r) :=
  (eqToHom (congrArg (homologyZMod2 (lengthSpace F a)) (degree_match m r))).hom
    ((LengthFilteredLoopRotation.BV F a (NativeGHPowers.degree m (r + 1))).hom z)

theorem filteredBV_full (m : ℕ) (F : ReversibleMetric (m + 1)) (r : ℕ) (a : ℝ)
    (z : homologyZMod2 (lengthSpace F a) (NativeGHPowers.degree m (r + 1))) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeThetaPowers.degree m r)).hom
      (filteredBV m F r a z) = alignedBV m r
        ((homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
          (NativeGHPowers.degree m (r + 1))).hom z) := by
  unfold filteredBV alignedBV
  rw [push_cast (LengthFilteredLoopRotation.full F a) (degree_match m r)]
  exact congrArg (eqToHom (congrArg (homologyZMod2 (Loops (m + 1))) (degree_match m r))).hom
    (ConcreteCategory.congr_hom (LengthFilteredLoopRotation.BV_full F a (NativeGHPowers.degree m (r + 1))) z).symm

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def detectsTheta (r : ℕ) : Prop :=
  ∀ z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)),
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))).hom
      (NativeGHPowers.power m (r + 1)) z = 1 →
    alignedBV m r z = NativeThetaPowers.fullPower m hm F P v₀ r

theorem lift_above_of_BV (r : ℕ) (hBV : detectsTheta m hm F P v₀ r)
    {a : ℝ} (ha : NativeGHSpectralSupport.level m F (r + 1) < a) :
    a ∈ NativeThetaSpectralLength.lifts m hm F P v₀ r := by
  obtain ⟨z, hz⟩ := NativeGHNearOptimalDetection.detection_above m hm F P v₀ (r + 1) ha
  exact ⟨filteredBV m F r a z, (filteredBV_full m F r a z).trans (hBV _ hz)⟩

theorem level_le_of_BV (r : ℕ) (hBV : detectsTheta m hm F P v₀ r) :
    NativeThetaSpectralLength.level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + 1) := by
  by_contra h
  have ha := lift_above_of_BV m hm F P v₀ r hBV
    (show NativeGHSpectralSupport.level m F (r + 1) <
      (NativeThetaSpectralLength.level m hm F P v₀ r + NativeGHSpectralSupport.level m F (r + 1)) / 2 by linarith)
  have hl := NativeThetaSpectralLength.level_le_lift m hm F P v₀ r ha
  linarith

theorem shift_two_of_alternating_BV
    (hBV : ∀ r, detectsTheta m hm F P v₀ r ∨ detectsTheta m hm F P v₀ (r + 1)) (r : ℕ) :
    NativeThetaSpectralLength.level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + 2) := by
  obtain ⟨L, hLpos, hL⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
  have hs : 0 ≤ NativeGHSpectralSupport.level m F 0 := by
    have h := NativeGHSpectralSupport.primitive_lower m hm F P v₀ 0 hL
    simp only [Nat.cast_zero, zero_add, one_mul] at h
    exact hLpos.le.trans h
  rcases hBV r with hr | hr
  · have h := NativeGHSpectralSupport.level_add m hm F P v₀ (r + 1) 0
    simp only [Nat.add_zero] at h
    linarith [level_le_of_BV m hm F P v₀ r hr]
  · have h := NativeThetaSpectralStep.level_succ_lower m hm F P v₀ r
    linarith [level_le_of_BV m hm F P v₀ (r + 1) hr]

theorem gap_le_of_alternating_BV
    (hBV : ∀ r, detectsTheta m hm F P v₀ r ∨ detectsTheta m hm F P v₀ (r + 1)) (r : ℕ) :
    NativeThetaGHSpectralGap.gap m hm F P v₀ r ≤ 2 * NativeThetaSpectralLength.level m hm F P v₀ 0 := by
  exact NativeThetaGHShiftShortcut.gap_le_of_shift m hm F P v₀ 2
    (shift_two_of_alternating_BV m hm F P v₀ hBV) r

end
end Finsler.NativeThetaBVShiftBridge
