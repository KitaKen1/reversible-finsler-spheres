module

public import Finsler.Loop.NativeGHBlockSlope

/-! The actual spectral support threshold of EACH original GH power is
finite and positive. It is a supremum of actual restriction-zero lengths,
not an extra geometric hypothesis. No endpoint attainment is assumed. -/
@[expose] public section
namespace Finsler.NativeGHSpectralSupport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

def supports (m : ℕ) (F : ReversibleMetric (m + 1)) (r : ℕ) : Set ℝ :=
  {R | (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom
    (NativeGHPowers.power m r) = 0}

def level (m : ℕ) (F : ReversibleMetric (m + 1)) (r : ℕ) : ℝ := sSup (supports m F r)

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

include hm in
theorem supports_nonempty (r : ℕ) : (supports m F r).Nonempty := by
  obtain ⟨L, hL, hz⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
  exact ⟨0, NativeGHPowerSharpSupport.power_below m hm F hz r (by positivity)⟩

include hm P v₀ in
theorem supports_bddAbove (r : ℕ) : BddAbove (supports m F r) := by
  refine ⟨NativeThetaPowers.bound m F P v₀ r, ?_⟩
  intro B hB
  exact NativeHighPowerFilteredCut.support_le_input m F r hB hm P v₀
    (NativeThetaPowers.filteredPower m hm F P v₀ r) rfl

include hm P v₀ in
theorem support_le_level (r : ℕ) {B : ℝ} (hB : B ∈ supports m F r) : B ≤ level m F r :=
  le_csSup (supports_bddAbove m hm F P v₀ r) hB

include hm in
theorem restriction_below (r : ℕ) {R : ℝ} (hR : R < level m F r) : R ∈ supports m F r := by
  obtain ⟨B, hB, hRB⟩ := exists_lt_of_lt_csSup (supports_nonempty m hm F r) hR
  exact CanonicalGHLengthSupport.restriction_zero_mono F (NativeGHPowers.degree m r)
    (NativeGHPowers.power m r) hRB.le hB

include hm P v₀ in
theorem le_level_of_below (r : ℕ) {B : ℝ} (hB : ∀ R : ℝ, R < B → R ∈ supports m F r) :
    B ≤ level m F r := by
  by_contra h
  have hz := hB ((B + level m F r) / 2) (by linarith)
  have hl := support_le_level m hm F P v₀ r hz
  linarith

include hm in
theorem level_le_lift (r : ℕ) {a : ℝ}
    (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m r)).hom z = NativeThetaPowers.fullPower m hm F P v₀ r) :
    level m F r ≤ a := by
  exact csSup_le (supports_nonempty m hm F r)
    (fun B hB => NativeHighPowerFilteredCut.support_le_input m F r hB hm P v₀ z hz)

include hm in
theorem level_le_primitive_lift (r : ℕ) {a : ℝ} (ha : 0 < a)
    (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m 0))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m 0)).hom z = NativeThetaPowers.fullPower m hm F P v₀ 0) :
    level m F r ≤ ((r : ℝ) + 1) * a := by
  exact csSup_le (supports_nonempty m hm F r)
    (fun B hB => NativeGHBlockSlope.block_support_le_primitive_lift m hm F r hB P v₀ ha z hz)

include hm P v₀ in
theorem primitive_lower (r : ℕ) {L : ℝ}
    (hL : (cohPullback (LengthFilteredLoopRotation.full F L) m).hom
      (MeridianLoopClass.H1TransgressionClass m) = 0) :
    ((r : ℝ) + 1) * L ≤ level m F r :=
  le_level_of_below m hm F P v₀ r
    (fun _R hR => NativeGHPowerSharpSupport.power_below m hm F hL r hR)

include hm P v₀ in
theorem level_add (a b : ℕ) : level m F a + level m F b ≤ level m F (a + b + 1) := by
  apply le_level_of_below m hm F P v₀ (a + b + 1)
  intro R hR
  let ε := (level m F a + level m F b - R) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ha := restriction_below m hm F a (by linarith : level m F a - ε < level m F a)
  have hb := restriction_below m hm F b (by linarith : level m F b - ε < level m F b)
  exact NativeGHPowerMultiplication.support_add m hm F a b ha hb
    (by dsimp [ε]; linarith)

end
end Finsler.NativeGHSpectralSupport
