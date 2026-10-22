module

public import Finsler.Loop.NativeThetaGHCommonRate
public import Finsler.Loop.NativeGHHomologyThreshold

/-! Actual finite-length to full-space homology maps in BOTH original
towers. Below the spectral level the map is zero, above it surjective.
The common rate gives a subcritical lower window and an exact-rate upper
window. No endpoint attainment or injectivity at a finite level is used. -/
@[expose] public section
namespace Finsler.NativeThetaGHImageWindow
open CategoryTheory AlgebraicTopology SphereOddDegree Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)
include hm P v₀

theorem theta_map_zero_iff_no_lift (r : ℕ) (a : ℝ) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeThetaPowers.degree m r)).hom = 0 ↔
      a ∉ NativeThetaSpectralLength.lifts m hm F P v₀ r := by
  rw [NativeThetaBVNonzeroCriterion.lifts_iff_exists_nonzero m hm F P v₀ r a]
  constructor
  · intro h ⟨z, hz⟩
    exact hz (by rw [h, LinearMap.zero_apply])
  · intro h
    apply LinearMap.ext
    intro z
    by_contra hz
    exact h ⟨z, hz⟩

theorem theta_map_surjective_iff_lift (r : ℕ) (a : ℝ) :
    Function.Surjective (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m r)).hom ↔ a ∈ NativeThetaSpectralLength.lifts m hm F P v₀ r := by
  constructor
  · intro h
    exact h (NativeThetaPowers.fullPower m hm F P v₀ r)
  · rintro ⟨z, hz⟩ y
    obtain ⟨c, hc⟩ := NativeThetaRankOne.theta_spans m hm F P v₀ r y
    exact ⟨c • z, by rw [map_smul, hz, hc]⟩

theorem theta_map_zero_below (r : ℕ) {a : ℝ}
    (ha : a < NativeThetaSpectralLength.level m hm F P v₀ r) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeThetaPowers.degree m r)).hom = 0 := by
  apply (theta_map_zero_iff_no_lift m hm F P v₀ r a).mpr
  intro h
  exact (not_le_of_gt ha) (NativeThetaSpectralLength.level_le_lift m hm F P v₀ r h)

theorem theta_map_surjective_above (r : ℕ) {a : ℝ}
    (ha : NativeThetaSpectralLength.level m hm F P v₀ r < a) :
    Function.Surjective (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m r)).hom :=
  (theta_map_surjective_iff_lift m hm F P v₀ r a).mpr
    (NativeThetaSpectralLength.lift_above m hm F P v₀ r ha)

include hm P v₀ in
theorem gh_map_surjective_above_line (r : ℕ) {a : ℝ}
    (ha : ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F < a) :
    Function.Surjective (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeGHPowers.degree m r)).hom :=
  NativeGHHomologyThreshold.full_map_surjective_above m hm F P v₀ r
    ((NativeThetaGHCommonRate.gh_level_upper m hm F P v₀ r).trans_lt ha)

theorem theta_map_surjective_above_line (r : ℕ) {a : ℝ}
    (ha : ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + NativeGHOptimalRate.rate m F < a) :
    Function.Surjective (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m r)).hom :=
  (theta_map_surjective_iff_lift m hm F P v₀ r a).mpr
    (NativeThetaGHCommonRate.theta_lift_above_line m hm F P v₀ r ha)

theorem common_zero_window {σ : ℝ} (hσ : σ < NativeGHOptimalRate.rate m F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (a : ℝ), a < ((r : ℝ) + 1) * σ - C →
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom = 0 ∧
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeThetaPowers.degree m r)).hom = 0 := by
  obtain ⟨C, hC, h⟩ := NativeGHOptimalRate.exists_level_band m hm F P v₀ hσ
  refine ⟨C, hC, ?_⟩
  intro r a ha
  have hs := ha.trans_le (h r)
  exact ⟨NativeGHHomologyThreshold.full_map_zero_below m hm F P v₀ r hs,
    theta_map_zero_below m hm F P v₀ r
      (hs.trans_le (NativeThetaSpectralLength.gh_le_level m hm F P v₀ r))⟩

/-- One constant precedes every power and every sublevel in this window.
The lower slope is strictly subcritical; the upper slope is exactly beta. -/
theorem common_window {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (a : ℝ),
    (a < ((r : ℝ) + 1) * (NativeGHOptimalRate.rate m F - ε) - C →
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom = 0 ∧
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeThetaPowers.degree m r)).hom = 0) ∧
    (((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + NativeGHOptimalRate.rate m F < a →
      Function.Surjective (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
        (NativeGHPowers.degree m r)).hom ∧
      Function.Surjective (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
        (NativeThetaPowers.degree m r)).hom) := by
  obtain ⟨C, hC, h⟩ := common_zero_window m hm F P v₀
    (show NativeGHOptimalRate.rate m F - ε < NativeGHOptimalRate.rate m F by linarith)
  refine ⟨C, hC, fun r a => ⟨h r a, ?_⟩⟩
  intro ha
  have hp := NativeGHOptimalRate.rate_positive m hm F P v₀
  exact ⟨gh_map_surjective_above_line m hm F P v₀ r (by linarith),
    theta_map_surjective_above_line m hm F P v₀ r ha⟩

end
end Finsler.NativeThetaGHImageWindow
