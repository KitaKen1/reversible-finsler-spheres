module

public import Finsler.Loop.NativeThetaGHImageWindow

/-! Isolate the remaining exact-rate lower deficit. Its uniform bound
is equivalent to a uniform absolute deviation for the SAME Theta tower.
An ACTUAL finite block whose spectral average attains beta is a sufficient
certificate, without assuming its support endpoint is attained. Existence
of such a block is not asserted. -/
@[expose] public section
namespace Finsler.NativeThetaGHRateDeficit
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)
include hm P v₀

theorem gh_level_positive (r : ℕ) : 0 < NativeGHSpectralSupport.level m F r := by
  obtain ⟨L, hL, hz⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
  exact (mul_pos (by positivity : (0 : ℝ) < (r : ℝ) + 1) hL).trans_le
    (NativeGHSpectralSupport.primitive_lower m hm F P v₀ r hz)

theorem block_level_lower (b k t : ℕ) :
    (k : ℝ) * NativeGHSpectralSupport.level m F b + NativeGHSpectralSupport.level m F t ≤
      NativeGHSpectralSupport.level m F (k * (b + 1) + t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := NativeGHSpectralSupport.level_add m hm F P v₀ b (k * (b + 1) + t)
    rw [show b + (k * (b + 1) + t) + 1 = (k + 1) * (b + 1) + t by ring] at h
    push_cast
    nlinarith

theorem quotient_level_lower (b r : ℕ) :
    ((r / (b + 1) : ℕ) : ℝ) * NativeGHSpectralSupport.level m F b ≤
      NativeGHSpectralSupport.level m F r := by
  have h := block_level_lower m hm F P v₀ b (r / (b + 1)) (r % (b + 1))
  rw [Nat.div_add_mod' r (b + 1)] at h
  linarith [gh_level_positive m hm F P v₀ (r % (b + 1))]

/-- A finite spectral certificate suffices; no support at the endpoint
and no regrouping of Theta products are needed. -/
theorem critical_band_of_block_attains (b : ℕ)
    (hb : NativeGHOptimalRate.average m F b = NativeGHOptimalRate.rate m F) (r : ℕ) :
    ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F -
      ((b : ℝ) + 1) * NativeGHOptimalRate.rate m F ≤ NativeGHSpectralSupport.level m F r := by
  have h := NativeGHBlockSlope.quotient_lower b r (NativeGHSpectralSupport.level m F b) 0
  have hp := NativeGHOptimalRate.rate_positive m hm F P v₀
  have he : NativeGHBlockSlope.slope b (NativeGHSpectralSupport.level m F b) =
      NativeGHOptimalRate.rate m F := hb
  simp only [NativeGHBlockSlope.remainder, he, sub_zero, abs_of_pos hp, mul_zero, add_zero] at h
  exact h.trans (quotient_level_lower m hm F P v₀ b r)

theorem support_band_of_block_attains (b : ℕ)
    (hb : NativeGHOptimalRate.average m F b = NativeGHOptimalRate.rate m F)
    (r : ℕ) {a : ℝ}
    (ha : a < ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F -
      ((b : ℝ) + 1) * NativeGHOptimalRate.rate m F) :
    a ∈ NativeGHSpectralSupport.supports m F r :=
  NativeGHSpectralSupport.restriction_below m hm F r
    (ha.trans_le (critical_band_of_block_attains m hm F P v₀ b hb r))

theorem common_deviation_of_critical_band {C : ℝ}
    (h : ∀ r : ℕ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C ≤
      NativeGHSpectralSupport.level m F r) (r : ℕ) :
    |NativeGHSpectralSupport.level m F r - ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F| ≤ C ∧
    |NativeThetaSpectralLength.level m hm F P v₀ r -
      ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F| ≤ max C (NativeGHOptimalRate.rate m F) := by
  have hs := NativeThetaGHCommonRate.gh_level_upper m hm F P v₀ r
  have ht := NativeThetaGHCommonRate.theta_level_upper m hm F P v₀ r
  have hst := NativeThetaSpectralLength.gh_le_level m hm F P v₀ r
  have hC : 0 ≤ C := by linarith [h r]
  have hcmax := le_max_left C (NativeGHOptimalRate.rate m F)
  have hbmax := le_max_right C (NativeGHOptimalRate.rate m F)
  exact ⟨abs_le.mpr ⟨by linarith [h r], by linarith⟩,
    abs_le.mpr ⟨by linarith [h r], by linarith⟩⟩

theorem critical_band_of_theta_deviation {D : ℝ}
    (h : ∀ r : ℕ, |NativeThetaSpectralLength.level m hm F P v₀ r -
      ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F| ≤ D) (r : ℕ) :
    ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F -
      (D + NativeThetaSpectralLength.level m hm F P v₀ 0) ≤ NativeGHSpectralSupport.level m F r := by
  have hl := (abs_le.mp (h r)).1
  have hg := NativeBVFixedShift.uniform_gap m hm F P v₀ r
  unfold NativeThetaGHSpectralGap.gap at hg
  linarith

theorem bounded_deviation_iff_critical_band :
    (∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℕ, |NativeThetaSpectralLength.level m hm F P v₀ r -
      ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F| ≤ D) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C ≤
      NativeGHSpectralSupport.level m F r) := by
  constructor
  · rintro ⟨D, hD, h⟩
    exact ⟨D + NativeThetaSpectralLength.level m hm F P v₀ 0,
      add_nonneg hD (NativeThetaSpectralLength.level_positive m hm F P v₀ 0).le,
      critical_band_of_theta_deviation m hm F P v₀ h⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨max C (NativeGHOptimalRate.rate m F), hC.trans (le_max_left _ _),
      fun r => (common_deviation_of_critical_band m hm F P v₀ h r).2⟩

theorem bounded_deviation_of_block_attains (b : ℕ)
    (hb : NativeGHOptimalRate.average m F b = NativeGHOptimalRate.rate m F) :
    ∀ r : ℕ, |NativeThetaSpectralLength.level m hm F P v₀ r -
      ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F| ≤
        ((b : ℝ) + 1) * NativeGHOptimalRate.rate m F := by
  intro r
  have h := (common_deviation_of_critical_band m hm F P v₀
    (critical_band_of_block_attains m hm F P v₀ b hb) r).2
  have hp := NativeGHOptimalRate.rate_positive m hm F P v₀
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
  rw [max_eq_left (by nlinarith)] at h
  exact h

end
end Finsler.NativeThetaGHRateDeficit
