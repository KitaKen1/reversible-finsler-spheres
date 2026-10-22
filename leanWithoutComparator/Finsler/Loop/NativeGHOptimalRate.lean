module

public import Finsler.Loop.NativeGHSpectralSupport

/-! A canonical positive, finite optimal GH slope, defined from the actual
support thresholds. Every smaller slope has an ACTUAL finite supported
block witness and a uniform-in-power remainder. Neither a better-than-
primitive optimal slope nor equality with Theta spectral lengths is assumed. -/
@[expose] public section
namespace Finsler.NativeGHOptimalRate
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
open Finsler.NativeGHSpectralSupport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

def average (m : ℕ) (F : ReversibleMetric (m + 1)) (r : ℕ) : ℝ :=
  level m F r / ((r : ℝ) + 1)

def rate (m : ℕ) (F : ReversibleMetric (m + 1)) : ℝ :=
  sSup (Set.range (average m F))

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem average_le_primitive_lift (r : ℕ) {a : ℝ} (ha : 0 < a)
    (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m 0))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m 0)).hom z = NativeThetaPowers.fullPower m hm F P v₀ 0) :
    average m F r ≤ a := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 1)).2
  have h := level_le_primitive_lift m hm F P v₀ r ha z hz
  nlinarith

include hm P v₀ in
theorem averages_bddAbove : BddAbove (Set.range (average m F)) := by
  refine ⟨NativeThetaLengthCut.bound F P v₀, ?_⟩
  rintro y ⟨r, rfl⟩
  exact average_le_primitive_lift m hm F P v₀ r (NativeThetaLengthCut.bound_positive F P v₀)
    (NativeThetaLengthCut.input m (by omega) F P v₀) rfl

include hm P v₀ in
theorem average_le_rate (r : ℕ) : average m F r ≤ rate m F :=
  le_csSup (averages_bddAbove m hm F P v₀) ⟨r, rfl⟩

theorem rate_le_primitive_lift {a : ℝ} (ha : 0 < a)
    (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m 0))
    (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m 0)).hom z = NativeThetaPowers.fullPower m hm F P v₀ 0) :
    rate m F ≤ a := by
  apply csSup_le (Set.range_nonempty (average m F))
  rintro y ⟨r, rfl⟩
  exact average_le_primitive_lift m hm F P v₀ r ha z hz

include hm P v₀ in
theorem rate_positive : 0 < rate m F := by
  obtain ⟨L, hL, hz⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
  have h := primitive_lower m hm F P v₀ 0 hz
  have ha := average_le_rate m hm F P v₀ 0
  simp only [average, Nat.cast_zero, zero_add, one_mul, div_one] at ha h
  linarith

include hm in
theorem exists_block_above {σ : ℝ} (hσ : σ < rate m F) :
    ∃ b : ℕ, ∃ B : ℝ, B ∈ supports m F b ∧ σ < NativeGHBlockSlope.slope b B := by
  obtain ⟨y, ⟨b, rfl⟩, hb⟩ := exists_lt_of_lt_csSup (Set.range_nonempty (average m F)) hσ
  have hd : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have hb' : σ * ((b : ℝ) + 1) < level m F b := (lt_div_iff₀ hd).mp hb
  let B := (σ * ((b : ℝ) + 1) + level m F b) / 2
  have hB : B < level m F b := by dsimp [B]; linarith
  refine ⟨b, B, restriction_below m hm F b hB, ?_⟩
  apply (lt_div_iff₀ hd).2
  dsimp [B]
  linarith

include hm in
theorem exists_support_band {σ : ℝ} (hσ : σ < rate m F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (R : ℝ), R < ((r : ℝ) + 1) * σ - C →
      R ∈ supports m F r := by
  obtain ⟨b, B, hB, hμ⟩ := exists_block_above m hm F hσ
  obtain ⟨L, hLpos, hL⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
  refine ⟨NativeGHBlockSlope.remainder b B L, NativeGHBlockSlope.remainder_nonneg b B L, ?_⟩
  intro r R hR
  apply NativeGHBlockSlope.power_below m hm F b hB hL r
  have hp := mul_pos (by positivity : (0 : ℝ) < (r : ℝ) + 1) (sub_pos.mpr hμ)
  nlinarith

include hm P v₀ in
theorem exists_level_band {σ : ℝ} (hσ : σ < rate m F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, ((r : ℝ) + 1) * σ - C ≤ level m F r := by
  obtain ⟨C, hC, h⟩ := exists_support_band m hm F hσ
  exact ⟨C, hC, fun r => le_level_of_below m hm F P v₀ r (h r)⟩

end
end Finsler.NativeGHOptimalRate
