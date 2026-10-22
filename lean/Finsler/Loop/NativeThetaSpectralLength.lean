module

public import Finsler.Loop.NativeGHOptimalRate
public import Finsler.Loop.NativeThetaTightRepresentatives

/-! Optimize representatives of EACH SAME original Theta power, keeping
its full class fixed. Infima need not be attained: every strictly larger
length has an actual lift. No loop-product associativity is assumed. -/
@[expose] public section
namespace Finsler.NativeThetaSpectralLength
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def lifts (r : ℕ) : Set ℝ :=
  {a | ∃ z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m r),
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
      (NativeThetaPowers.degree m r)).hom z = NativeThetaPowers.fullPower m hm F P v₀ r}

def level (r : ℕ) : ℝ := sInf (lifts m hm F P v₀ r)

theorem lifts_nonempty (r : ℕ) : (lifts m hm F P v₀ r).Nonempty :=
  ⟨NativeThetaPowers.bound m F P v₀ r, NativeThetaPowers.filteredPower m hm F P v₀ r, rfl⟩

theorem lifts_bddBelow (r : ℕ) : BddBelow (lifts m hm F P v₀ r) := by
  refine ⟨NativeGHSpectralSupport.level m F r, ?_⟩
  rintro a ⟨z, hz⟩
  exact NativeGHSpectralSupport.level_le_lift m hm F P v₀ r z hz

theorem level_le_lift (r : ℕ) {a : ℝ} (ha : a ∈ lifts m hm F P v₀ r) :
    level m hm F P v₀ r ≤ a := csInf_le (lifts_bddBelow m hm F P v₀ r) ha

theorem lift_mono (r : ℕ) {a b : ℝ} (hab : a ≤ b) (ha : a ∈ lifts m hm F P v₀ r) :
    b ∈ lifts m hm F P v₀ r := by
  obtain ⟨z, hz⟩ := ha
  refine ⟨(homologyPushZMod2 (LengthFilteredLoopRotation.cut F hab)
    (NativeThetaPowers.degree m r)).hom z, ?_⟩
  rw [NativePrimitiveCutSurjective.cut_full_apply]
  exact hz

theorem lift_above (r : ℕ) {a : ℝ} (ha : level m hm F P v₀ r < a) :
    a ∈ lifts m hm F P v₀ r := by
  obtain ⟨b, hb, hba⟩ := exists_lt_of_csInf_lt (lifts_nonempty m hm F P v₀ r) ha
  exact lift_mono m hm F P v₀ r hba.le hb

theorem gh_le_level (r : ℕ) : NativeGHSpectralSupport.level m F r ≤ level m hm F P v₀ r := by
  apply le_csInf (lifts_nonempty m hm F P v₀ r)
  rintro a ⟨z, hz⟩
  exact NativeGHSpectralSupport.level_le_lift m hm F P v₀ r z hz

theorem level_positive (r : ℕ) : 0 < level m hm F P v₀ r := by
  obtain ⟨L, hLpos, hL⟩ := NativeGHPowerPositiveSupport.exists_primitive_support m hm F
  have h := NativeGHSpectralSupport.primitive_lower m hm F P v₀ r hL
  have hp : 0 < ((r : ℝ) + 1) * L := mul_pos (by positivity) hLpos
  exact hp.trans_le (h.trans (gh_le_level m hm F P v₀ r))

theorem level_le_primitive_lift (r : ℕ) {a : ℝ} (ha : a ∈ lifts m hm F P v₀ 0) :
    level m hm F P v₀ r ≤ ((r : ℝ) + 1) * a := by
  have hapos : 0 < a := (level_positive m hm F P v₀ 0).trans_le
    (level_le_lift m hm F P v₀ 0 ha)
  obtain ⟨z, hz⟩ := ha
  by_contra h
  let δ := (level m hm F P v₀ r - ((r : ℝ) + 1) * a) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hl := level_le_lift m hm F P v₀ r
    (NativeThetaTightRepresentatives.exists_tight_lift m F z hm P v₀ hapos hz r hδ)
  dsimp [δ] at hl
  linarith

theorem level_le_primitive_level (r : ℕ) :
    level m hm F P v₀ r ≤ ((r : ℝ) + 1) * level m hm F P v₀ 0 := by
  have hr : 0 < (r : ℝ) + 1 := by positivity
  have h : level m hm F P v₀ r / ((r : ℝ) + 1) ≤ level m hm F P v₀ 0 := by
    apply le_csInf (lifts_nonempty m hm F P v₀ 0)
    intro a ha
    apply (div_le_iff₀ hr).mpr
    simpa only [mul_comm] using level_le_primitive_lift m hm F P v₀ r ha
  have := (div_le_iff₀ hr).mp h
  nlinarith

theorem rate_le_primitive_level : NativeGHOptimalRate.rate m F ≤ level m hm F P v₀ 0 := by
  apply le_csInf (lifts_nonempty m hm F P v₀ 0)
  intro a ha
  have hp : 0 < a := (level_positive m hm F P v₀ 0).trans_le
    (level_le_lift m hm F P v₀ 0 ha)
  obtain ⟨z, hz⟩ := ha
  exact NativeGHOptimalRate.rate_le_primitive_lift m hm F P v₀ hp z hz

end
end Finsler.NativeThetaSpectralLength
