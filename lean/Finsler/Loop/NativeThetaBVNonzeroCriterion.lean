module

public import Finsler.Loop.NativeThetaRankOne
public import Finsler.Loop.NativeThetaBVShiftBridge

/-! With the actual Theta rank-one theorem, identifying a BV output with
the SAME original Theta power needs only nonvanishing over F2. The remaining
alternating nonvanishing claim is explicit, not assumed proved. -/
@[expose] public section
namespace Finsler.NativeThetaBVNonzeroCriterion
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.NativeThetaBVShiftBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def nonzeroOnDetectors (m r : ℕ) : Prop :=
  ∀ z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)),
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m (r + 1))).hom
      (NativeGHPowers.power m (r + 1)) z = 1 → alignedBV m r z ≠ 0

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem lifts_iff_exists_nonzero (r : ℕ) (a : ℝ) :
    a ∈ NativeThetaSpectralLength.lifts m hm F P v₀ r ↔
      ∃ z : homologyZMod2 (StrictLengthEnergyBridge.lengthSpace F a) (NativeThetaPowers.degree m r),
        (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeThetaPowers.degree m r)).hom z ≠ 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz ▸ NativeThetaPowers.fullPower_ne_zero m hm F P v₀ r⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, NativeThetaRankOne.nonzero_eq_theta m hm F P v₀ r _ hz⟩

theorem spectral_length_independent (Q : Sphere (m + 1)) (w₀ : equator Q) (r : ℕ) :
    NativeThetaSpectralLength.level m hm F P v₀ r = NativeThetaSpectralLength.level m hm F Q w₀ r := by
  apply congrArg sInf
  ext a
  rw [lifts_iff_exists_nonzero m hm F P v₀ r a, lifts_iff_exists_nonzero m hm F Q w₀ r a]

theorem detectsTheta_iff_nonzero (r : ℕ) :
    detectsTheta m hm F P v₀ r ↔ nonzeroOnDetectors m r := by
  constructor
  · intro h z hz
    rw [h z hz]
    exact NativeThetaPowers.fullPower_ne_zero m hm F P v₀ r
  · intro h z hz
    exact NativeThetaRankOne.nonzero_eq_theta m hm F P v₀ r _ (h z hz)

theorem level_le_of_nonzero (r : ℕ) (h : nonzeroOnDetectors m r) :
    NativeThetaSpectralLength.level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + 1) :=
  level_le_of_BV m hm F P v₀ r ((detectsTheta_iff_nonzero m hm F P v₀ r).mpr h)

theorem shift_two_of_alternating_nonzero
    (h : ∀ r, nonzeroOnDetectors m r ∨ nonzeroOnDetectors m (r + 1)) (r : ℕ) :
    NativeThetaSpectralLength.level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + 2) := by
  apply shift_two_of_alternating_BV m hm F P v₀ _ r
  intro j
  exact (h j).imp ((detectsTheta_iff_nonzero m hm F P v₀ j).mpr)
    ((detectsTheta_iff_nonzero m hm F P v₀ (j + 1)).mpr)

theorem gap_le_of_alternating_nonzero
    (h : ∀ r, nonzeroOnDetectors m r ∨ nonzeroOnDetectors m (r + 1)) (r : ℕ) :
    NativeThetaGHSpectralGap.gap m hm F P v₀ r ≤ 2 * NativeThetaSpectralLength.level m hm F P v₀ 0 := by
  apply gap_le_of_alternating_BV m hm F P v₀ _ r
  intro j
  exact (h j).imp ((detectsTheta_iff_nonzero m hm F P v₀ j).mpr)
    ((detectsTheta_iff_nonzero m hm F P v₀ (j + 1)).mpr)

end
end Finsler.NativeThetaBVNonzeroCriterion
