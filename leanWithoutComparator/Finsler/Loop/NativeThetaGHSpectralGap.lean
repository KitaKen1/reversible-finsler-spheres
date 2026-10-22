module

public import Finsler.Loop.NativeThetaSpectralLength

/-! Optimize BOTH actual input representatives and actual GH support at
each fixed power. The original cut has a lift at t_r-s_r+delta for EVERY
delta>0, without attaining either endpoint or regrouping Theta products.
A uniform total gap is an explicit, still unproved geometric premise. -/
@[expose] public section
namespace Finsler.NativeThetaGHSpectralGap
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

def gap (r : ℕ) : ℝ :=
  NativeThetaSpectralLength.level m hm F P v₀ r - NativeGHSpectralSupport.level m F r

theorem gap_nonneg (r : ℕ) : 0 ≤ gap m hm F P v₀ r :=
  sub_nonneg.mpr (NativeThetaSpectralLength.gh_le_level m hm F P v₀ r)

theorem gap_le_primitive (r : ℕ) :
    gap m hm F P v₀ r ≤
      ((r : ℝ) + 1) * NativeThetaSpectralLength.level m hm F P v₀ 0 -
        NativeGHSpectralSupport.level m F r :=
  sub_le_sub_right (NativeThetaSpectralLength.level_le_primitive_level m hm F P v₀ r) _

theorem exists_same_cut (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : homologyZMod2 (lengthSpace F (gap m hm F P v₀ r + δ)) (m + 1),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F
        (gap m hm F P v₀ r + δ)) (m + 1)).hom w =
          NativeHighPowerUnitComparison.singleCut m hm F P v₀ r ∧
      (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
        ((homologyPushZMod2 (LengthFilteredLoopRotation.full F
          (gap m hm F P v₀ r + δ)) (m + 1)).hom w) =
            AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  let a := NativeThetaSpectralLength.level m hm F P v₀ r + δ / 3
  let L := NativeGHSpectralSupport.level m F r - δ / 3
  obtain ⟨z, hz⟩ := NativeThetaSpectralLength.lift_above m hm F P v₀ r
    (show NativeThetaSpectralLength.level m hm F P v₀ r < a by dsimp [a]; linarith)
  have hL := NativeGHSpectralSupport.restriction_below m hm F r
    (show L < NativeGHSpectralSupport.level m F r by dsimp [L]; linarith)
  have hε : 0 < δ / 9 := by linarith
  have hlen : a - L + 3 * (δ / 9) ≤ gap m hm F P v₀ r + δ := by
    dsimp [a, L, gap]; linarith
  let w := (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hlen) (m + 1)).hom
    (NativeHighPowerFilteredCut.cut m F r hL hε z)
  have hw : (homologyPushZMod2 (LengthFilteredLoopRotation.full F
      (gap m hm F P v₀ r + δ)) (m + 1)).hom w =
        NativeHighPowerUnitComparison.singleCut m hm F P v₀ r := by
    dsimp only [w]
    rw [NativePrimitiveCutSurjective.cut_full_apply]
    exact NativeHighPowerFilteredCut.cut_full m F r hL hm P v₀ z hz hε
  refine ⟨w, hw, ?_⟩
  rw [hw]
  exact NativeHighPowerUnit.single_UNIT m hm F P v₀ r

/-- ONE bound precedes ALL powers and all positive slack. This concerns
representatives with the original full image, not equality with the
constant-loop unit inside that same finite sublevel. -/
theorem uniform_cut_of_gap_bound {C : ℝ} (hC : ∀ r, gap m hm F P v₀ r ≤ C) :
    ∀ (r : ℕ) (δ : ℝ), 0 < δ →
      ∃ w : homologyZMod2 (lengthSpace F (C + δ)) (m + 1),
        (homologyPushZMod2 (LengthFilteredLoopRotation.full F (C + δ)) (m + 1)).hom w =
          NativeHighPowerUnitComparison.singleCut m hm F P v₀ r ∧
        (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
          ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (C + δ)) (m + 1)).hom w) =
            AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  intro r δ hδ
  obtain ⟨w, hw, _hU⟩ := exists_same_cut m hm F P v₀ r hδ
  have hlen : gap m hm F P v₀ r + δ ≤ C + δ := by linarith [hC r]
  let w' := (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hlen) (m + 1)).hom w
  have hw' : (homologyPushZMod2 (LengthFilteredLoopRotation.full F (C + δ)) (m + 1)).hom w' =
      NativeHighPowerUnitComparison.singleCut m hm F P v₀ r := by
    dsimp only [w']
    rw [NativePrimitiveCutSurjective.cut_full_apply]
    exact hw
  refine ⟨w', hw', ?_⟩
  rw [hw']
  exact NativeHighPowerUnit.single_UNIT m hm F P v₀ r

end
end Finsler.NativeThetaGHSpectralGap
