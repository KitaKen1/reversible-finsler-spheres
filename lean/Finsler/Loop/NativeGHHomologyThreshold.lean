module

public import Finsler.Loop.NativeRaisedBVCandidates
public import Finsler.Loop.NativeBVOriginalScalar

/-! The original GH support threshold is the actual zero/surjective
transition of the full homology image. The SAME constructed high BV
input has infimal lift length exactly that threshold; no endpoint claim. -/
@[expose] public section
namespace Finsler.NativeGHHomologyThreshold
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

include hm P v₀ in
theorem support_iff_full_map_zero (r : ℕ) (a : ℝ) :
    a ∈ NativeGHSpectralSupport.supports m F r ↔
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro z
    apply NativeGHRankOne.pairing_injective m hm P v₀ r
    have hn := congrArg (fun φ : homologyDualZMod2 (lengthSpace F a) (NativeGHPowers.degree m r) => φ z)
      (kroneckerMap_naturality_apply (LengthFilteredLoopRotation.full F a)
        (NativeGHPowers.degree m r) (NativeGHPowers.power m r))
    change (kroneckerMap (lengthSpace F a) (NativeGHPowers.degree m r)).hom
      ((cohPullback (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom
        (NativeGHPowers.power m r)) z = _ at hn
    rw [h, map_zero, LinearMap.zero_apply] at hn
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using hn.symm
  · intro h
    apply kroneckerMap_injective (lengthSpace F a) (NativeGHPowers.degree m r)
    rw [map_zero]
    apply LinearMap.ext
    intro z
    have hn := congrArg (fun φ : homologyDualZMod2 (lengthSpace F a) (NativeGHPowers.degree m r) => φ z)
      (kroneckerMap_naturality_apply (LengthFilteredLoopRotation.full F a)
        (NativeGHPowers.degree m r) (NativeGHPowers.power m r))
    change (kroneckerMap (lengthSpace F a) (NativeGHPowers.degree m r)).hom
      ((cohPullback (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom
        (NativeGHPowers.power m r)) z = _ at hn
    rw [h, LinearMap.comp_apply, LinearMap.zero_apply, map_zero] at hn
    exact hn

include hm P v₀ in
theorem full_map_zero_below (r : ℕ) {a : ℝ} (ha : a < NativeGHSpectralSupport.level m F r) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom = 0 :=
  (support_iff_full_map_zero m hm F P v₀ r a).mp (NativeGHSpectralSupport.restriction_below m hm F r ha)

include hm P v₀ in
theorem full_map_surjective_above (r : ℕ) {a : ℝ} (ha : NativeGHSpectralSupport.level m F r < a) :
    Function.Surjective (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom := by
  obtain ⟨z, hz⟩ := NativeGHNearOptimalDetection.detection_above m hm F P v₀ r ha
  have he : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom z =
      NativeGHRankOne.detector m hm P v₀ r := NativeGHRankOne.pairing_injective m hm P v₀ r
        (hz.trans (NativeGHRankOne.detector_pairing m hm P v₀ r).symm)
  intro y
  refine ⟨((kroneckerMap _ (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r) y) • z, ?_⟩
  rw [map_smul, he]
  exact (NativeBVOriginalScalar.gh_expansion m hm P v₀ r y).symm

def candidateLifts (r : ℕ) : Set ℝ :=
  {a | ∃ z : homologyZMod2 (lengthSpace F a) (NativeGHPowers.degree m (r + 1)),
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m (r + 1))).hom z =
      NativeRaisedBVCandidates.full m hm F P v₀ r}

theorem candidateLifts_eq_detection (r : ℕ) :
    candidateLifts m hm F P v₀ r = NativeGHNearOptimalDetection.lengths m F (r + 1) := by
  ext a
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz ▸ NativeRaisedBVCandidates.pairing_one m hm F P v₀ r⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, NativeGHRankOne.pairing_injective m hm P v₀ (r + 1)
      (hz.trans (NativeRaisedBVCandidates.pairing_one m hm F P v₀ r).symm)⟩

theorem candidate_lift_infimum (r : ℕ) :
    sInf (candidateLifts m hm F P v₀ r) = NativeGHSpectralSupport.level m F (r + 1) := by
  rw [candidateLifts_eq_detection]
  exact NativeGHNearOptimalDetection.detection_infimum m hm F P v₀ (r + 1)

theorem candidate_lift_above (r : ℕ) {a : ℝ} (ha : NativeGHSpectralSupport.level m F (r + 1) < a) :
    a ∈ candidateLifts m hm F P v₀ r :=
  full_map_surjective_above m hm F P v₀ (r + 1) ha _

end
end Finsler.NativeGHHomologyThreshold
