module

public import Finsler.Loop.NativeGHSpectralSupport
public import Finsler.Loop.NativeGHPowerFiniteDetection

/-! Every length strictly ABOVE the actual GH support supremum has
an actual finite-length homology detector with pairing ONE. Lean Pool's
Kronecker injectivity supplies detection without a rank-one hypothesis.
The infimum of detector lengths equals the support supremum. -/
@[expose] public section
namespace Finsler.NativeGHNearOptimalDetection
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

theorem exists_pairing_one (X : TopCat.{0}) (k : ℕ) (c : cohomologyZMod2 X k) (hc : c ≠ 0) :
    ∃ z : homologyZMod2 X k, (kroneckerMap X k).hom c z = 1 := by
  have hn : ∃ z : homologyZMod2 X k, (kroneckerMap X k).hom c z ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    apply kroneckerMap_injective X k
    rw [map_zero]
    exact LinearMap.ext h
  obtain ⟨z, hz⟩ := hn
  refine ⟨((kroneckerMap X k).hom c z)⁻¹ • z, ?_⟩
  rw [map_smul]
  exact inv_mul_cancel₀ hz

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def lengths (r : ℕ) : Set ℝ :=
  {a | ∃ z : homologyZMod2 (lengthSpace F a) (NativeGHPowers.degree m r),
    (kroneckerMap (Loops (m + 1)) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
        (NativeGHPowers.degree m r)).hom z) = 1}

include hm P v₀ in
theorem detection_above (r : ℕ) {a : ℝ} (ha : NativeGHSpectralSupport.level m F r < a) :
    a ∈ lengths m F r := by
  have hn : (cohPullback (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r) ≠ 0 := by
    intro hz
    exact (not_le_of_gt ha) (NativeGHSpectralSupport.support_le_level m hm F P v₀ r hz)
  obtain ⟨z, hz⟩ := exists_pairing_one (lengthSpace F a) (NativeGHPowers.degree m r) _ hn
  refine ⟨z, ?_⟩
  rw [kroneckerMap_naturality_apply] at hz
  exact hz

include hm in
theorem level_le_detection (r : ℕ) {a : ℝ} (ha : a ∈ lengths m F r) :
    NativeGHSpectralSupport.level m F r ≤ a := by
  by_contra h
  have hs := NativeGHSpectralSupport.restriction_below m hm F r (lt_of_not_ge h)
  obtain ⟨z, hz⟩ := ha
  have hn := congrArg (fun φ : homologyDualZMod2 (lengthSpace F a) (NativeGHPowers.degree m r) => φ z)
    (kroneckerMap_naturality_apply (LengthFilteredLoopRotation.full F a)
      (NativeGHPowers.degree m r) (NativeGHPowers.power m r))
  change (kroneckerMap (lengthSpace F a) (NativeGHPowers.degree m r)).hom
    ((cohPullback (LengthFilteredLoopRotation.full F a) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r)) z = _ at hn
  rw [hs, map_zero, LinearMap.zero_apply] at hn
  exact zero_ne_one (hn.trans hz)

include hm P v₀ in
theorem detection_infimum (r : ℕ) : sInf (lengths m F r) = NativeGHSpectralSupport.level m F r := by
  have hb : BddBelow (lengths m F r) := ⟨NativeGHSpectralSupport.level m F r,
    fun _a ha => level_le_detection m hm F r ha⟩
  have hn : (lengths m F r).Nonempty := ⟨NativeGHSpectralSupport.level m F r + 1,
    detection_above m hm F P v₀ r (by linarith)⟩
  apply le_antisymm
  · by_contra h
    have ha := detection_above m hm F P v₀ r
      (show NativeGHSpectralSupport.level m F r <
        (sInf (lengths m F r) + NativeGHSpectralSupport.level m F r) / 2 by linarith)
    have hh := csInf_le hb ha
    linarith
  · exact le_csInf hn (fun _a ha => level_le_detection m hm F r ha)

include hm P v₀ in
theorem relative_detection_above (r : ℕ) {a : ℝ} (ha : NativeGHSpectralSupport.level m F r < a) :
    ∃ z : homologyZMod2 (lengthSpace F a) (NativeGHPowers.degree m r),
      RelativeKronecker.comparison (NativeFilteredRelativeTheta.pair F a) (NativeGHPowers.degree m r)
        (NativeGHPowerFiniteDetection.finitePower m hm F a r)
        (((NativeFilteredRelativeTheta.pair F a).singularHomologyπ coeff (NativeGHPowers.degree m r)).hom z) = 1 := by
  obtain ⟨z, hz⟩ := detection_above m hm F P v₀ r ha
  exact ⟨z, (NativeGHPowerFiniteDetection.pairing m hm F a r z).trans hz⟩

end
end Finsler.NativeGHNearOptimalDetection
