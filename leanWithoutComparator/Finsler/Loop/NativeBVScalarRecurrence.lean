module

public import Finsler.Loop.NativePowerCutEquivalences
public import Finsler.Loop.NativeRaisedBVCandidates
public import Finsler.Loop.NativeBVOriginalScalar

/-! The exact obstruction to propagating the primitive actual BV identity.
It is tested on the concrete raised cube, and equals the difference of
adjacent actual coefficients. Vanishing of this obstruction is NOT assumed proved. -/
@[expose] public section
namespace Finsler.NativeBVScalarRecurrence
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.NativeThetaBVShiftBridge
open Finsler.NativePowerCutEquivalences Finsler.NativeBVOriginalScalar
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def defect (m r : ℕ) : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1)) →ₗ[ZMod 2]
    homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) :=
  (thetaCut m r).comp (BVmap m (r + 1)) - (BVmap m r).comp (ghCut m (r + 1))

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem defect_formula (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1))) :
    defect m r z =
      (((kroneckerMap _ (NativeGHPowers.degree m (r + 1 + 1))).hom (NativeGHPowers.power m (r + 1 + 1)) z) *
        (coefficient m hm P v₀ (r + 1) - coefficient m hm P v₀ r)) •
          NativeThetaPowers.fullPower m hm F P v₀ r := by
  change thetaCut m r (alignedBV m (r + 1) z) - alignedBV m r (ghCut m (r + 1) z) = _
  rw [BV_formula m hm F P v₀ (r + 1) z, map_smul, theta_full,
    BV_formula m hm F P v₀ r (ghCut m (r + 1) z), gh_pairing, ← sub_smul, ← mul_sub]

theorem candidate_defect_scalar (r : ℕ) :
    thetaPairing m r (defect m r (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1))) =
      coefficient m hm P v₀ (r + 1) - coefficient m hm P v₀ r := by
  rw [defect_formula m hm F P v₀, NativeRaisedBVCandidates.pairing_one, one_mul, map_smul]
  have he : thetaPairing m r (NativeThetaPowers.fullPower m hm F P v₀ r) = 1 :=
    NativeHighPowerUnit.scalar_one m hm F P v₀ r
  rw [he]
  exact mul_one _

theorem candidate_defect_zero_iff (r : ℕ) :
    defect m r (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) = 0 ↔
      coefficient m hm P v₀ (r + 1) = coefficient m hm P v₀ r := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    rw [← candidate_defect_scalar m hm F P v₀ r, h, map_zero]
  · intro h
    apply thetaPairing_injective m hm F P v₀ r
    rw [candidate_defect_scalar, h, sub_self, map_zero]

theorem all_one_iff_candidate_defects :
    (∀ r, coefficient m hm P v₀ r = 1) ↔
      ∀ r, defect m r (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) = 0 := by
  constructor
  · intro h r
    exact (candidate_defect_zero_iff m hm F P v₀ r).mpr ((h (r + 1)).trans (h r).symm)
  · intro h r
    induction r with
    | zero => exact coefficient_zero m hm P v₀
    | succ r ih => exact ((candidate_defect_zero_iff m hm F P v₀ r).mp (h r)).trans ih

theorem all_detectsTheta_iff_candidate_defects :
    (∀ r, detectsTheta m hm F P v₀ r) ↔
      ∀ r, defect m r (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) = 0 := by
  rw [← all_one_iff_candidate_defects m hm F P v₀]
  exact forall_congr' (fun r => (coefficient_one_iff m hm F P v₀ r).symm)

theorem shift_one_of_candidate_defects
    (h : ∀ r, defect m r (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) = 0) (r : ℕ) :
    NativeThetaSpectralLength.level m hm F P v₀ r ≤ NativeGHSpectralSupport.level m F (r + 1) :=
  level_le_of_BV m hm F P v₀ r ((all_detectsTheta_iff_candidate_defects m hm F P v₀).mpr h r)

theorem gap_le_primitive_of_candidate_defects
    (h : ∀ r, defect m r (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) = 0) (r : ℕ) :
    NativeThetaGHSpectralGap.gap m hm F P v₀ r ≤ NativeThetaSpectralLength.level m hm F P v₀ 0 := by
  have he := NativeThetaGHShiftShortcut.gap_le_of_shift m hm F P v₀ 1
    (shift_one_of_candidate_defects m hm F P v₀ h) r
  simpa only [Nat.cast_one, one_mul] using he

end
end Finsler.NativeBVScalarRecurrence
