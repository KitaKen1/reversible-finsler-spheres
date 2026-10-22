module

public import Finsler.Loop.OriginalFirstHalfCutOutputJoinData
public import Finsler.Loop.FirstInputRotationCutAlignment
public import Finsler.Loop.OriginalFirstHalfJointSupportedCap

/-! The actual proper near-pair cut domain is homeomorphic to the
near join domain of canonical retained right cuts and beta. The joined
output is the already established fixed retained loop, pointwise. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutOutputJoinGeometry

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.H1SelfCutNeighborhood Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.OriginalFirstHalfCutOutputJoinData

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ) (hr : r < 1)

def nearHomeo : FirstInputRotatingCut.source α β R r ≃ₜ CompactNearJoinParameters.tube (kept α r hr) β R where
  toFun z := ⟨(⟨(z.val.1, z.val.2.val.1), z.property⟩, z.val.2.val.2), by
    change dist (basepoint (kept α r hr _)) (basepoint (β _)) ≤ R
    rw [kept_basepoint]
    exact z.val.2.property⟩
  invFun z := ⟨(z.val.1.val.1, ⟨(z.val.1.val.2, z.val.2), by
    change dist (basepoint (α z.val.1.val.2)) (basepoint (β z.val.2)) ≤ R
    rw [← kept_basepoint α r hr z.val.1]
    exact z.property⟩), z.val.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def nearIso : TopCat.of (FirstInputRotatingCut.source α β R r) ≅
    TopCat.of (CompactNearJoinParameters.tube (kept α r hr) β R) := TopCat.isoOfHomeo (nearHomeo α β R r hr)

theorem original_time_square :
    (nearIso α β R r hr).hom ≫ SupportedCap.subspaceMap
      (TopCat.of (CompactRotatedCutData.source α r × Q)) (CompactNearJoinParameters.tube (kept α r hr) β R) ≫
      originalTime α r (Q := Q) = OriginalFirstHalfJointCover.source α β R r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (hR : R ≤ 1 / 2)

def joined : C(CompactNearJoinParameters.tube (kept α r hr) β R, SphereLoop (m + 1)) :=
  JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs (kept α r hr) β R (hR.trans_lt (by norm_num)))

theorem joined_eq_fixed (z : FirstInputRotatingCut.source α β R r) :
    joined α β R r hr hR (nearHomeo α β R r hr z) = FirstInputRotatingFixedOutput.output α β R r hR hr z := by
  rw [FirstInputRotationCutAlignment.output_eq_original_join]
  rfl

theorem joined_square : (nearIso α β R r hr).hom ≫ TopCat.ofHom (joined α β R r hr hR) =
    TopCat.ofHom (FirstInputRotatingFixedOutput.output α β R r hR hr) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact joined_eq_fixed α β R r hr hR

end
end Finsler.OriginalFirstHalfCutOutputJoinGeometry
