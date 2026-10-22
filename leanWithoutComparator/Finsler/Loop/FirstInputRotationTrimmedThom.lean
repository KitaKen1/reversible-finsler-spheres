module

public import Finsler.Loop.FirstInputRotationTimeTrim
public import Finsler.Loop.FirstHalfAnnularPullbacks

/-! The actual trimmed rotation-one Thom cochain equals the original
native first-half Thom source on the entire cylinder, before any cap,
subdivision or passage to homology. -/

@[expose] public section
namespace Finsler.FirstInputRotationTrimmedThom

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality
open Finsler.FirstInputRotationCutCylinder Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ) (hR : R ≤ 1 / 2)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

local instance : CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

theorem thom_agreement (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) n (thom α β R hR hn h) =
      FirstHalfAnnularTimeDomain.thom
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hn h := by
  rw [FirstHalfAnnularPullbacks.thom_pullback, FirstHalfThomNaturality.trimmed_annular]
  change cochainPullback _ n (cochainPullback (reorder α β R) n
    (cochainPullback (FirstInputRotationAmbientCover.ambientEvaluation α β R hR) n
      (AnnularSelfCut.cocycle n hn h))) = _
  rw [← pullback_comp, ← pullback_comp]
  have he := rotation_one_parameters α β R a ha ha1 hR
  simpa only [Category.assoc] using congrArg
    (fun f => cochainPullback f n (AnnularSelfCut.cocycle n hn h)) he

end
end Finsler.FirstInputRotationTrimmedThom
