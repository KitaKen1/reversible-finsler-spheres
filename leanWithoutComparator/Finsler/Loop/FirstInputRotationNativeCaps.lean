module

public import Finsler.Loop.FirstInputRotationNativeTested
public import Finsler.Loop.LocalizedDoubleCapAgreement

/-! The actual original first-half two-cap agrees with the rotating
trimmed two-cap on its genuine far/domain face cover. This compares the
literal tested extensions by localization, with distinct radii retained. -/

@[expose] public section
namespace Finsler.FirstInputRotationNativeCaps

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SelfCutParameterFamily Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.SmallChainCarrier Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r₀ r₁ : ℝ)
  (hR : R ≤ 1 / 2) (hr₀ : r₀ < 1) (hr₁ : r₁ ≤ 1) (hr : r₁ ≤ r₀)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

local instance : CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

def far (ρ : ℝ) : Set (ClosedInterval × CompactNearJoinParameters.tube α β R) :=
  (planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1) ⁻¹'
    JoinedRectangleRefinement.far
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1

theorem thom_far_zero (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback
      (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (far α β R hR a ha ha1 ρ)) n
      (FirstHalfAnnularTimeDomain.thom
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hn h) = 0 := by
  apply pullback_support
    (planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1)
    (far α β R hR a ha ha1 ρ)
    (JoinedRectangleRefinement.far
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1)
    (fun _ hz => hz) n
    (SupportedSelfCutAdequacy.extension (tube (CompactNearJoinParameters.tube α β R))
      (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le)
        1 n (AnnularSelfCut.cocycle n hn h))
  exact JoinedCochainBoundary.extension_far_zero
    (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1 n
    (AnnularSelfCut.cocycle n hn h) (AnnularSupportedCut.cocycle_supported n hn h)

include hr in
theorem cap_agreement (η : ℝ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hW : ∀ center,
      JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
        JoinedRectangleRefinement.far
          (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1 ∨
      JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
        domain (tube (CompactNearJoinParameters.tube α β R))
          (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le)
            (fun _ => r₁) 1)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) (q : ℕ) :
    (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) n p q
          (FirstHalfAnnularTimeDomain.thom
            (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hn h)
          (FirstHalfAnnularTimeDomain.tested
            (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ p T) =
    (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) n p q
          (cochainPullback (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) n
            (FirstInputRotationCutCylinder.thom α β R hR hn h))
          (cochainPullback (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) p
            (FirstInputRotationCutCylinder.tested α β R r₀ hR hr₀ p T)) := by
  rw [FirstInputRotationTrimmedThom.thom_agreement α β R hR a ha ha1]
  apply LocalizedDoubleCapAgreement.on_cover
    (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
    (far α β R hR a ha ha1 ρ) (FirstInputRotationNativeTested.faceDomain α β R r₁ hR a ha ha1)
    _ n p _ (thom_far_zero α β R hR a ha ha1 hn h) _ _
    (FirstInputRotationNativeTested.agreement α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 p T) q
  intro center
  rcases hW center with hf | hd
  · exact Or.inl (fun _ hz => hf hz)
  · exact Or.inr (fun _ hz => hd hz)

end
end Finsler.FirstInputRotationNativeCaps
