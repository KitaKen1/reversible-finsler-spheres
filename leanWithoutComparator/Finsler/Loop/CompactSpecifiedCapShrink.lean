module

public import Finsler.Loop.CompactJoinRepresentative
public import Finsler.Loop.ClosedCarrierSupportedComparison

/-! Shrink only the specified representative into any smaller open
near neighborhood, retaining the original compact normalized cap,
rectangle cover and closed R carrier. -/

@[expose] public section
namespace Finsler.CompactSpecifiedCapShrink

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (κ R : ℝ)
  (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (s : ℝ) (hs : 0 < s) (hsR : s ≤ R)

include hsR in
theorem near_sub : CompactNormalizedJoinCapComparison.near α β s ⊆ CompactNearJoinParameters.tube α β R :=
  fun _ hz => hz.le.trans hsR

include hs in
theorem diagonal_in_near (z : TopCat.of (P × Q))
    (hz : StrictLengthProductFamilies.leftEvaluation α z = StrictLengthProductFamilies.rightEvaluation β z) :
    z ∈ CompactNormalizedJoinCapComparison.near α β s := by
  have hz' := congrArg Subtype.val hz
  change basepoint (α z.1) = basepoint (β z.2) at hz'
  change dist (basepoint (α z.1)) (basepoint (β z.2)) < s
  rw [hz', dist_self]
  exact hs

def intoCarrier := ClosedCarrierSupportedComparison.nearInclusion (TopCat.of (P × Q))
  (CompactNormalizedJoinCapComparison.near α β s) (CompactNearJoinParameters.tube α β R) (near_sub α β R s hsR)

def smallOperation := DiagonalCutNaturality.operation (dim_pos m)
  (StrictLengthProductFamilies.leftEvaluation α (Q := Q)) (StrictLengthProductFamilies.rightEvaluation β (P := P))
  (CompactNormalizedJoinCapComparison.near α β s) (CompactNormalizedJoinCapComparison.near_open α β s)
  (diagonal_in_near α β s hs)

def specifiedUnrefined := (CompactJoinRepresentative.specifiedOperation α β κ R hκ hκR).pre
  (smallSingularRetraction (X := TopCat.of (P × Q)) coeff (CompactJoinCapLocalization.cover α β κ)
    (CompactJoinCapLocalization.cover_open α β κ) (CompactJoinCapLocalization.cover_univ α β hκ))

theorem specified_homology (q : ℕ) : (specifiedUnrefined α β κ R hκ hκR).homology q =
    ((smallOperation α β s hs).post (push (intoCarrier α β R s hsR))).homology q := by
  exact ClosedCarrierSupportedComparison.homology_eq (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)
    (DiagonalPullbackCut.exclusion (StrictLengthProductFamilies.leftEvaluation α (Q := Q))
      (StrictLengthProductFamilies.rightEvaluation β (P := P)))
    (CompactNormalizedJoinCapComparison.near α β s) (DiagonalPullbackCut.exclusion_open _ _)
    (CompactNormalizedJoinCapComparison.near_open α β s)
    (DiagonalPullbackCut.neighborhood_cover _ _ _ (diagonal_in_near α β s hs))
    (CompactNearJoinParameters.tube α β R) (near_sub α β R s hsR) (m + 1) _
    (DiagonalPullbackCut.cocycle_supported (dim_pos m) _ _) (DiagonalPullbackCut.cocycle_closed (dim_pos m) _ _)
    (CompactJoinRepresentative.specifiedOperation α β κ R hκ hκR)
    (CompactFarCarrierCap.source α β κ R hκR (m + 1) (CompactJoinRepresentative.specified α β)
      (CompactJoinRepresentative.specified_far α β κ hκ))
    (CompactJoinCapLocalization.cover_open α β κ) (CompactJoinCapLocalization.cover_univ α β hκ) q


theorem homology_eq (hm : 1 ≤ m) (hκ2 : κ ≤ 2) (q : ℕ) :
    (CompactJoinCapLocalization.unrefined α β (dim_pos m) hκ hκR).homology q =
    ((smallOperation α β s hs).post (push (intoCarrier α β R s hsR))).homology q := by
  rw [CompactJoinCapLocalization.unrefined, DegreeLoweringHomology.Map.pre_homology,
    CompactJoinRepresentative.homology_eq α β κ R hκ hκR hm hκ2 q]
  simpa only [specifiedUnrefined, DegreeLoweringHomology.Map.pre_homology] using
    specified_homology α β κ R hκ hκR s hs hsR q

end
end Finsler.CompactSpecifiedCapShrink
