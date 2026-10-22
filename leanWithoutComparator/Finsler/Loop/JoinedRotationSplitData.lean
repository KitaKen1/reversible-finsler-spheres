module

public import Finsler.Loop.FirstInputRotationJoinedTime
public import Finsler.Loop.FullSecondHalfCompactTimeOperation
public import Finsler.Topology.JoinedFirstHalfDeformedSplit

/-! Preserve the actual original full and second-half source formulas
when replacing the first-half summand by the constructed rotation-zero
operation. No ambient-homology injectivity is part of this data. -/

@[expose] public section
namespace Finsler.JoinedRotationSplitData

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

structure Data {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
    (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric (m + 1))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (B θ ζ : ℝ) (hθ : 0 < θ) (hζ : 0 < ζ)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r)
    (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B ζ p T)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) where
  caps : Fin 3 → ∀ q,
    (small (TopCat.of (Outer (CompactNearJoinParameters.tube α β R)))
      (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) θ)).X ((m + 1) + (p + q)) ⟶
        (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q
  caps_source : ∀ i q, caps i q ≫
    (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (Outer (CompactNearJoinParameters.tube α β R)))
        (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) θ)).f ((m + 1) + (p + q)) ≫
      (push (JoinedFamilyNaturality.globalMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i)).f ((m + 1) + (p + q)) ≫
      eqToHom (congrArg (chains (parameters (m + 1))).X
        (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫ AnnularCutComparison.cut m p h hρr hr.le T hT q
  caps_comm : ∀ i q, caps i (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q =
    (small (TopCat.of (Outer (CompactNearJoinParameters.tube α β R)))
      (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) θ)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ caps i q
  full : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p)
  second : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p)
  full_component : ∀ q, full.component q =
    AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    (push (JoinedCommonInputRefinement.maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 0)).f ((m + p) + q + 1) ≫
    JoinedSmallCapExtension.cap (CompactNearJoinParameters.tube α β R) θ hθ
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) (ClosedCapDegreeTransport.align m p (caps 0)) q
  second_component : ∀ q, second.component q =
    AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    (push (JoinedCommonInputRefinement.maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 4)).f ((m + p) + q + 1) ≫
    JoinedSmallCapExtension.cap (CompactNearJoinParameters.tube α β R) θ hθ
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) (ClosedCapDegreeTransport.align m p (caps 2)) q
  split : ∀ q, full.homology q =
    (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F B ζ hζ hρr hgood hT 0).homology q + second.homology q
  full_image : ∀ q, full.homology q ≫
    HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (JoinedFilteredCap.sublevel F B))) q =
    ((AnnularCutComparison.operation m p h hρr hr.le T hT).pre
      (push (TopCat.ofHom (JoinedTimeSplit.loopFamily
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))))))).homology q

end
end Finsler.JoinedRotationSplitData
