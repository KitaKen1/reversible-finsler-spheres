module

public import Finsler.Loop.SingleInputNativeCanonicalTime
public import Finsler.Loop.JoinedRotationSplitData
public import Finsler.Topology.NestedCapHomology

/-! Identify the actual native D.full with canonical self-cut AFTER
the actual joined compact family, in the identical filtered output.
The actual R and native rectangle data remain unchanged. -/

@[expose] public section
namespace Finsler.JoinedNativeCanonicalTime

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 3000000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
    (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric (m + 1))
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1 / 2) (θ ζ : ℝ) (hθ : 0 < θ) (hζ : 0 < ζ)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r)
    (ε a L : ℝ) (hε : 0 < ε)
    (hg : FirstInputRotationTestedCap.Adequate α β R r hR hr F (a - L + 3 * ε) ζ p T)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (D : JoinedRotationSplitData.Data α β R r hR hr F s hs hs1 (a - L + 3 * ε) θ ζ hθ hζ p T h hρr hg hT)

abbrev joinedFamily := JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))

theorem family_square : JoinedCommonInputRefinement.maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 0 ≫
    JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) s hs.le hs1.le 0 =
      AnnularSelfCut.familyMap (joinedFamily α β R hR) := by
  ext z : 1
  rfl

variable (κ₀ σ : ℝ) (hσ : 0 < σ) (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate (joinedFamily α β R hR) r hr F ε σ)
  (index : (ClosedInterval × CompactNearJoinParameters.tube α β R) →
    Option (CompactRotatedCutData.source (joinedFamily α β R hR) r))
  (hindex : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆
    FirstInputSelfCutCover.cover (joinedFamily α β R hR) r hr κ₀ ρ (index c))
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (joinedFamily α β R hR x) < a) (hm : 1 ≤ m)

include hσ hradius hsmall hindex hm in
theorem full_homology (q : ℕ) : D.full.homology q =
    ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
      (push (CompactInputShortMaps.family (joinedFamily α β R hR) F a hA))).homology q := by
  let X : TopCat.{0} := TopCat.of (CompactNearJoinParameters.tube α β R)
  let Z : TopCat.{0} := TopCat.of (Outer (CompactNearJoinParameters.tube α β R))
  let V := JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) θ
  let v := NestedCapHomology.operation (m + 1) p (D.caps 0) (D.caps_comm 0)
  let g := JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) s hs.le hs1.le 0
  have hv (t : ℕ) : v.component t ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (a - L + 3 * ε)))).f t =
    (inclusion Z V).f (((m + 1) + p) + t) ≫ (push g).f (((m + 1) + p) + t) ≫
      eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
        (show ((m + 1) + p) + t = (m + p) + t + 1 by omega)) ≫ AnnularCutComparison.cut m p h hρr hr.le T hT t := by
    have hh := CapSourceDegreeTransport.pre (inclusion Z V ≫ push g)
      (((m + 1) + p) + t) ((m + 1) + (p + t)) ((m + p) + t + 1)
      (by omega) (by omega) (by omega)
      ((D.caps 0 t) ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε)))).f t)
      (AnnularCutComparison.cut m p h hρr hr.le T hT t)
      (by simpa only [Z, V, g, JoinedFilteredCap.sublevel, SelfCutOscillation.short,
        HomologicalComplex.comp_f, Category.assoc] using D.caps_source 0 t)
    simpa only [v, NestedCapHomology.operation, HomologicalComplex.comp_f, Category.assoc] using hh
  have hz (t : ℕ) : D.full.component t = AnnularTimeTrim.prism X ((m + p) + t) ≫
      (push (JoinedCommonInputRefinement.maps X 0) ≫ TauCeti.smallSingularRetraction (X := Z) coeff V
        (JoinedSimultaneousPrisms.rectangles_open _ θ) (JoinedSimultaneousPrisms.rectangles_univ _ θ hθ)).f ((m + p) + t + 1) ≫
        DegreeLoweringSuccAlignment.align (m + p) v (by omega) t := by
    rw [D.full_component]
    simp only [v, NestedCapHomology.operation, DegreeLoweringSuccAlignment.align,
      JoinedSmallCapExtension.cap, ClosedCapDegreeTransport.align, HomologicalComplex.comp_f, Category.assoc]
    simp only [JoinedSimultaneousPrisms.retraction, X, Z, V]
    rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]
  exact SingleInputNativeCanonicalTime.homology_eq (joinedFamily α β R hR) r hr κ₀ h p T hT F ε a L σ hσ hε
    hradius hsmall index hindex hshort hA hρr hm Z V
    (JoinedSimultaneousPrisms.rectangles_open _ θ) (JoinedSimultaneousPrisms.rectangles_univ _ θ hθ)
    (JoinedCommonInputRefinement.maps X 0) g (family_square α β R hR s hs hs1) v hv D.full hz q

end
end Finsler.JoinedNativeCanonicalTime
