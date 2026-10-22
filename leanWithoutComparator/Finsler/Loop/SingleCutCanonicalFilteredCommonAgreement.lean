module

public import Finsler.Loop.SingleCutCanonicalCupOnCommonCover
public import Finsler.Loop.SingleCutBoundedCanonicalThomCap
public import Finsler.Topology.PullbackPairCover

/-! Genuine canonical two-stage and individually filtered one-cup cap
agree on one actual common source refinement inside the literal short
output complex. Only degreewise chain inclusions are cancelled. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalFilteredCommonAgreement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)


variable (R : ℝ) (hrR : r < R) (hR : R ≤ 1)
  (hRR : R ≤ SelfCutLengthControl.radius F hε)

def common := PullbackPairCover.cover
  (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)
  (OriginalFirstHalfFactorwiseCover.first σ) (𝟙 (ambient α)) (𝟙 (ambient α))

theorem common_open (i) : IsOpen (common α r F ε a σ hA R hrR hR (ρ := ρ) i) :=
  PullbackPairCover.isOpen _ _ _ _
    (SingleCutCanonicalThomSmallLift.cover_open α r F a R hrR hA hR ε)
    (OriginalFirstHalfFactorwiseCover.first_open σ) i

include hε in
theorem common_univ (hσ : 0 < σ) (hρr : ρ < r) :
    ⋃ i, common α r F ε a σ hA R hrR hR (ρ := ρ) i = Set.univ :=
  PullbackPairCover.covers _ _ _ _
    (SingleCutCanonicalThomSmallLift.cover_univ α r F a R hrR hA hR ε hε hρr)
    (OriginalFirstHalfFactorwiseCover.first_univ hσ)

def leftMap := SmallRefinementComparison.refinement
  (common α r F ε a σ hA R hrR hR (ρ := ρ))
  (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ) Prod.fst (fun _ _ hz => hz.1)

def rightMap := SmallRefinementComparison.refinement
  (common α r F ε a σ hA R hrR hR (ρ := ρ))
  (OriginalFirstHalfFactorwiseCover.first σ) Prod.snd (fun _ _ hz => hz.2)

theorem left_source : leftMap α r F ε a σ hA R hrR hR (ρ := ρ) ≫
    inclusion (ambient α) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ) =
      inclusion (ambient α) (common α r F ε a σ hA R hrR hR (ρ := ρ)) :=
  SmallRefinementComparison.refinement_inclusion _ _ _ _

theorem right_source : rightMap α r F ε a σ hA R hrR hR (ρ := ρ) ≫
    inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ) =
      inclusion (ambient α) (common α r F ε a σ hA R hrR hR (ρ := ρ)) :=
  SmallRefinementComparison.refinement_inclusion _ _ _ _

def toProper := inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
  (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
  push (FirstInputSelfCutBoundedSpace.toCut α r hr F (a - L + 3 * ε))

theorem toProper_source : toProper α r hr κ F ε a L ≫ push (source α r) =
    FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ := by
  rw [toProper, Category.assoc, ← push_comp, FirstInputSelfCutBoundedSpace.source_square]
  rfl

def retained := inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
  (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
  push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε))

theorem retained_source : retained α r hr κ F ε a L ≫
    push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F (a - L + 3 * ε))) =
    toProper α r hr κ F ε a L ≫ push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr)) := by
  have hs : FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε) ≫
      SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (a - L + 3 * ε)) =
      FirstInputSelfCutBoundedSpace.toCut α r hr F (a - L + 3 * ε) ≫
        TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  dsimp only [retained, toProper]
  rw [Category.assoc, ← push_comp, hs, push_comp, Category.assoc]

theorem proper_component (q : ℕ) :
    (rightMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).component q ≫
      (toProper α r hr κ F ε a L).f q =
    (leftMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      SingleCutCanonicalCupOnCommonCover.cupComponent α r hr F a R hrR hA hR ε h p T q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
        (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)).f q := by
  haveI : Mono ((push (source α r)).f q) :=
    SupportedCap.subspacePush_mono (ambient α) (CompactRotatedCutData.source α r) q
  have hb := SingleCutBoundedCanonicalThomCap.operation_source α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q
  have hc := SingleCutCanonicalCupOnCommonCover.component_source α r hr F a R hrR hA hR ε h p T hT q
  rw [SingleCutCanonicalCupOnCommonCover.component_eq_cup] at hc
  have hi := congrArg (fun f => f.f (((m + 1) + p) + q))
    (left_source α r F ε a σ hA R hrR hR (ρ := ρ))
  have hj := congrArg (fun f => f.f (((m + 1) + p) + q))
    (right_source α r F ε a σ hA R hrR hR (ρ := ρ))
  have hk := congrArg (fun f => f.f q) (toProper_source α r hr κ F ε a L)
  simp only [HomologicalComplex.comp_f] at hi hj hk hc
  apply (cancel_mono ((push (source α r)).f q)).mp
  simp only [Category.assoc]
  rw [hk, hb, hc]
  simpa only [Category.assoc] using congrArg (fun f => f ≫
    absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl
      (SingleCutCanonicalThomCochains.canonicalGamma α r hr h p T)) (hj.trans hi.symm)

theorem filtered_component (q : ℕ) :
    (leftMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      (SingleCutCanonicalTwoStage.operation α r F a R hrR hA hR ε h hε hRR L p T hT hshortT).component q =
    (rightMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).component q ≫
      (retained α r hr κ F ε a L).f q := by
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F (a - L + 3 * ε)))).f q) :=
    SupportedCap.subspacePush_mono _ _ q
  have hs := congrArg (fun f => f.f q) (retained_source α r hr κ F ε a L)
  simp only [HomologicalComplex.comp_f] at hs
  apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F (a - L + 3 * ε)))).f q)).mp
  simp only [Category.assoc]
  rw [SingleCutCanonicalCupOnCommonCover.filtered_twoStage_source α r hr F a R hrR hA hR ε h p T hT hε hRR L hshortT q,
    hs]
  have he := congrArg (fun f => f ≫ (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr))).f q)
    (proper_component α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR q)
  simpa only [Category.assoc] using he.symm

end
end Finsler.SingleCutCanonicalFilteredCommonAgreement
