module

public import Finsler.Loop.SingleCutCanonicalFilteredCommonAgreement
public import Finsler.Loop.RegradedTimeCoverComparison
public import Finsler.Loop.SingleCutBoundedCanonicalThomTime
public import Finsler.Loop.SingleCutCanonicalThomEndpoints
public import Finsler.Loop.RegradedSingleCapTime

/-! The actual common-cover refinement of the individually filtered
canonical-Thom-cup time operation. The real source and endpoint supports
construct genuine time descent before retained output. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalCommonTime

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
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)


variable (R : ℝ) (hrR : r < R) (hR : R ≤ 1) (hρr : ρ < r)

def refinedCap := (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).pre (SingleCutCanonicalFilteredCommonAgreement.rightMap α r F ε a σ hA R hrR hR (ρ := ρ))

theorem refined_source (q : ℕ) :
    (refinedCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR).component q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ))).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl
        (SingleCutCanonicalThomCochains.canonicalGamma α r hr h p T) := by
  dsimp only [refinedCap, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, SingleCutBoundedCanonicalThomCap.operation_source, ← Category.assoc,
    ← HomologicalComplex.comp_f, SingleCutCanonicalFilteredCommonAgreement.right_source]

def cap := RegradedSingleCapTime.cap (TopCat.of P) (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr)
  (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)) (m + p) ((m + 1) + p) (by omega) (refinedCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR)

theorem cap_comm (q : ℕ) :
    cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr (q + 1) ≫ (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q =
      (chains (ambient α)).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr q :=
  RegradedSingleCapTime.cap_comm (TopCat.of P) (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)) (m + p) ((m + 1) + p) (by omega) (refinedCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR) q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of P) t)).f ((m + p) + q + 1) ≫ cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr q = 0 :=
  RegradedSingleCapTime.endpoint_zero (TopCat.of P) (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)) (m + p) ((m + 1) + p) (by omega) (refinedCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR)
    (SingleCutCanonicalThomEndpoints.sliceSet α t) (SingleCutCanonicalThomCochains.canonicalGamma α r hr h p T)
    (SingleCutCanonicalThomEndpoints.gamma_slice_zero α h r hr p T t ht)
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
    (refined_source α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR) t (fun _ => rfl) q

def operation := TimePrismDescent.operation
  ((AnnularTimeTrim.cylinder (TopCat.of P)).toSSet.chainComplexMap coeff) (m + p)
  (cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr) (cap_comm α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr)
  (endpoint_zero α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr 0 (Or.inl rfl)) (endpoint_zero α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr 1 (Or.inr rfl))

theorem component_normal (q : ℕ) :
    (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr).component q =
    AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      eqToHom (congrArg (chains (ambient α)).X (show ((m + p) + q) + 1 = ((m + 1) + p) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α) coeff (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr)).f (((m + 1) + p) + q) ≫
      (refinedCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR).component q := rfl

theorem metric_homology_eq (q : ℕ) :
    (SingleCutBoundedCanonicalThomTime.operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA).homology q =
      (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr).homology q := by
  apply RegradedTimeCoverComparison.homology_eq (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ))
    (OriginalFirstHalfFactorwiseCover.first σ) Prod.snd (fun _ _ hz => hz.2)
    (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr) (OriginalFirstHalfFactorwiseCover.first_open σ)
    (OriginalFirstHalfFactorwiseCover.first_univ hσ) (TopCat.of P)
    (AnnularTimeTrim.slice (TopCat.of P) 0) (AnnularTimeTrim.slice (TopCat.of P) 1)
    ((AnnularTimeTrim.cylinder (TopCat.of P)).toSSet.chainComplexMap coeff)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)) (m + p) ((m + 1) + p) (by omega) (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
  · exact SingleCutBoundedCanonicalThomTime.component_normal α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA
  · intro j
    rw [component_normal]
    simp only [refinedCap, DegreeLoweringHomology.Map.pre, HomologicalComplex.comp_f, Category.assoc,
      AnnularTimeTrim.prism, SingleCutCanonicalFilteredCommonAgreement.rightMap]

def retained := (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr).post
  (SingleCutCanonicalFilteredCommonAgreement.retained α r hr κ F ε a L)

theorem retained_metric_homology_eq (q : ℕ) :
    (SingleCutBoundedCanonicalThomTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA).homology q =
      (retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr).homology q := by
  rw [SingleCutBoundedCanonicalThomTime.retained, retained,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology,
    metric_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr q]
  rfl

variable (hRR : R ≤ SelfCutLengthControl.radius F hε)

theorem retained_component (q : ℕ) :
    (retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr).component q =
    AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      eqToHom (congrArg (chains (ambient α)).X (show ((m + p) + q) + 1 = ((m + 1) + p) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α) coeff (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr)).f (((m + 1) + p) + q) ≫
      (SingleCutCanonicalFilteredCommonAgreement.leftMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      (SingleCutCanonicalTwoStage.operation α r F a R hrR hA hR ε h hε hRR L p T hT hshortT).component q := by
  dsimp only [retained, DegreeLoweringHomology.Map.post]
  rw [component_normal]
  simp only [refinedCap, DegreeLoweringHomology.Map.pre, Category.assoc]
  rw [← SingleCutCanonicalFilteredCommonAgreement.filtered_component α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hRR q]

end
end Finsler.SingleCutCanonicalCommonTime
