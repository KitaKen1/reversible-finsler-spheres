module

public import Finsler.Loop.SingleCutCanonicalMappedCap
public import Finsler.Loop.TimeMappedRetractionComparison
public import Finsler.Loop.SingleCutBoundedThomComparison
public import Finsler.Loop.SingleCutCanonicalCommonTime
public import Finsler.Loop.RegradedTimeCoverComparison
public import Finsler.Loop.SingleCutBoundedCanonicalThomTime
public import Finsler.Loop.SingleCutCanonicalThomEndpoints
public import Finsler.Loop.RegradedSingleCapTime

/-! Remove the actual common-small-source restriction from time
comparison. Genuine canonical family D_T and the constructed filtered
annular time maps agree in the same literal short target. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalFullTime

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

variable (hRR : R ≤ SelfCutLengthControl.radius F hε)

theorem canonical_common_homology_eq (q : ℕ) :
    (SingleCutCanonicalTwoStage.familyOperation α F a R hA hR ε h hε hRR L p T hT hshortT (hρr.trans hrR)).homology q =
      (SingleCutCanonicalCommonTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr).homology q := by
  apply TimeMappedRetractionComparison.homology_eq (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ))
    (CanonicalFilteredLocalizedCap.cover F a ρ R) (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr)
    (CanonicalFilteredLocalizedCap.cover_open F a ρ R)
    (CanonicalFilteredLocalizedCap.cover_univ F a ρ R (hρr.trans hrR))
    (CompactInputShortMaps.cylinder α F a hA) (fun i => i.1.isSome)
    (SingleCutCanonicalMappedCap.maps α r F ε a σ hA R hrR hR (ρ := ρ))
    (TopCat.of P) (AnnularTimeTrim.slice (TopCat.of P) 0) (AnnularTimeTrim.slice (TopCat.of P) 1)
    ((AnnularTimeTrim.cylinder (TopCat.of P)).toSSet.chainComplexMap coeff)
    (chains (TopCat.of (SelfCutOscillation.short F (a - L + 3 * ε)))) (m + p)
    (CanonicalFilteredLocalizedCap.indexed F a ρ R (h.1.trans h.2.2) hR ε hε hRR L p T hT hshortT)
    (CanonicalFilteredLocalizedCap.indexed_comm F a ρ R (h.1.trans h.2.2) hR ε hε hRR L p T hT hshortT)
  · exact CanonicalFilteredLocalizedCap.family_component F a ρ R (h.1.trans h.2.2) (hρr.trans hrR) hR ε hε hRR L p T hT hshortT α hA
  · intro j
    rw [SingleCutCanonicalCommonTime.retained_component α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr hRR j]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    have hu := SingleCutCanonicalMappedCap.aligned_component α r h p T hT F ε a L σ hε hshortT hA R hrR hR hρr hRR j
    dsimp only [SingleCutCanonicalMappedCap.mapped] at hu
    rw [hu]
    have ht := LocalizedCapCupComponentSource.transport_f (TauCeti.smallSingularRetraction (X := ambient α) coeff (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_open α r F ε a σ hA R hrR hR (ρ := ρ)) (SingleCutCanonicalFilteredCommonAgreement.common_univ α r F ε a σ hε hA R hrR hR hσ hρr))
      (((m + p) + j) + 1) (((m + 1) + p) + j) (by omega)
    simpa only [AnnularTimeTrim.prism, Category.assoc] using congrArg (fun f =>
      AnnularTimeTrim.prism (TopCat.of P) ((m + p) + j) ≫ f ≫
      (SingleCutCanonicalFilteredCommonAgreement.leftMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + j) ≫
      (SingleCutCanonicalTwoStage.operation α r F a R hrR hA hR ε h hε hRR L p T hT hshortT).component j) ht

theorem bounded_canonical_homology_eq (q : ℕ) :
    (SingleCutBoundedCanonicalThomTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA).homology q =
      (SingleCutCanonicalTwoStage.familyOperation α F a R hA hR ε h hε hRR L p T hT hshortT (hρr.trans hrR)).homology q :=
  (SingleCutCanonicalCommonTime.retained_metric_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr q).trans
    (canonical_common_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr hRR q).symm

variable (hm : 1 ≤ m) (hρ2 : ρ ≤ 2)

include hm hρ2 in
theorem raw_canonical_homology_eq (q : ℕ) :
    (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA false).homology q =
      (SingleCutCanonicalTwoStage.familyOperation α F a R hA hR ε h hε hRR L p T hT hshortT (hρr.trans hrR)).homology q :=
  (SingleCutBoundedThomComparison.retained_homology_eq α r hr κ h p T hm hρ2 hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q).trans
    (bounded_canonical_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr hRR q)

include hm hρ2 in
theorem normalized_canonical_homology_eq (q : ℕ) :
    (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA true).homology q =
      (SingleCutCanonicalTwoStage.familyOperation α F a R hA hR ε h hε hRR L p T hT hshortT (hρr.trans hrR)).homology q :=
  (SingleCutBoundedThomComparison.normalized_retained_homology_eq α r hr κ h p T hm hρ2 hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q).trans
    (bounded_canonical_homology_eq α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA R hrR hR hρr hRR q)

end
end Finsler.SingleCutCanonicalFullTime
