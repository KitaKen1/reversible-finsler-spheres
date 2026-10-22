module

public import Finsler.Loop.CanonicalFilteredCapFactor
public import Finsler.Loop.SingleCutCanonicalFilteredCommonAgreement
public import Finsler.Loop.RegradedTimeCoverComparison
public import Finsler.Loop.SingleCutBoundedCanonicalThomTime
public import Finsler.Loop.SingleCutCanonicalThomEndpoints
public import Finsler.Loop.RegradedSingleCapTime

/-! Map the actual common source cover to the canonical far/near
cover. The localized canonical cap after this genuine small map is
exactly the common filtered two-stage cap, with native time degrees. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalMappedCap

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

theorem maps (i) : Set.MapsTo (CompactInputShortMaps.cylinder α F a hA)
    (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ) i)
    (CanonicalFilteredLocalizedCap.cover F a ρ R i.1.isSome) := by
  intro z hz
  exact SingleCutCanonicalThomSmallLift.canonical_refines α r F a R hrR hA hR ε i.1 hz.1

def mapped := SmallRetractionComparison.map
  (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ))
  (CanonicalFilteredLocalizedCap.cover F a ρ R) (CompactInputShortMaps.cylinder α F a hA)
  (fun i => i.1.isSome) (maps α r F ε a σ hA R hrR hR (ρ := ρ))

theorem mapped_source : mapped α r F ε a σ hA R hrR hR (ρ := ρ) ≫
    inclusion (FilteredPrismSelfCut.domain F a) (CanonicalFilteredLocalizedCap.cover F a ρ R) =
    inclusion (ambient α) (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) ≫
      push (CompactInputShortMaps.cylinder α F a hA) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

include hρr in
theorem mapped_retraction : mapped α r F ε a σ hA R hrR hR (ρ := ρ) =
    inclusion (ambient α) (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ)) ≫
      push (CompactInputShortMaps.cylinder α F a hA) ≫
      TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff
        (CanonicalFilteredLocalizedCap.cover F a ρ R) (CanonicalFilteredLocalizedCap.cover_open F a ρ R)
        (CanonicalFilteredLocalizedCap.cover_univ F a ρ R (hρr.trans hrR)) := by
  have hh := congrArg (fun f => f ≫ TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff
    (CanonicalFilteredLocalizedCap.cover F a ρ R) (CanonicalFilteredLocalizedCap.cover_open F a ρ R)
    (CanonicalFilteredLocalizedCap.cover_univ F a ρ R (hρr.trans hrR)))
    (mapped_source α r F ε a σ hA R hrR hR (ρ := ρ))
  rw [Category.assoc, TauCeti.ι_comp_smallSingularRetraction, Category.comp_id] at hh
  simpa only [Category.assoc] using hh

variable (hRR : R ≤ SelfCutLengthControl.radius F hε)

include hρr in
theorem component (q : ℕ) :
    (mapped α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      (CanonicalFilteredLocalizedCap.operation F a ρ R (h.1.trans h.2.2) hR ε hε hRR L p T hT hshortT).component q =
    (SingleCutCanonicalFilteredCommonAgreement.leftMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      (SingleCutCanonicalTwoStage.operation α r F a R hrR hA hR ε h hε hRR L p T hT hshortT).component q := by
  rw [CanonicalFilteredCapFactor.actual_common F a ρ R (h.1.trans h.2.2) hR ε hε hRR L p T hT hshortT α hA r hrR h hρr q]
  have hm := congrArg (fun f => f.f (((m + 1) + p) + q))
    (mapped_retraction α r F ε a σ hA R hrR hR hρr)
  have hl := congrArg (fun f => f.f (((m + 1) + p) + q))
    (SingleCutCanonicalFilteredCommonAgreement.left_source α r F ε a σ hA R hrR hR (ρ := ρ))
  simp only [HomologicalComplex.comp_f] at hm hl ⊢
  rw [hm]
  simp only [Category.assoc]
  rw [← CanonicalFilteredCapFactor.component_retraction F a ρ R (h.1.trans h.2.2) (hρr.trans hrR) hR ε hε hRR L p T hT hshortT q]
  simpa only [Category.assoc] using congrArg (fun f => f ≫
    (push (CompactInputShortMaps.cylinder α F a hA)).f (((m + 1) + p) + q) ≫
      (CanonicalFilteredCapFactor.original F a ρ R (h.1.trans h.2.2) (hρr.trans hrR) hR ε hε hRR L p T hT hshortT).component q) hl.symm

include hρr in
theorem aligned_component (q : ℕ) :
    (mapped α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + p) + q) + 1) ≫
      CanonicalFilteredLocalizedCap.indexed F a ρ R (h.1.trans h.2.2) hR ε hε hRR L p T hT hshortT q =
    eqToHom (congrArg (small (ambient α)
      (SingleCutCanonicalFilteredCommonAgreement.common α r F ε a σ hA R hrR hR (ρ := ρ))).X
      (show ((m + p) + q) + 1 = ((m + 1) + p) + q by omega)) ≫
      (SingleCutCanonicalFilteredCommonAgreement.leftMap α r F ε a σ hA R hrR hR (ρ := ρ)).f (((m + 1) + p) + q) ≫
      (SingleCutCanonicalTwoStage.operation α r F a R hrR hA hR ε h hε hRR L p T hT hshortT).component q := by
  dsimp only [CanonicalFilteredLocalizedCap.indexed, DegreeLoweringSuccAlignment.align]
  have ht := LocalizedCapCupComponentSource.transport_f
    (mapped α r F ε a σ hA R hrR hR (ρ := ρ))
    (((m + p) + q) + 1) (((m + 1) + p) + q) (by omega)
  rw [← Category.assoc, ← ht, Category.assoc,
    component α r h p T hT F ε a L σ hε hshortT hA R hrR hR hρr hRR q]

end
end Finsler.SingleCutCanonicalMappedCap
