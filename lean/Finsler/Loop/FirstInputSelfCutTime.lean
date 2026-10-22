module

public import Finsler.Loop.RegradedSingleCapTime
public import Finsler.Loop.FirstInputSelfCutBoundedFactorization
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! Genuine raw and normalized single-input cut-time operations in
the actual proper-cut small complex. Both endpoint zeros come from the
actual inner collar. The optional common-input section has the same
homology map and an exact common-prism component. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutTime

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (σ : ℝ) (hσ : 0 < σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))

def cochain (v : Bool) := if v then normalized α r hr h p T else raw α r hr h p T

def properCap (v : Bool) := if v then FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT
  else FirstInputSelfCutOperations.rawOperation α r hr κ h p T hT

def sourceMap := inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ) ≫ push (source α r)

theorem sourceMap_mono (q : ℕ) : Mono ((sourceMap α r hr κ).f q) :=
  FirstInputSelfCutCarrierCap.target_mono α r hr κ q

theorem proper_source (v : Bool) (q : ℕ) :
    (properCap α r hr κ h p T hT v).component q ≫ (sourceMap α r hr κ).f q =
    (inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl (cochain α r hr h p T v) := by
  cases v
  · simpa only [properCap, cochain, Bool.false_eq_true, ↓reduceIte, sourceMap, HomologicalComplex.comp_f, Category.assoc] using
      FirstInputSelfCutOperations.raw_source α r hr κ h p T hT q
  · simpa only [properCap, cochain, ↓reduceIte, sourceMap, HomologicalComplex.comp_f, Category.assoc] using
      FirstInputSelfCutOperations.normalized_source α r hr κ h p T hT q

def refinedCap (v : Bool) := (properCap α r hr κ h p T hT v).pre
  (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst)

theorem refined_source (v : Bool) (q : ℕ) :
    (refinedCap α r hr κ h p T hT σ firstIndex hfirst v).component q ≫ (sourceMap α r hr κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl (cochain α r hr h p T v) := by
  dsimp only [refinedCap, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, proper_source, ← Category.assoc]
  have hi := congrArg (fun f => f.f (((m + 1) + p) + q))
    (SmallRefinementComparison.refinement_inclusion (X := ambient α)
      (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst)
  simp only [HomologicalComplex.comp_f] at hi
  rw [FirstInputSelfCutBoundedFactorization.firstMap, hi]

theorem inner_zero (v : Bool) :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) ((m + 1) + p) (cochain α r hr h p T v) = 0 := by
  cases v
  · exact raw_inner_zero α r hr h p T
  · exact normalized_inner_zero α r hr h p T

def cap (v : Bool) (q : ℕ) := RegradedSingleCapTime.cap (TopCat.of P)
  (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
  (OriginalFirstHalfFactorwiseCover.first_univ hσ)
  (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ))
  (m + p) ((m + 1) + p) (by omega) (refinedCap α r hr κ h p T hT σ firstIndex hfirst v) q

theorem cap_comm (v : Bool) (q : ℕ) :
    cap α r hr κ h p T hT σ hσ firstIndex hfirst v (q + 1) ≫
      (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).d (q + 1) q =
    (chains (ambient α)).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ cap α r hr κ h p T hT σ hσ firstIndex hfirst v q :=
  RegradedSingleCapTime.cap_comm _ _ _ _ _ _ _ _ _ q

theorem endpoint_zero (v : Bool) (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of P) t)).f ((m + p) + q + 1) ≫
      cap α r hr κ h p T hT σ hσ firstIndex hfirst v q = 0 := by
  apply RegradedSingleCapTime.endpoint_zero (TopCat.of P)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
    (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ))
    (m + p) ((m + 1) + p) (by omega) (refinedCap α r hr κ h p T hT σ firstIndex hfirst v)
    (inner α δ) (cochain α r hr h p T v) (inner_zero α r hr h p T v)
    (sourceMap α r hr κ) (sourceMap_mono α r hr κ) (refined_source α r hr κ h p T hT σ firstIndex hfirst v) t _ q
  intro x
  rcases ht with rfl | rfl
  · exact (UniformSelfCutCollar.distance_zero α x).le.trans h.1.le
  · exact (UniformSelfCutCollar.distance_one α x).le.trans h.1.le

def operation (v : Bool) : DegreeLoweringHomology.Map (chains (TopCat.of P))
    (small (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)) (m + p) :=
  TimePrismDescent.operation ((AnnularTimeTrim.cylinder (TopCat.of P)).toSSet.chainComplexMap coeff) (m + p)
    (cap α r hr κ h p T hT σ hσ firstIndex hfirst v) (cap_comm α r hr κ h p T hT σ hσ firstIndex hfirst v)
    (endpoint_zero α r hr κ h p T hT σ hσ firstIndex hfirst v 0 (Or.inl rfl))
    (endpoint_zero α r hr κ h p T hT σ hσ firstIndex hfirst v 1 (Or.inr rfl))

theorem component_normal (v : Bool) (q : ℕ) :
    (operation α r hr κ h p T hT σ hσ firstIndex hfirst v).component q =
    AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      eqToHom (congrArg (chains (ambient α)).X (show (m + p) + q + 1 = ((m + 1) + p) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + 1) + p) + q) ≫
      (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f (((m + 1) + p) + q) ≫
      (properCap α r hr κ h p T hT v).component q := rfl

def sectioned (v : Bool) := (operation α r hr κ h p T hT σ hσ firstIndex hfirst v).pre
  (TauCeti.smallSingularRetraction (X := TopCat.of P) coeff
    (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ))
    (CommonPrismRefinement.endpointCover_open (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ))
    (CommonPrismRefinement.endpointCover_univ (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_univ hσ)) ≫
    inclusion (TopCat.of P) (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)))

theorem sectioned_homology (v : Bool) (q : ℕ) :
    (sectioned α r hr κ h p T hT σ hσ firstIndex hfirst v).homology q =
      (operation α r hr κ h p T hT σ hσ firstIndex hfirst v).homology q := by
  rw [sectioned, DegreeLoweringHomology.Map.pre_homology, homologyMap_comp,
    SmallInclusionHomologyCancellation.homology_section, Category.id_comp]

theorem sectioned_component (v : Bool) (q : ℕ) :
    (sectioned α r hr κ h p T hT σ hσ firstIndex hfirst v).component q =
    (TauCeti.smallSingularRetraction (X := TopCat.of P) coeff
      (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ))
      (CommonPrismRefinement.endpointCover_open (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ))
      (CommonPrismRefinement.endpointCover_univ (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_univ hσ))).f ((m + p) + q) ≫
    (CommonPrismRefinement.prism (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)).hom
      ((m + p) + q) ((m + p) + q + 1) ≫ cap α r hr κ h p T hT σ hσ firstIndex hfirst v q := rfl

end
end Finsler.FirstInputSelfCutTime
