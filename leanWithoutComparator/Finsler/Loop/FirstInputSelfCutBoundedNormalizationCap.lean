module

public import Finsler.Loop.FirstInputSelfCutBoundedOperations

/-! The literal normalization primitive has its full cap boundary
inside the individual length bound, with the real normalized/raw
boundary source. Only actual chain source monicity is used. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedNormalizationCap

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


def boundaryCap (q : ℕ) :=
  eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
    (show ((m + p) + 1) + q = ((m + 1) + p) + q by omega)) ≫
  ((FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA true).component q -
    (FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA false).component q)

theorem boundary_to_proper (q : ℕ) :
    boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q ≫
      (FirstInputSelfCutBoundedSpace.toProperSmall α r hr F (a - L + 3 * ε) κ).f q =
    (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f (((m + p) + 1) + q) ≫
      FirstInputSelfCutNormalizationCap.boundaryCap α r hr κ h p T hT q := by
  dsimp only [boundaryCap]
  rw [Category.assoc, Preadditive.sub_comp, FirstInputSelfCutBoundedOperations.operation_to_proper,
    FirstInputSelfCutBoundedOperations.operation_to_proper]
  have hm := LocalizedCapCupComponentSource.transport_f
    (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst)
    (((m + p) + 1) + q) (((m + 1) + p) + q) (by omega)
  have hh := congrArg (fun f => f ≫
    ((FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT).component q -
      (FirstInputSelfCutOperations.rawOperation α r hr κ h p T hT).component q)) hm
  simpa only [FirstInputSelfCutTime.refinedCap, DegreeLoweringHomology.Map.pre,
    FirstInputSelfCutTime.properCap, Bool.false_eq_true, ↓reduceIte,
    FirstInputSelfCutNormalizationCap.boundaryCap, Preadditive.comp_sub, Category.assoc] using hh

theorem boundary_source (q : ℕ) :
    boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (((m + p) + 1) + q) ≫
      absoluteChain (ambient α) ((m + p) + 1) q (((m + p) + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α) (m + p) (primitive α r hr h p T)) := by
  have hm := congrArg (fun f => f.f q)
    (FirstInputSelfCutBoundedSpace.proper_source_square α r hr F (a - L + 3 * ε) κ)
  simp only [HomologicalComplex.comp_f] at hm
  rw [← hm, ← Category.assoc, boundary_to_proper, Category.assoc,
    FirstInputSelfCutNormalizationCap.boundary_source, ← Category.assoc]
  have hi := congrArg (fun f => f.f (((m + p) + 1) + q))
    (SmallRefinementComparison.refinement_inclusion (X := ambient α)
      (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst)
  simp only [HomologicalComplex.comp_f] at hi
  rw [FirstInputSelfCutBoundedFactorization.firstMap, hi]

theorem boundary (q : ℕ) :
    FirstInputSelfCutBoundedOperations.primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA (q + 1) ≫
      (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q =
    (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).d ((m + p) + (q + 1)) ((m + p) + q) ≫
      FirstInputSelfCutBoundedOperations.primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q -
    eqToHom (congrArg (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).X
      (show (m + p) + (q + 1) = ((m + p) + 1) + q by omega)) ≫
      boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q :=
  LiftedCapCochainBoundary.boundary (OriginalFirstHalfFactorwiseCover.first σ)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
    (m + p) (primitive α r hr h p T)
    (FirstInputSelfCutBoundedOperations.primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (FirstInputSelfCutBoundedOperations.primitive_source α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (boundary_source α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA) q

end
end Finsler.FirstInputSelfCutBoundedNormalizationCap
