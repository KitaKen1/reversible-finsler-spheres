module

public import Finsler.Loop.FirstInputSelfCutBoundedParent

/-! Actual cap lifts into the individually bounded first-cut carrier.
The old proper cap is recovered by its real source square. Closure only
on proper/far pieces suffices for the genuine chain operation. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedCarrierCap

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
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ ρ : ℝ)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) (ambient α) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) d φ = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshort : cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
    (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) d
      (cochainPullback (source α r) d φ) = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)


theorem lift_source : SmallCapSubspaceLift.source (ambient α)
    (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)) (Iso.refl _) =
    FirstInputSelfCutBoundedSpace.source α r hr F (a - L + 3 * ε) := by
  simp only [SmallCapSubspaceLift.source, Iso.refl_hom, Category.id_comp, FirstInputSelfCutBoundedSpace.source]

def component (q : ℕ) := SmallCapSubspaceLift.component (ambient α)
  (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
  (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)) (Iso.refl _)
  (OriginalFirstHalfFactorwiseCover.first σ) (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)
  d φ (fun q s hnz => by
    rw [lift_source]
    exact FirstInputSelfCutBoundedParent.parent_image α r hr κ ρ d φ hfar F ε a L σ hε hradius
      hsmall firstIndex hfirst hshort hA q s hnz) q

theorem component_source (q : ℕ) :
    component α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA q ≫
      (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ).f q =
    (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f (d + q) ≫
      absoluteChain (ambient α) d q (d + q) rfl φ := by
  have hc := SmallCapSubspaceLift.component_inclusion (ambient α)
    (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)) (Iso.refl _)
    (OriginalFirstHalfFactorwiseCover.first σ) (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)
    d φ (fun q s hnz => by
      rw [lift_source]
      exact FirstInputSelfCutBoundedParent.parent_image α r hr κ ρ d φ hfar F ε a L σ hε hradius
        hsmall firstIndex hfirst hshort hA q s hnz) q
  simpa only [component, SmallCapSubspaceLift.target, SmallCapSubspaceLift.source,
    Iso.refl_hom, Category.id_comp, FirstInputSelfCutBoundedSpace.sourceChain,
    FirstInputSelfCutBoundedSpace.source] using hc

theorem component_to_proper (q : ℕ) :
    component α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA q ≫
      (FirstInputSelfCutBoundedSpace.toProperSmall α r hr F (a - L + 3 * ε) κ).f q =
    (FirstInputSelfCutBoundedFactorization.firstMap α r hr σ firstIndex hfirst).f (d + q) ≫
      FirstInputSelfCutCarrierCap.component α r hr κ ρ d φ hfar q := by
  haveI := FirstInputSelfCutTime.sourceMap_mono α r hr κ q
  have hm := congrArg (fun f => f.f q)
    (FirstInputSelfCutBoundedSpace.proper_source_square α r hr F (a - L + 3 * ε) κ)
  simp only [HomologicalComplex.comp_f] at hm
  have hc : FirstInputSelfCutCarrierCap.component α r hr κ ρ d φ hfar q ≫
      (FirstInputSelfCutTime.sourceMap α r hr κ).f q =
      (inclusion (ambient α) (cover α r hr κ ρ)).f (d + q) ≫ absoluteChain (ambient α) d q (d + q) rfl φ := by
    simpa only [FirstInputSelfCutTime.sourceMap, HomologicalComplex.comp_f, Category.assoc] using
      FirstInputSelfCutCarrierCap.component_source α r hr κ ρ d φ hfar q
  have hi := congrArg (fun f => f.f (d + q))
    (SmallRefinementComparison.refinement_inclusion (X := ambient α)
      (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst)
  simp only [HomologicalComplex.comp_f] at hi
  apply (cancel_mono ((FirstInputSelfCutTime.sourceMap α r hr κ).f q)).mp
  simp only [Category.assoc]
  rw [hm, component_source, hc, ← Category.assoc]
  rw [FirstInputSelfCutBoundedFactorization.firstMap, hi]

variable (hproper : cochainPullback (source α r) (d + 1) (cochainCoboundary (ZMod 2) (ambient α) d φ) = 0)

include hproper in
theorem component_comm (q : ℕ) :
    component α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA (q + 1) ≫
      (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q =
    (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).d (d + (q + 1)) (d + q) ≫
      component α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA q := by
  have hz (q : ℕ) :
      (inclusion (ambient α) (OriginalFirstHalfFactorwiseCover.first σ)).f ((d + 1) + q) ≫
      absoluteChain (ambient α) (d + 1) q ((d + 1) + q) rfl
        (cochainCoboundary (ZMod 2) (ambient α) d φ) = 0 := by
    have hi := congrArg (fun f => f.f ((d + 1) + q))
      (SmallRefinementComparison.refinement_inclusion (X := ambient α)
        (OriginalFirstHalfFactorwiseCover.first σ) (cover α r hr κ ρ) firstIndex hfirst)
    simp only [HomologicalComplex.comp_f] at hi
    rw [← hi, Category.assoc, FirstInputSelfCutCarrierCap.small_boundary_zero α r hr κ ρ d φ hfar hproper q, comp_zero]
  have hb := LiftedCapCochainBoundary.boundary (OriginalFirstHalfFactorwiseCover.first σ)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ) d φ
    (component α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA) (fun _ => 0)
    (component_source α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA)
    (fun q => by rw [zero_comp, hz q]) q
  simpa only [comp_zero, sub_zero] using hb

def operation : DegreeLoweringHomology.Map (small (ambient α) (OriginalFirstHalfFactorwiseCover.first σ))
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)) d where
  component := component α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA
  comm := component_comm α r hr κ ρ d φ hfar F ε a L σ hε hradius hsmall firstIndex hfirst hshort hA hproper

end
end Finsler.FirstInputSelfCutBoundedCarrierCap
