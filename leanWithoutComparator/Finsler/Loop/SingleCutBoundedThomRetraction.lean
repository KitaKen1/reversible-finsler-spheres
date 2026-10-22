module

public import Finsler.Loop.SingleCutBoundedCanonicalThomCap
public import Finsler.Loop.SingleCutCanonicalThomEndpoints
public import Finsler.Loop.CapCochainBoundaryPre
public import Finsler.Loop.SingleCapSourceCollar

/-! Complete annular/canonical Thom comparison cap boundary after actual
metric subdivision, in the same individual length-bound carrier. Both
primitive time endpoint terms vanish by their literal slice supports. -/

@[expose] public section
namespace Finsler.SingleCutBoundedThomRetraction

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
  (hm : 1 ≤ m) (hρ2 : ρ ≤ 2)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)



def retractedPrimitive (q : ℕ) :=
  (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f ((m + p) + q) ≫
    SingleCutBoundedCanonicalThomCap.primitiveCap α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q

def retractedBoundary (q : ℕ) :=
  (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + p) + 1) + q) ≫
    SingleCutBoundedCanonicalThomCap.boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q

theorem retracted_boundary (q : ℕ) :
    retractedPrimitive α r hr κ h p T hm hρ2 F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA (q + 1) ≫
      (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q =
    (chains (ambient α)).d ((m + p) + (q + 1)) ((m + p) + q) ≫
      retractedPrimitive α r hr κ h p T hm hρ2 F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q -
    eqToHom (congrArg (chains (ambient α)).X
      (show (m + p) + (q + 1) = ((m + p) + 1) + q by omega)) ≫
      retractedBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q :=
  CapCochainBoundaryPre.pre
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)) (m + p)
    (SingleCutBoundedCanonicalThomCap.primitiveCap α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (SingleCutBoundedCanonicalThomCap.boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (SingleCutBoundedCanonicalThomCap.boundary α r hr κ h p T hm hρ2 hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA) q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of P) t)).f ((m + p) + q) ≫
      retractedPrimitive α r hr κ h p T hm hρ2 F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q = 0 := by
  apply SingleCapSourceCollar.lift_zero (OriginalFirstHalfFactorwiseCover.first σ)
    (SingleCutCanonicalThomEndpoints.sliceSet α t) (m + p)
    (SingleCutCanonicalThomCochains.comparisonPrimitive α r hr h p T hm hρ2)
    (SingleCutCanonicalThomEndpoints.primitive_slice_zero α h r hr p T hm hρ2 t ht)
    (AnnularTimeTrim.slice (TopCat.of P) t) _
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
    (SingleCutBoundedCanonicalThomCap.primitiveCap α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (SingleCutBoundedCanonicalThomCap.primitive_source α r hr κ h p T hm hρ2 F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA) q
  intro x
  rfl

theorem boundary_normal (q : ℕ) :
    retractedBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q =
    eqToHom (congrArg (chains (ambient α)).X
      (show ((m + p) + 1) + q = ((m + 1) + p) + q by omega)) ≫
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + 1) + p) + q) ≫
    ((FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA false).component q -
      (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).component q) := by
  dsimp only [retractedBoundary, SingleCutBoundedCanonicalThomCap.boundaryCap]
  rw [← Category.assoc, ← LocalizedCapCupComponentSource.transport_f
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ))
    (((m + p) + 1) + q) (((m + 1) + p) + q) (by omega)]
  simp only [Category.assoc]

end
end Finsler.SingleCutBoundedThomRetraction
