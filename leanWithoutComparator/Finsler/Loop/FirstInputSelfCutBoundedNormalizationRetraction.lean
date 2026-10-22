module

public import Finsler.Loop.FirstInputSelfCutBoundedNormalizationCap
public import Finsler.Loop.FirstInputSelfCutBoundedTime
public import Finsler.Loop.CapCochainBoundaryPre
public import Finsler.Loop.SingleCapSourceCollar

/-! The actual normalization primitive boundary and both endpoint
collars after metric subdivision, inside the individual length bound. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutBoundedNormalizationRetraction

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



def retractedPrimitive (q : ℕ) :=
  (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f ((m + p) + q) ≫
    FirstInputSelfCutBoundedOperations.primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q

def retractedBoundary (q : ℕ) :=
  (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + p) + 1) + q) ≫
    FirstInputSelfCutBoundedNormalizationCap.boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA q

theorem retracted_boundary (q : ℕ) :
    retractedPrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA (q + 1) ≫
      (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q =
    (chains (ambient α)).d ((m + p) + (q + 1)) ((m + p) + q) ≫
      retractedPrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q -
    eqToHom (congrArg (chains (ambient α)).X
      (show (m + p) + (q + 1) = ((m + p) + 1) + q by omega)) ≫
      retractedBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q :=
  CapCochainBoundaryPre.pre
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)) (m + p)
    (FirstInputSelfCutBoundedOperations.primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (FirstInputSelfCutBoundedNormalizationCap.boundaryCap α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (FirstInputSelfCutBoundedNormalizationCap.boundary α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA) q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of P) t)).f ((m + p) + q) ≫
      retractedPrimitive α r hr κ h p T F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q = 0 := by
  apply SingleCapSourceCollar.lift_zero (OriginalFirstHalfFactorwiseCover.first σ) (inner α δ) (m + p)
    (primitive α r hr h p T) (primitive_inner_zero α r hr h p T) (AnnularTimeTrim.slice (TopCat.of P) t) _
    (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedOperations.primitiveCap α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (FirstInputSelfCutBoundedOperations.primitive_source α r hr κ h p T F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA) q
  intro x
  rcases ht with rfl | rfl
  · exact (UniformSelfCutCollar.distance_zero α x).le.trans h.1.le
  · exact (UniformSelfCutCollar.distance_one α x).le.trans h.1.le

theorem boundary_normal (q : ℕ) :
    retractedBoundary α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q =
    eqToHom (congrArg (chains (ambient α)).X
      (show ((m + p) + 1) + q = ((m + 1) + p) + q by omega)) ≫
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + 1) + p) + q) ≫
    ((FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA true).component q -
      (FirstInputSelfCutBoundedOperations.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA false).component q) := by
  dsimp only [retractedBoundary, FirstInputSelfCutBoundedNormalizationCap.boundaryCap]
  rw [← Category.assoc, ← LocalizedCapCupComponentSource.transport_f
    (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
      (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ))
    (((m + p) + 1) + q) (((m + 1) + p) + q) (by omega)]
  simp only [Category.assoc]

end
end Finsler.FirstInputSelfCutBoundedNormalizationRetraction
