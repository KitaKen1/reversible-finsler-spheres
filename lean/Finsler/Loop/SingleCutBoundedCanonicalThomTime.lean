module

public import Finsler.Loop.SingleCutBoundedCanonicalThomCap
public import Finsler.Loop.SingleCutCanonicalThomEndpoints
public import Finsler.Loop.RegradedSingleCapTime

/-! Genuine canonical Thom/tested cup time operation in the individual
length-bounded carrier, with actual time descent and literal endpoint
support. Identification with the separately specified canonical D_T
still requires the two-stage cap and radius comparisons. -/

@[expose] public section
namespace Finsler.SingleCutBoundedCanonicalThomTime

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


def cap := RegradedSingleCapTime.cap (TopCat.of P)
  (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
  (OriginalFirstHalfFactorwiseCover.first_univ hσ)
  (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
  (m + p) ((m + 1) + p) (by omega)
  (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)

theorem cap_comm (q : ℕ) :
    cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA (q + 1) ≫
      (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)).d (q + 1) q =
    (chains (ambient α)).d ((m + p) + q + 2) ((m + p) + q + 1) ≫
      cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q :=
  RegradedSingleCapTime.cap_comm (TopCat.of P)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
    (OriginalFirstHalfFactorwiseCover.first_univ hσ) _ _ _ (by omega) _ q

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (AnnularTimeTrim.slice (TopCat.of P) t)).f ((m + p) + q + 1) ≫
      cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA q = 0 :=
  RegradedSingleCapTime.endpoint_zero (TopCat.of P)
    (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.first_open σ)
    (OriginalFirstHalfFactorwiseCover.first_univ hσ)
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
    (m + p) ((m + 1) + p) (by omega)
    (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    (SingleCutCanonicalThomEndpoints.sliceSet α t) (SingleCutCanonicalThomCochains.canonicalGamma α r hr h p T)
    (SingleCutCanonicalThomEndpoints.gamma_slice_zero α h r hr p T t ht)
    (FirstInputSelfCutBoundedSpace.sourceChain α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedSpace.sourceChain_mono α r hr F (a - L + 3 * ε) κ)
    (SingleCutBoundedCanonicalThomCap.operation_source α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA)
    t (fun _ => rfl) q

def operation := TimePrismDescent.operation
  ((AnnularTimeTrim.cylinder (TopCat.of P)).toSSet.chainComplexMap coeff) (m + p)
  (cap α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA)
  (cap_comm α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA)
  (endpoint_zero α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA 0 (Or.inl rfl))
  (endpoint_zero α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA 1 (Or.inr rfl))

theorem component_normal (q : ℕ) :
    (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA).component q =
    AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      eqToHom (congrArg (chains (ambient α)).X (show ((m + p) + q) + 1 = ((m + 1) + p) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := ambient α) coeff (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ) (OriginalFirstHalfFactorwiseCover.first_univ hσ)).f (((m + 1) + p) + q) ≫
      (SingleCutBoundedCanonicalThomCap.operation α r hr κ h p T hT F ε a L σ hε hradius hsmall firstIndex hfirst hshortT hA).component q := rfl

def retained :=
  (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA).post
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
      push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε)))

def sectioned :=
  (operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA).pre
    (TauCeti.smallSingularRetraction (X := TopCat.of P) coeff
      (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ))
      (CommonPrismRefinement.endpointCover_open (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_open σ))
      (CommonPrismRefinement.endpointCover_univ (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)
        (OriginalFirstHalfFactorwiseCover.first_univ hσ)) ≫
      inclusion (TopCat.of P) (CommonPrismRefinement.endpointCover (TopCat.of P) (OriginalFirstHalfFactorwiseCover.first σ)))

end
end Finsler.SingleCutBoundedCanonicalThomTime
