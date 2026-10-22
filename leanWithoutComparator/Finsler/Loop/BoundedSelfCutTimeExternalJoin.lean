module

public import Finsler.Loop.BoundedCarrierExternalJoin
public import Finsler.Loop.FirstInputSelfCutBoundedTime
public import Finsler.Loop.FirstInputSelfCutTimeFactorization

/-! Actual individually bounded self-cut time, actual beta subdivision,
and a genuine closed external join operation factor the original
proper-cut time component. All native transports and input sections
are retained, including output degree zero. -/

@[expose] public section
namespace Finsler.BoundedSelfCutTimeExternalJoin

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ) (hr : r < 1)
  {κ δ ρ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
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
  (otherIndex : Q → Q)
  (hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
    OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c))

def tensorInput (i j : ℕ) :=
  (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA true).component i ⊗ₘ
    FirstInputSelfCutTimeFactorization.otherSection β σ hσ otherIndex hother j

def geometric (i j k : ℕ) (hij : i + j = (m + 1) + k) :=
  tensorInput α β r hr h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA otherIndex hother i j ≫
    BoundedCarrierExternalJoin.component α β r hr F (a - L + 3 * ε) κ R hκ hκR i j k hij

theorem to_proper (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    geometric α β R r hr hκ hκR h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA
      otherIndex hother i j k hij ≫
      (push (BoundedKeptProductInputs.properTube α β r hr F (a - L + 3 * ε) R)).f k =
    FirstInputSelfCutTimeFactorization.geometric α β R r hr hκ hκR h p T hT σ hσ firstIndex hfirst
      otherIndex hother i j k hij := by
  rw [geometric, Category.assoc, BoundedCarrierExternalJoin.component_to_proper]
  dsimp only [tensorInput, FirstInputSelfCutTimeFactorization.geometric]
  simp only [← Category.assoc]
  rw [tensorHom_comp_tensorHom]
  simp only [Category.comp_id]
  rw [FirstInputSelfCutBoundedTime.sectioned_component_to_proper]

theorem closed_join_summand (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    geometric α β R r hr hκ hκR h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA
      otherIndex hother i j k hij =
    tensorInput α β r hr h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA otherIndex hother i j ≫
      ιTensorObj (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
        (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) i j ((m + 1) + k) hij ≫
      (BoundedCarrierExternalJoin.operation α β r hr F (a - L + 3 * ε) κ R hκ hκR).component k := by
  exact (congrArg (fun z => tensorInput α β r hr h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA otherIndex hother i j ≫ z)
    (BoundedCarrierExternalJoin.on_summand α β r hr F (a - L + 3 * ε) κ R hκ hκR i j k hij)).symm

end
end Finsler.BoundedSelfCutTimeExternalJoin
