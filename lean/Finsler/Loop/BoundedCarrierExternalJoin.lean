module

public import Finsler.Loop.BoundedCarrierJoinNaturality
public import Finsler.Loop.FirstFactorSectionedSmallCross

/-! A genuine closed normalized join operation on the bounded carrier's
small external tensor. Its native homogeneous components map strictly
to the original proper-cut external join in every output degree. -/

@[expose] public section
namespace Finsler.BoundedCarrierExternalJoin

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B κ R : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

def operation := (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).pre
  (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ)
    (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ))

def component (i j k : ℕ) (hij : i + j = (m + 1) + k) :=
  SmallNormalizedCapShuffle.component (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ)
    (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j ≫
  eqToHom (congrArg (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
    (BoundedCarrierJoinCap.rectangles α β r hr F B κ)).X hij) ≫
  (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).component k

theorem on_summand (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    ιTensorObj (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ))
      (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) i j ((m + 1) + k) hij ≫
      (operation α β r hr F B κ R hκ hκR).component k = component α β r hr F B κ R hκ hκR i j k hij := by
  have he := FirstFactorSectionedSmallCross.summand_map
    (SmallRectangleCross.cross (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ)
      (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) i j ((m + 1) + k) hij
  exact congrArg (fun z => z ≫ (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).component k) he

theorem component_to_proper (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    component α β r hr F B κ R hκ hκR i j k hij ≫
      (push (BoundedKeptProductInputs.properTube α β r hr F B R)).f k =
    ((FirstInputSelfCutBoundedSpace.toProperSmall α r hr F B κ).f i ⊗ₘ
      𝟙 ((small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).X j)) ≫
    SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
      (FirstInputSelfCutCover.carrier α r hr κ)
      (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j ≫
    eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).X hij) ≫
    (CompactJoinCapLocalization.localized (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ hκR).component k := by
  have ht := LocalizedCapCupComponentSource.transport_f (BoundedCarrierJoinCap.properRectangle α β r hr F B κ)
    (i + j) ((m + 1) + k) hij
  dsimp only [component]
  simp only [Category.assoc]
  rw [← BoundedCarrierJoinNaturality.cap α β r hr F B κ R hκ hκR k]
  rw [← Category.assoc (eqToHom _), ht]
  simp only [← Category.assoc]
  rw [← BoundedCarrierJoinNaturality.cross α β r hr F B κ i j]

end
end Finsler.BoundedCarrierExternalJoin
