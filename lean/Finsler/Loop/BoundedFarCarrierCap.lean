module

public import Finsler.Loop.CompactFarCarrierCap
public import Finsler.Loop.BoundedCarrierJoinCap

/-! Arbitrary-degree far-supported cochains, including actual nonclosed
comparison primitives, cap the original proper-centered bounded
rectangles into the very same closed bounded near carrier. -/

@[expose] public section
namespace Finsler.BoundedFarCarrierCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B κ R : ℝ) (hκR : 2 * κ ≤ R)
  (d : ℕ) (φ : singularCochainGroup (ZMod 2) (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) d)
  (hfar : cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
    (NearFarCapComparison.far (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
      (fun x => basepoint (OriginalFirstHalfCutOutputJoinData.kept α r hr x)) (fun y => basepoint (β y)) κ)) d φ = 0)

include hκR hfar in
theorem parent_good (q : ℕ)
    (σ : ((TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)).smallSingularSubcomplex
      (BoundedCarrierJoinCap.rectangles α β r hr F B κ) : SSet) _⦋d + q⦌)
    (hn : (TopCat.toSSet.obj (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))).ιChainComplex σ.val ≫
      absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) d q (d + q) rfl
        (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) d φ) ≠ 0) :
    Set.range ((TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)).toSSetObjEquiv _ σ.val) ⊆
      CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R :=
  SingleCapEmbeddingPullback.good
    (Z := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
    (X := OriginalFirstHalfCutProductCochains.space α r (Q := Q)) (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
    (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)
    (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) id (BoundedCarrierJoinCap.cover_maps α β r hr F B κ)
    (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R) d φ
    (BoundedCarrierJoinCap.proper_mono α r hr F B (Q := Q))
    (fun q σ hn => CompactFarCarrierCap.parent_near (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ R hκR d φ hfar q σ hn)
    q σ hn

def component (q : ℕ) := CapOutputSupport.component
  (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
  (Y := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
  (𝟙 (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)))
  (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R) d
  (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) d φ)
  (fun q σ hn _z hz => parent_good α β r hr F B κ R hκR d φ hfar q σ hn hz) q

theorem source (q : ℕ) : component α β r hr F B κ R hκR d φ hfar q ≫
    (push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R))).f q =
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (BoundedCarrierJoinCap.rectangles α β r hr F B κ)).f (d + q) ≫
    absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) d q (d + q) rfl
      (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) d φ) := by
  have he := CapOutputSupport.component_inclusion
    (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
    (Y := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
    (𝟙 (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)))
    (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R) d
    (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) d φ)
    (fun q σ hn _z hz => parent_good α β r hr F B κ R hκR d φ hfar q σ hn hz) q
  rw [FarDiagonalCutComparison.push_identity, HomologicalComplex.id_f] at he
  exact he.trans (congrArg (fun z => (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
    (BoundedCarrierJoinCap.rectangles α β r hr F B κ)).f (d + q) ≫ z)
      (Category.comp_id (absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) d q (d + q) rfl
        (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) d φ))))

def operation (hc : cochainCoboundary (ZMod 2) (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) d φ = 0) :=
  CapOutputSupport.operation
    (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
    (Y := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
    (𝟙 (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)))
    (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R) d
    (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) d φ)
    (fun q σ hn _z hz => parent_good α β r hr F B κ R hκR d φ hfar q σ hn hz)
    (pullback_closed _ d φ hc)

end
end Finsler.BoundedFarCarrierCap
