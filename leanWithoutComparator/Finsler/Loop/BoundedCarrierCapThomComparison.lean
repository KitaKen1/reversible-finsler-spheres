module

public import Finsler.Loop.BoundedCarrierJoinCover
public import Finsler.Loop.CompactNormalizedJoinCapComparison

/-! The real bounded-carrier cap on the proper-centered pullback cover
induces the specified diagonal Thom cut in the actual open near tube.
The common-cover and far-supported primitive comparisons apply to this
cover directly; no recentering assumption is needed. -/

@[expose] public section
namespace Finsler.BoundedCarrierCapThomComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B κ R S : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hRS : R < S)

def nearOperation := (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).post
  (push (CompactNormalizedJoinCapComparison.toNear (BoundedKeptProductInputs.kept α r hr F B) β R S hRS))

theorem source (k : ℕ) : (nearOperation α β r hr F B κ R S hκ hκR hRS).component k ≫
    (push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β S))).f k =
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (BoundedCarrierJoinCap.rectangles α β r hr F B κ)).f ((m + 1) + k) ≫
    RelativeCapAssociativity.absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (m + 1) k ((m + 1) + k) rfl
      (FarNormalizedDiagonalCap.cocycle m (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B))
        (StrictLengthProductFamilies.rightEvaluation β) hκ) := by
  have hj : push (CompactNormalizedJoinCapComparison.toNear (BoundedKeptProductInputs.kept α r hr F B) β R S hRS) ≫
      push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
        (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β S)) =
    push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R)) := by
    rw [← push_comp, CompactNormalizedJoinCapComparison.toNear_source]
  change ((BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).component k ≫ _ ) ≫ _ = _
  rw [Category.assoc, ← HomologicalComplex.comp_f, hj, CompactNormalizedJoinCapComparison.cocycle_eq]
  exact BoundedCarrierJoinCap.source α β r hr F B κ R hκ hκR k

def unrefined := (nearOperation α β r hr F B κ R S hκ hκR hRS).pre
  (BoundedCarrierJoinCover.retraction α β r hr F B κ hκ)

theorem existing_unrefined (k : ℕ) :
    ((BoundedCarrierJoinCover.unrefined α β r hr F B κ R hκ hκR).post
      (push (CompactNormalizedJoinCapComparison.toNear (BoundedKeptProductInputs.kept α r hr F B) β R S hRS))).homology k =
    (unrefined α β r hr F B κ R S hκ hκR hRS).homology k := by
  rw [DegreeLoweringHomology.Map.post_homology, BoundedCarrierJoinCover.unrefined,
    DegreeLoweringHomology.Map.pre_homology, unrefined, DegreeLoweringHomology.Map.pre_homology,
    nearOperation, DegreeLoweringHomology.Map.post_homology, Category.assoc]

theorem normalized_homology (k : ℕ) : (unrefined α β r hr F B κ R S hκ hκR hRS).homology k =
    (FarNormalizedDiagonalCap.operation m (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B))
      (StrictLengthProductFamilies.rightEvaluation β) hκ
      (CompactNormalizedJoinCapComparison.far (BoundedKeptProductInputs.kept α r hr F B) β κ)
      (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β S)
      (CompactNormalizedJoinCapComparison.far_open (BoundedKeptProductInputs.kept α r hr F B) β κ)
      (CompactNormalizedJoinCapComparison.near_open (BoundedKeptProductInputs.kept α r hr F B) β S)
      (CompactNormalizedJoinCapComparison.covers (BoundedKeptProductInputs.kept α r hr F B) β hκ R S hκR hRS)
      (CompactNormalizedJoinCapComparison.far_maps (BoundedKeptProductInputs.kept α r hr F B) β)).homology k := by
  exact LocalizedSupportedCapComparison.homology_eq
    (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
    (CompactNormalizedJoinCapComparison.far (BoundedKeptProductInputs.kept α r hr F B) β κ)
    (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β S)
    (CompactNormalizedJoinCapComparison.far_open (BoundedKeptProductInputs.kept α r hr F B) β κ)
    (CompactNormalizedJoinCapComparison.near_open (BoundedKeptProductInputs.kept α r hr F B) β S)
    (CompactNormalizedJoinCapComparison.covers (BoundedKeptProductInputs.kept α r hr F B) β hκ R S hκR hRS)
    (m + 1) _ (FarNormalizedDiagonalCap.cocycle_supported m _ _ hκ _
      (CompactNormalizedJoinCapComparison.far_maps (BoundedKeptProductInputs.kept α r hr F B) β))
    (FarNormalizedDiagonalCap.cocycle_closed m _ _ hκ) (nearOperation α β r hr F B κ R S hκ hκR hRS)
    (source α β r hr F B κ R S hκ hκR hRS) (BoundedCarrierJoinCover.isOpen α β r hr F B κ)
    (BoundedCarrierJoinCover.covers α β r hr F B κ hκ) k

theorem specified_homology (hm : 1 ≤ m) (hκ2 : κ ≤ 2) (k : ℕ) :
    (unrefined α β r hr F B κ R S hκ hκR hRS).homology k =
    (DiagonalCutNaturality.operation (dim_pos m)
      (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B))
      (StrictLengthProductFamilies.rightEvaluation β)
      (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β S)
      (CompactNormalizedJoinCapComparison.near_open (BoundedKeptProductInputs.kept α r hr F B) β S)
      (FarDiagonalCutComparison.diagonal_in_near m _ _ hκ
        (CompactNormalizedJoinCapComparison.far (BoundedKeptProductInputs.kept α r hr F B) β κ)
        (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β S)
        (CompactNormalizedJoinCapComparison.covers (BoundedKeptProductInputs.kept α r hr F B) β hκ R S hκR hRS)
        (CompactNormalizedJoinCapComparison.far_maps (BoundedKeptProductInputs.kept α r hr F B) β))).homology k := by
  rw [normalized_homology]
  exact FarDiagonalCutComparison.normalized_homology m _ _ hκ
    (CompactNormalizedJoinCapComparison.far (BoundedKeptProductInputs.kept α r hr F B) β κ)
    (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β S)
    (CompactNormalizedJoinCapComparison.far_open (BoundedKeptProductInputs.kept α r hr F B) β κ)
    (CompactNormalizedJoinCapComparison.near_open (BoundedKeptProductInputs.kept α r hr F B) β S)
    (CompactNormalizedJoinCapComparison.covers (BoundedKeptProductInputs.kept α r hr F B) β hκ R S hκR hRS)
    (CompactNormalizedJoinCapComparison.far_maps (BoundedKeptProductInputs.kept α r hr F B) β) hm hκ2 k

end
end Finsler.BoundedCarrierCapThomComparison
