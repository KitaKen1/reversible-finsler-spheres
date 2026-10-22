module

public import Finsler.Loop.CompactFarCarrierCap
public import Finsler.Loop.LiftedRepresentativeComparison
public import Finsler.Loop.CompactNormalizedJoinCapComparison

/-! The actual original fixed-scale normalized compact join cap,
specified diagonal cap and genuine primitive all live in the same
closed compact near carrier. No product-radius premise is used. -/

@[expose] public section
namespace Finsler.CompactJoinRepresentative

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (κ R : ℝ)
  (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hm : 1 ≤ m) (hκ2 : κ ≤ 2)

def farSet := NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q)
  (fun x => basepoint (α x)) (fun y => basepoint (β y)) κ

theorem far_maps : Set.MapsTo (DiagonalPullbackCut.pairEvaluation
    (StrictLengthProductFamilies.leftEvaluation α (Q := Q)) (StrictLengthProductFamilies.rightEvaluation β (P := P)))
    (farSet α β κ) (DiagonalAvoidanceCocycle.far (m + 1) κ) := by
  intro z hz
  change κ ≤ ‖basepoint (β z.2) - basepoint (α z.1)‖
  have he : κ ≤ dist (basepoint (α z.1)) (basepoint (β z.2)) := hz
  simpa only [dist_eq_norm, norm_sub_rev] using he

def specified := DiagonalPullbackCut.cocycle (dim_pos m)
  (StrictLengthProductFamilies.leftEvaluation α (Q := Q)) (StrictLengthProductFamilies.rightEvaluation β (P := P))

theorem specified_closed : cochainCoboundary (ZMod 2) (TopCat.of (P × Q)) (m + 1) (specified α β) = 0 :=
  DiagonalPullbackCut.cocycle_closed (dim_pos m) _ _

include hκ in
theorem specified_far : cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q)) (farSet α β κ)) (m + 1)
    (specified α β) = 0 := FarNormalizedDiagonalCap.specified_supported m _ _ hκ (farSet α β κ) (far_maps α β κ)

def primitive := FarNormalizedDiagonalCap.primitive m (StrictLengthProductFamilies.leftEvaluation α (Q := Q))
  (StrictLengthProductFamilies.rightEvaluation β (P := P)) hκ hm hκ2

theorem primitive_far : cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × Q)) (farSet α β κ)) m
    (primitive α β κ hκ hm hκ2) = 0 :=
  FarNormalizedDiagonalCap.primitive_supported m _ _ hκ hm hκ2 (farSet α β κ) (far_maps α β κ)

theorem primitive_boundary : cochainCoboundary (ZMod 2) (TopCat.of (P × Q)) m (primitive α β κ hκ hm hκ2) =
    CompactJoinCocycle.cocycle α β (dim_pos m) hκ - specified α β := by
  have he := FarNormalizedDiagonalCap.primitive_boundary m (StrictLengthProductFamilies.leftEvaluation α (Q := Q))
    (StrictLengthProductFamilies.rightEvaluation β (P := P)) hκ hm hκ2
  rw [CompactNormalizedJoinCapComparison.cocycle_eq] at he
  exact he

def specifiedOperation := CompactFarCarrierCap.operation α β κ R hκR (m + 1) (specified α β)
  (specified_far α β κ hκ) (specified_closed α β)

def primitiveCap (q : ℕ) := CompactFarCarrierCap.component α β κ R hκR m (primitive α β κ hκ hm hκ2)
  (primitive_far α β κ hκ hm hκ2) q

include hm hκ2 in
theorem homology_eq (q : ℕ) : (CompactJoinCapLocalization.localized α β (dim_pos m) hκ hκR).homology q =
    (specifiedOperation α β κ R hκ hκR).homology q := by
  exact LiftedRepresentativeComparison.homology_eq (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ)
    (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (push (SupportedCap.subspaceMap (TopCat.of (P × Q)) (CompactNearJoinParameters.tube α β R)))
    (fun q => SupportedCap.subspacePush_mono _ _ q) m _ _ _ (primitive_boundary α β κ hκ hm hκ2)
    (CompactJoinCapLocalization.localized α β (dim_pos m) hκ hκR) (specifiedOperation α β κ R hκ hκR)
    (CompactJoinCapLocalization.source α β (dim_pos m) hκ hκR)
    (CompactFarCarrierCap.source α β κ R hκR (m + 1) (specified α β) (specified_far α β κ hκ))
    (primitiveCap α β κ R hκ hκR hm hκ2)
    (CompactFarCarrierCap.source α β κ R hκR m (primitive α β κ hκ hm hκ2) (primitive_far α β κ hκ hm hκ2)) q

end
end Finsler.CompactJoinRepresentative
