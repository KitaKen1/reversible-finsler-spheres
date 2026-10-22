module

public import Finsler.Loop.SingleCutCanonicalThomCochains
public import Finsler.Loop.CochainCupTotalRegrade
public import Finsler.Loop.NormalizedCupBoundary
public import Finsler.Loop.FirstInputSelfCutLocalCochainZero

/-! The actual annular/canonical Thom comparison after cup with the
literal tested extension. Its only Leibniz error vanishes on the proper
and far pieces, hence its actual small cap vanishes. -/

@[expose] public section
namespace Finsler.SingleCutThomRepresentativeError

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover
open Finsler.SingleCutCanonicalThomCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f d (φ - ψ) = cochainPullback f d φ - cochainPullback f d ψ :=
  map_sub (((singularCochainComplexZMod2.map f.op).f d).hom) φ ψ

private theorem coboundary_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (d : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y d) :
    cochainPullback f (d + 1) (cochainCoboundary (ZMod 2) Y d φ) =
      cochainCoboundary (ZMod 2) X d (cochainPullback f d φ) :=
  (ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm d (d + 1)) φ).symm

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hm : 1 ≤ m) (hρ2 : ρ ≤ 2)

theorem proper_thom_boundary :
    cochainCoboundary (ZMod 2) (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) m
      (cochainPullback (FirstInputRotationOriginalFactors.originalEvaluation α r) m
        (AnnularSelfCut.primitive (m + 1) (by omega) h hρ2)) =
    cochainPullback (FirstInputRotationOriginalFactors.originalEvaluation α r) (m + 1)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h) -
    cochainPullback (FirstInputRotationOriginalFactors.originalEvaluation α r) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) (h.1.trans h.2.2)) := by
  rw [← coboundary_pullback]
  have hb := AnnularSelfCut.primitive_boundary (m + 1) (show 2 ≤ m + 1 by omega) h hρ2
  change cochainCoboundary (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) m
    (AnnularSelfCut.primitive (m + 1) (by omega) h hρ2) = _ at hb
  rw [hb, pullback_sub]

def difference := CochainInputRegrade.regrade (ambient α) ((m + p) + 1) ((m + 1) + p) (by omega)
  (raw α r hr h p T - canonicalGamma α r hr h p T)

def error : singularCochainGroup (ZMod 2) (ambient α) ((m + p) + 1) :=
  cochainCoboundary (ZMod 2) (ambient α) (m + p)
    (comparisonPrimitive α r hr h p T hm hρ2) - difference α r hr h p T

theorem error_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + p) + 1)
      (error α r hr h p T hm hρ2) = 0 := by
  rw [error, pullback_sub, coboundary_pullback, SingleCutCanonicalThomCochains.primitive_far_zero,
    difference, CochainInputRegrade.pullback, pullback_sub, raw_far_zero, gamma_far_zero, sub_self]
  simp only [CochainInputRegrade.regrade, comp_zero, cochainCoboundary, map_zero, sub_self]

variable (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hT in
theorem proper_primitive_boundary :
    cochainCoboundary (ZMod 2) (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (m + p)
      (properPrimitive α r hr h p T hm hρ2) =
    CochainInputRegrade.regrade (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      ((m + p) + 1) ((m + 1) + p) (by omega)
      (OriginalFirstHalfCutNormalizedFactors.cutGamma α r hr h p T - properGamma α r hr h p T) := by
  rw [properPrimitive, NormalizedCupBoundary.boundary_right_closed _ m p (m + p) rfl _ _
    (pullback_closed _ _ _ hT), proper_thom_boundary α r h hm hρ2, NormalizedCupBoundary.cup_sub_left]
  have hc : OriginalFirstHalfCutNormalizedFactors.cutGamma α r hr h p T =
      CupOne.cup (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (m + 1) p ((m + 1) + p) rfl
        (cochainPullback (FirstInputRotationOriginalFactors.originalEvaluation α r) (m + 1)
          (AnnularSelfCut.cocycle (m + 1) (by omega) h))
        (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T) := by
    rw [CupOne.cup_comparison]
    rfl
  rw [hc, properGamma]
  simp only [CochainInputRegrade.regrade, Preadditive.comp_sub]
  change _ = CochainInputRegrade.regrade _ ((m + p) + 1) ((m + 1) + p) (by omega) _ -
    CochainInputRegrade.regrade _ ((m + p) + 1) ((m + 1) + p) (by omega) _
  rw [CochainCupTotalRegrade.cup, CochainCupTotalRegrade.cup]

include hT in
theorem error_source_zero : cochainPullback (source α r) ((m + p) + 1)
    (error α r hr h p T hm hρ2) = 0 := by
  rw [error, pullback_sub, coboundary_pullback, SingleCutCanonicalThomCochains.source_primitive,
    proper_primitive_boundary α r hr h p T hm hρ2 hT,
    difference, CochainInputRegrade.pullback, pullback_sub, source_raw, source_gamma]
  exact sub_self _

include hT in
theorem error_small_cap_zero (κ : ℝ) (q : ℕ) :
    (inclusion (ambient α) (cover α r hr κ ρ)).f (((m + p) + 1) + q) ≫
      absoluteChain (ambient α) ((m + p) + 1) q (((m + p) + 1) + q) rfl
        (error α r hr h p T hm hρ2) = 0 :=
  FirstInputSelfCutLocalCochainZero.small_cap_zero α r hr κ ρ _ _
    (error_far_zero α r hr h p T hm hρ2) (error_source_zero α r hr h p T hm hρ2 hT) q

end
end Finsler.SingleCutThomRepresentativeError
