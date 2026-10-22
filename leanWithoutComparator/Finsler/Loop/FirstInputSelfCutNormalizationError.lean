module

public import Finsler.Loop.CochainInputRegrade
public import Finsler.Loop.FirstInputSelfCutLocalCochainZero
public import Finsler.Loop.FirstInputSelfCutOperations
import all Finsler.Loop.OriginalFirstHalfCutNormalizedFactors
import all Finsler.Loop.OriginalFirstHalfCutGammaJoinCap

/-! The literal single-input normalization error vanishes on proper
and far regions. Its small cap is zero without ambient raw closure. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutNormalizationError

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

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

def difference := CochainInputRegrade.regrade (ambient α) ((m + p) + 1) ((m + 1) + p) (by omega)
  (normalized α r hr h p T - raw α r hr h p T)

def error : singularCochainGroup (ZMod 2) (ambient α) ((m + p) + 1) :=
  cochainCoboundary (ZMod 2) (ambient α) (m + p) (primitive α r hr h p T) - difference α r hr h p T

theorem boundary_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α) (m + p) (primitive α r hr h p T)) = 0 := by
  rw [coboundary_pullback, primitive_far_zero]
  exact map_zero _

theorem boundary_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) ((m + p) + 1)
      (cochainCoboundary (ZMod 2) (ambient α) (m + p) (primitive α r hr h p T)) = 0 := by
  rw [coboundary_pullback, primitive_inner_zero]
  exact map_zero _

theorem difference_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + p) + 1)
      (difference α r hr h p T) = 0 := by
  rw [difference, CochainInputRegrade.pullback, pullback_sub, normalized_far_zero, raw_far_zero, sub_self]
  simp only [CochainInputRegrade.regrade, comp_zero]

theorem difference_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) ((m + p) + 1)
      (difference α r hr h p T) = 0 := by
  rw [difference, CochainInputRegrade.pullback, pullback_sub, normalized_inner_zero, raw_inner_zero, sub_self]
  simp only [CochainInputRegrade.regrade, comp_zero]

theorem error_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + p) + 1)
      (error α r hr h p T) = 0 := by
  rw [error, pullback_sub, boundary_far_zero, difference_far_zero, sub_self]

theorem error_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) ((m + p) + 1)
      (error α r hr h p T) = 0 := by
  rw [error, pullback_sub, boundary_inner_zero, difference_inner_zero, sub_self]

variable (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

include hT in
theorem error_source_zero : cochainPullback (source α r) ((m + p) + 1) (error α r hr h p T) = 0 := by
  rw [error, pullback_sub, coboundary_pullback, source_primitive,
    difference, CochainInputRegrade.pullback, pullback_sub, source_normalized, source_raw,
    OriginalFirstHalfCutNormalizedFactors.primitive_boundary α r hr h p T hT]
  simp only [CochainInputRegrade.regrade, sub_self]

include hT in
theorem error_small_cap_zero (κ : ℝ) (q : ℕ) :
    (inclusion (ambient α) (cover α r hr κ ρ)).f (((m + p) + 1) + q) ≫
      absoluteChain (ambient α) ((m + p) + 1) q (((m + p) + 1) + q) rfl (error α r hr h p T) = 0 :=
  FirstInputSelfCutLocalCochainZero.small_cap_zero α r hr κ ρ _ _
    (error_far_zero α r hr h p T) (error_source_zero α r hr h p T hT) q

end
end Finsler.FirstInputSelfCutNormalizationError
