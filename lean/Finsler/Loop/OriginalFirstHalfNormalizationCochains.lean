module

public import Finsler.Loop.NormalizedCupBoundary
public import Finsler.Loop.OriginalFirstHalfCupOrderCochains
import all Finsler.Loop.FirstInputRotationNormalizedGamma

/-! Actual normalization and its primitive on the entire original
cut-time cylinder. Naturality gives exact first-input and proper-cut
factorizations, without asserting global closure of the zero extension. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizationCochains

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def normalized : singularCochainGroup (ZMod 2) (ambient α β) ((m + 1) + p) :=
  SingularNormalization.normalize (ambient α β) ((m + 1) + p) (gamma α β r hr h p T)

def primitive : singularCochainGroup (ZMod 2) (ambient α β) (m + p) :=
  (SingularNormalization.projectorHomotopy (ambient α β)).hom (m + p) ((m + 1) + p) ≫
    gamma α β r hr h p T

theorem normalized_first_input : normalized α β r hr h p T =
    cochainPullback (firstInput α β) ((m + 1) + p)
      (SingularNormalization.normalize (TopCat.of (ClosedInterval × P)) ((m + 1) + p)
        (FirstInputRotationZeroTimeFactors.originalGamma α r hr h p T)) := by
  rw [normalized, gamma, ← SingularNormalization.normalize_natural]

theorem primitive_first_input : primitive α β r hr h p T =
    cochainPullback (firstInput α β) (m + p)
      ((SingularNormalization.projectorHomotopy (TopCat.of (ClosedInterval × P))).hom (m + p) ((m + 1) + p) ≫
        FirstInputRotationZeroTimeFactors.originalGamma α r hr h p T) := by
  rw [primitive, gamma]
  exact (FirstInputRotationNormalizedGamma.primitive_pullback _ _ _ _).symm

theorem normalized_cut_source :
    cochainPullback (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q)) ((m + 1) + p)
      (normalized α β r hr h p T) =
    SingularNormalization.normalize (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) ((m + 1) + p)
      (OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q)) := by
  rw [normalized, SingularNormalization.normalize_natural, OriginalFirstHalfCutProductCochains.source_gamma]

theorem primitive_cut_source :
    cochainPullback (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q)) (m + p)
      (primitive α β r hr h p T) =
    (SingularNormalization.projectorHomotopy (OriginalFirstHalfCutProductCochains.space α r (Q := Q))).hom
      (m + p) ((m + 1) + p) ≫ OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q) := by
  rw [primitive, FirstInputRotationNormalizedGamma.primitive_pullback, OriginalFirstHalfCutProductCochains.source_gamma]

theorem normalized_cut_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) ((m + 1) + p)
      (normalized α β r hr h p T) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (gamma_cut_far_zero α β r hr h p T)

theorem primitive_cut_far_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (cutFar α β ρ)) (m + p)
      (primitive α β r hr h p T) = 0 := by
  rw [primitive, FirstInputRotationNormalizedGamma.primitive_pullback, gamma_cut_far_zero, comp_zero]

theorem normalized_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) ((m + 1) + p)
      (normalized α β r hr h p T) = 0 :=
  SingularNormalization.normalize_supported _ _ _
    (OriginalFirstHalfCupOrderCochains.gamma_inner_zero α β r hr h p T)

theorem primitive_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (ambient α β) (inner α β δ)) (m + p)
      (primitive α β r hr h p T) = 0 := by
  rw [primitive, FirstInputRotationNormalizedGamma.primitive_pullback,
    OriginalFirstHalfCupOrderCochains.gamma_inner_zero, comp_zero]

variable (R : ℝ) (hR : R ≤ 1 / 2)

theorem normalized_source :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) ((m + 1) + p)
      (normalized α β r hr h p T) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) ((m + 1) + p)
      (FirstInputRotationNormalizedGamma.normalized α β R r hR hr h p T) := by
  rw [normalized, SingularNormalization.normalize_natural,
    OriginalFirstHalfJointCochains.source_gamma α β R r hR hr h p T,
    ← SingularNormalization.normalize_natural]
  rfl

theorem primitive_source :
    cochainPullback (OriginalFirstHalfJointCover.source α β R r) (m + p)
      (primitive α β r hr h p T) =
    cochainPullback (FirstInputRotationEndpoints.stage α β R r 0) (m + p)
      (FirstInputRotationNormalizedGamma.primitive α β R r hR hr h p T) := by
  rw [primitive, FirstInputRotationNormalizedGamma.primitive_pullback,
    OriginalFirstHalfJointCochains.source_gamma α β R r hR hr h p T]
  exact (FirstInputRotationNormalizedGamma.primitive_pullback _ _ _ _).symm

end
end Finsler.OriginalFirstHalfNormalizationCochains
