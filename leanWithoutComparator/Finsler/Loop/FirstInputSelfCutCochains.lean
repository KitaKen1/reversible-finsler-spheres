module

public import Finsler.Loop.OriginalFirstHalfCutNormalizedFactors
public import Finsler.Loop.FirstInputRotationZeroTimeFactors
import all Finsler.Loop.FirstInputRotationNormalizedGamma

/-! The actual single-input cut-time cochain, including the literal
tested zero extension. Its proper restriction is the genuine canonical
cut cochain. Normalization and its primitive retain the actual supports. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutCochains

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)

abbrev ambient (_α : C(P, SphereLoop (m + 1))) : TopCat.{0} := TopCat.of (ClosedInterval × P)

def source : OriginalFirstHalfCutNormalizedFactors.cutSpace α r ⟶ ambient α :=
  SupportedCap.subspaceMap (ambient α) (CompactRotatedCutData.source α r)

def far (ρ : ℝ) : Set (ambient α) := {z | ρ < distance (m + 1) (z.1, α z.2)}

def inner (δ : ℝ) : Set (ambient α) := {z | distance (m + 1) (z.1, α z.2) ≤ δ}

theorem evaluation_square : source α r ≫ AnnularSelfCut.familyMap α =
    FirstInputRotationOriginalFactors.originalEvaluation α r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

def raw := FirstInputRotationZeroTimeFactors.originalGamma α r hr h p T

def normalized := SingularNormalization.normalize (ambient α) ((m + 1) + p) (raw α r hr h p T)

def primitive := (SingularNormalization.projectorHomotopy (ambient α)).hom (m + p) ((m + 1) + p) ≫
  raw α r hr h p T

theorem source_raw : cochainPullback (source α r) ((m + 1) + p) (raw α r hr h p T) =
    OriginalFirstHalfCutNormalizedFactors.cutGamma α r hr h p T := by
  rw [raw, FirstInputRotationZeroTimeFactors.originalGamma, cochainCup_naturality,
    FirstInputRotationZeroTimeFactors.originalThom, AnnularSelfCut.familyCocycle,
    ← pullback_comp, evaluation_square, FirstInputRotationZeroTimeFactors.originalTested]
  rw [show source α r = SupportedCap.subspaceMap (ambient α) (CompactRotatedCutData.source α r) from rfl,
    TubeCochainExtension.restriction]
  rfl

theorem source_normalized : cochainPullback (source α r) ((m + 1) + p) (normalized α r hr h p T) =
    OriginalFirstHalfCutNormalizedFactors.normalized α r hr h p T := by
  rw [normalized, SingularNormalization.normalize_natural, source_raw]
  rfl

theorem source_primitive : cochainPullback (source α r) (m + p) (primitive α r hr h p T) =
    OriginalFirstHalfCutNormalizedFactors.primitive α r hr h p T := by
  rw [primitive, FirstInputRotationNormalizedGamma.primitive_pullback, source_raw]
  rfl

theorem raw_far_zero : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + 1) + p)
    (raw α r hr h p T) = 0 := by
  rw [raw, FirstInputRotationZeroTimeFactors.originalGamma, cochainCup_naturality]
  have ht : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) (m + 1)
      (FirstInputRotationZeroTimeFactors.originalThom α h) = 0 := by
    rw [FirstInputRotationZeroTimeFactors.originalThom, AnnularSelfCut.familyCocycle]
    apply pullback_support (AnnularSelfCut.familyMap α)
      (far α ρ) (exterior (m + 1) ρ) (fun _ hz => hz) (m + 1)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
  rw [ht, cochainCup_zero_left]

theorem raw_inner_zero : cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) ((m + 1) + p)
    (raw α r hr h p T) = 0 := by
  rw [raw, FirstInputRotationZeroTimeFactors.originalGamma, cochainCup_naturality]
  have ht : cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) (m + 1)
      (FirstInputRotationZeroTimeFactors.originalThom α h) = 0 := by
    rw [FirstInputRotationZeroTimeFactors.originalThom, AnnularSelfCut.familyCocycle]
    apply pullback_support (AnnularSelfCut.familyMap α) (inner α δ)
      {z | distance (m + 1) z ≤ δ} (fun _ hz => hz) (m + 1)
      (AnnularSelfCut.cocycle (m + 1) (by omega) h) (AnnularSelfCut.cocycle_small_zero (m + 1) (by omega) h)
  rw [ht, cochainCup_zero_left]

theorem normalized_far_zero : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) ((m + 1) + p)
    (normalized α r hr h p T) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (raw_far_zero α r hr h p T)

theorem normalized_inner_zero : cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) ((m + 1) + p)
    (normalized α r hr h p T) = 0 :=
  SingularNormalization.normalize_supported _ _ _ (raw_inner_zero α r hr h p T)

theorem primitive_far_zero : cochainPullback (SupportedCap.subspaceMap (ambient α) (far α ρ)) (m + p)
    (primitive α r hr h p T) = 0 := by
  rw [primitive, FirstInputRotationNormalizedGamma.primitive_pullback, raw_far_zero, comp_zero]

theorem primitive_inner_zero : cochainPullback (SupportedCap.subspaceMap (ambient α) (inner α δ)) (m + p)
    (primitive α r hr h p T) = 0 := by
  rw [primitive, FirstInputRotationNormalizedGamma.primitive_pullback, raw_inner_zero, comp_zero]

end
end Finsler.FirstInputSelfCutCochains
