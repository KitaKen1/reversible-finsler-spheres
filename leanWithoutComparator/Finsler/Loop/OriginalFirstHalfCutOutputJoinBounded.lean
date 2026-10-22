module

public import Finsler.Loop.OriginalFirstHalfCutThenJoinCap
public import Finsler.Loop.OriginalFirstHalfBoundedStage

/-! Real canonical cut-output join on the identical bounded proper
parameter domain. Its source square and length bound identify the
actual retained map, before any chain or homology comparison. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutOutputJoinBounded

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.H1SelfCutNeighborhood Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.OriginalFirstHalfCutOutputJoinData

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric (m + 1)) (B : ℝ)

def toNear : TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B) ⟶
    TopCat.of (CompactNearJoinParameters.tube (kept α r hr) β R) :=
  SupportedCap.subspaceMap (TopCat.of (FirstInputRotatingCut.source α β R r))
    (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B) ≫
      (OriginalFirstHalfCutOutputJoinGeometry.nearIso α β R r hr).hom

theorem source_square : toNear α β R r hR hr F B ≫ OriginalFirstHalfCutThenJoinCap.source α β R r hr =
    OriginalFirstHalfJointSupportedCap.source α β R r hR hr F B := by
  rw [toNear, Category.assoc, OriginalFirstHalfCutThenJoinCap.source_square,
    ← OriginalFirstHalfBoundedStage.source_original]

theorem output_square : toNear α β R r hR hr F B ≫ TopCat.ofHom
    (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR) =
    OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B ≫
      SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
    (OriginalFirstHalfCutOutputJoinGeometry.nearHomeo α β R r hr z.val) =
    FirstInputRotatingFixedOutput.output α β R r hR hr z.val
  exact OriginalFirstHalfCutOutputJoinGeometry.joined_eq_fixed α β R r hr hR z.val

theorem length_bound (z : OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B) :
    SobolevLength.length F (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
      (toNear α β R r hR hr F B z)) < B := by
  have he := ConcreteCategory.congr_hom (output_square α β R r hR hr F B) z
  change OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR (toNear α β R r hR hr F B z) =
    (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B z).val at he
  rw [he]
  exact (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B z).property

def retained : TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F B) ⟶
    TopCat.of (JoinedFilteredCap.sublevel F B) :=
  TopCat.ofHom ⟨fun z => ⟨OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
    (toNear α β R r hR hr F B z), length_bound α β R r hR hr F B z⟩,
    (((OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR).continuous.comp
      (toNear α β R r hR hr F B).hom.continuous)).subtype_mk _⟩

theorem retained_eq : retained α β R r hR hr F B = OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F B := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (output_square α β R r hR hr F B) z

theorem retained_source : retained α β R r hR hr F B ≫
    SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B) =
    toNear α β R r hR hr F B ≫ TopCat.ofHom (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR) := by
  rw [retained_eq, output_square]

theorem exists_filtered_bound [CompactSpace P] {ε : ℝ} (hε : 0 < ε)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < u →
      ∀ (A L : ℝ) (z : CompactNearJoinParameters.tube (kept α r hr) β R),
        SobolevLength.length F (α z.val.1.val.2) + SobolevLength.length F (β z.val.2) < A →
        L - ε ≤ SobolevLength.length F (H1SelfCutNeighborhood.left
          (FirstInputRotationOriginalFactors.originalCut α r hr z.val.1)) →
        SobolevLength.length F (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR z) < A - L + 5 * ε := by
  obtain ⟨u, hu, hu1, hb⟩ := FirstInputRotatingFixedOutput.exists_filtered_bound α β r hr F hε hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu A L z hA hleft
  let w := (OriginalFirstHalfCutOutputJoinGeometry.nearHomeo α β R r hr).symm z
  have he := hb R hR hRu A L 0 w hA
  rw [FirstInputRotatingCut.rotation_zero] at he
  have hl : L - ε ≤ SobolevLength.length F (left (FirstInputRotatingCut.original α β R r hR hr w)) := hleft
  have hj := OriginalFirstHalfCutOutputJoinGeometry.joined_eq_fixed α β R r hr hR w
  rw [Homeomorph.apply_symm_apply] at hj
  rw [hj]
  exact he hl

end
end Finsler.OriginalFirstHalfCutOutputJoinBounded
