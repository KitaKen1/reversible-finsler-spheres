module

public import Finsler.Loop.BoundedCarrierLengthProduct
public import Finsler.Loop.OriginalFirstHalfCutOutputJoinBounded

/-! A true compact proper-cut family supplies one raw-join length radius
before every individual kept and beta threshold. Thus the actual raw
join maps all later bounded near spaces into their separate length sum,
without positivity assumptions or a later energy-product radius. -/

@[expose] public section
namespace Finsler.BoundedCarrierUniformRawJoin

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

attribute [local instance] CompactRotatedCutData.source_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) {ε : ℝ} (hε : 0 < ε)

include hε in
theorem exists_uniform : ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < u →
    ∀ (B b : ℝ) (hβ : ∀ y, SobolevLength.length F (β y) < b)
      (z : CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R),
      SobolevLength.length F (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
        (BoundedKeptProductInputs.properTube α β r hr F B R z)) < B + (b + ε) := by
  obtain ⟨u, hu, hu1, hb⟩ := CompactNearJoinParameters.exists_length_tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β F hε
  refine ⟨min u (1 / 2), lt_min hu (by norm_num), min_le_right _ _, ?_⟩
  intro R hR hRu B b hβ z
  have hRu' : R < u := hRu.trans_le (min_le_left _ _)
  let w : CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β u :=
    ⟨((FirstInputSelfCutBoundedSpace.toCut α r hr F B) z.val.1, z.val.2), z.property.trans hRu'.le⟩
  have he := hb w
  have hj : JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs (OriginalFirstHalfCutOutputJoinData.kept α r hr) β u hu1) w =
      OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR (BoundedKeptProductInputs.properTube α β r hr F B R z) := rfl
  rw [hj] at he
  have hleft := BoundedKeptProductInputs.length_lt α r hr F B z.val.1
  have hright := hβ z.val.2
  change SobolevLength.length F (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
    (BoundedKeptProductInputs.properTube α β r hr F B R z)) < _
  change SobolevLength.length F (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
    (BoundedKeptProductInputs.properTube α β r hr F B R z)) <
    SobolevLength.length F (BoundedKeptProductInputs.kept α r hr F B z.val.1) + SobolevLength.length F (β z.val.2) + ε at he
  linarith

def radius : ℝ := (exists_uniform α β r hr F hε).choose

theorem radius_pos : 0 < radius α β r hr F hε := (exists_uniform α β r hr F hε).choose_spec.1

theorem radius_le_half : radius α β r hr F hε ≤ 1 / 2 := (exists_uniform α β r hr F hε).choose_spec.2.1

variable (R : ℝ) (hR : R ≤ 1 / 2) (hRu : R < radius α β r hr F hε)
  (B b : ℝ) (hβ : ∀ y, SobolevLength.length F (β y) < b)

def joinMap : TopCat.of (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R) ⟶
    lengthSpace F (B + (b + ε)) := TopCat.ofHom
  ⟨fun z => ⟨OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR
      (BoundedKeptProductInputs.properTube α β r hr F B R z),
      (exists_uniform α β r hr F hε).choose_spec.2.2 R hR hRu B b hβ z⟩,
    (((OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR).continuous.comp
      (BoundedKeptProductInputs.properTube α β r hr F B R).hom.continuous)).subtype_mk _⟩

theorem loop_square : joinMap α β r hr F hε R hR hRu B b hβ ≫
    SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (B + (b + ε))) =
    BoundedKeptProductInputs.properTube α β r hr F B R ≫
      TopCat.ofHom (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR) := rfl

end
end Finsler.BoundedCarrierUniformRawJoin
