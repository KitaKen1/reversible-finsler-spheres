module

public import Finsler.Loop.FirstInputSelfCutOperations
public import Finsler.Loop.SingularCrossComponentNaturality
public import Finsler.Loop.OriginalFirstHalfNormalizationExternalShuffle

/-! The actual normalized single-input proper-cut cap followed by
external beta. Its strict source is the original-cylinder gamma cap
after the genuine external cross, in every bidegree. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutExternalCap

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)

theorem source_square : (source α r ⊗ₘ 𝟙 (TopCat.of Q)) ≫
    OriginalFirstHalfNormalizationExternalShuffle.reorder α β =
    OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem cross_source (i j : ℕ) :
    ((push (source α r)).f i ⊗ₘ 𝟙 ((chains (TopCat.of Q)).X j)) ≫
      SingularChainCross.component (ambient α) (TopCat.of Q) i j ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f (i + j) =
    SingularChainCross.component (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (TopCat.of Q) i j ≫
      (push (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q))).f (i + j) := by
  rw [← Category.assoc, SingularCrossComponentNaturality.right_identity,
    Category.assoc, ← HomologicalComplex.comp_f, ← push_comp, source_square]

variable {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def component (i j : ℕ) :
    (small (ambient α) (cover α r hr κ ρ)).X (((m + 1) + p) + i) ⊗
      (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).X j ⟶
    (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).X (i + j) :=
  ((FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT).component i ▷
    (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).X j) ≫
    SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
      (carrier α r hr κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j

theorem tensor_source (i j : ℕ) :
    ((FirstInputSelfCutOperations.normalizedOperation α r hr κ h p T hT).component i ▷
      (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).X j) ≫
      ((inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (carrier α r hr κ)).f i ⊗ₘ
        (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f j) ≫
      ((push (source α r)).f i ⊗ₘ 𝟙 ((chains (TopCat.of Q)).X j)) =
    ((inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + i) ⊗ₘ
      (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f j) ≫
      (absoluteChain (ambient α) ((m + 1) + p) i (((m + 1) + p) + i) rfl
        (normalized α r hr h p T) ▷ (chains (TopCat.of Q)).X j) := by
  rw [← tensorHom_id, ← tensorHom_id, ← Category.assoc,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]
  rw [FirstInputSelfCutOperations.normalized_source]

theorem component_source (i j : ℕ) :
    component α β r hr κ h p T hT i j ≫
      (inclusion (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).f (i + j) ≫
      (push (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q))).f (i + j) =
    ((inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + i) ⊗ₘ
      (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f j) ≫
    SingularChainCross.component (ambient α) (TopCat.of Q) (((m + 1) + p) + i) j ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f ((((m + 1) + p) + i) + j) ≫
    absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β) ((m + 1) + p) (i + j)
      ((((m + 1) + p) + i) + j) (by omega) (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) := by
  have hinc := SmallNormalizedCapShuffle.component_inclusion
    (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
    (carrier α r hr κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j
  change SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
    (carrier α r hr κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j ≫
    (inclusion (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).f (i + j) = _ at hinc
  dsimp only [component]
  rw [Category.assoc, ← Category.assoc
    (SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
      (carrier α r hr κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j), hinc]
  rw [Category.assoc, ← cross_source α β r i j]
  have ht := congrArg (fun k => k ≫ SingularChainCross.component (ambient α) (TopCat.of Q) i j ≫
    (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f (i + j))
    (tensor_source α β r hr κ h p T hT i j)
  simpa only [Category.assoc, OriginalFirstHalfNormalizationExternalShuffle.component_cap,
    FirstInputSelfCutCochains.normalized, FirstInputSelfCutCochains.raw] using ht

end
end Finsler.FirstInputSelfCutExternalCap
