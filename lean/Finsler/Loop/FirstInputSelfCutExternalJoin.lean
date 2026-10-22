module

public import Finsler.Loop.FirstInputSelfCutExternalCap
public import Finsler.Loop.LocalizedCapCupComponentSource
public import Finsler.Loop.OriginalFirstHalfNormalizationCup

/-! The actual single-input normalized proper cut cap, external beta,
and the genuine localized retained-right-output join cap. Its source is
the real normalized original cut-first cup, with exact degree casts. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutExternalJoin

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
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ) (hr : r < 1)
  {κ δ ρ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R)
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem first_source (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    FirstInputSelfCutExternalCap.component α β r hr κ h p T hT i j ≫
      eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).X hij) ≫
      (inclusion (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).f ((m + 1) + q) ≫
      (push (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q))).f ((m + 1) + q) =
    ((inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + i) ⊗ₘ
      (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f j) ≫
    SingularChainCross.component (ambient α) (TopCat.of Q) (((m + 1) + p) + i) j ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f ((((m + 1) + p) + i) + j) ≫
    absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β) ((m + 1) + p) ((m + 1) + q)
      ((((m + 1) + p) + i) + j) (by omega) (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) := by
  have ht := LocalizedCapCupComponentSource.transport_f
    (inclusion (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ) ≫
      push (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q))) (i + j) ((m + 1) + q) hij
  have hh := congrArg (fun k => FirstInputSelfCutExternalCap.component α β r hr κ h p T hT i j ≫ k) ht
  simp only [HomologicalComplex.comp_f, Category.assoc] at hh
  rw [hh]
  have hs := congrArg (fun k => k ≫ eqToHom (congrArg
    (chains (OriginalFirstHalfCupOneCochains.ambient α β)).X hij))
    (FirstInputSelfCutExternalCap.component_source α β r hr κ h p T hT i j)
  simp only [Category.assoc] at hs
  rw [hs]
  rw [LocalizedCapCupComponentSource.cap_output_transport]
  exact hij

def component (i j q : ℕ) (hij : i + j = (m + 1) + q) :=
  FirstInputSelfCutExternalCap.component α β r hr κ h p T hT i j ≫
    eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).X hij) ≫
    (CompactJoinCapLocalization.localized (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (by omega) hκ hκR).component q

theorem component_source (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    component α β R r hr hκ hκR h p T hT i j q hij ≫
      (push (OriginalFirstHalfCutThenJoinCap.source α β R r hr)).f q =
    ((inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + i) ⊗ₘ
      (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f j) ≫
    SingularChainCross.component (ambient α) (TopCat.of Q) (((m + 1) + p) + i) j ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f ((((m + 1) + p) + i) + j) ≫
    absoluteChain (OriginalFirstHalfCupOneCochains.ambient α β) (((m + 1) + (m + p)) + 1) q
      ((((m + 1) + p) + i) + j) (by omega) (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) := by
  have hg : (CompactJoinCapLocalization.localized (OriginalFirstHalfCutOutputJoinData.kept α r hr) β
      (by omega) hκ hκR).component q ≫
      (push (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R))).f q =
    (inclusion (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).f ((m + 1) + q) ≫
      absoluteChain (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) (m + 1) q ((m + 1) + q) rfl
        (cochainPullback (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q)) (m + 1)
          (OriginalFirstHalfCupOneCochains.join α β hκ)) := by
    rw [OriginalFirstHalfCutProductCochains.source_join]
    exact CompactJoinCapLocalization.source (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (by omega) hκ hκR q
  have hc := LocalizedCapCupComponentSource.component_source
    (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)
    (OriginalFirstHalfCutOutputJoinData.originalTime α r (Q := Q))
    ((m + 1) + p) (m + 1) (((m + 1) + (m + p)) + 1) q ((((m + 1) + p) + i) + j) (by omega) (by omega)
    (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T)
    (OriginalFirstHalfCupOneCochains.join α β hκ)
    (FirstInputSelfCutExternalCap.component α β r hr κ h p T hT i j ≫
      eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)).X hij))
    (((inclusion (ambient α) (cover α r hr κ ρ)).f (((m + 1) + p) + i) ⊗ₘ
      (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).f j) ≫
      SingularChainCross.component (ambient α) (TopCat.of Q) (((m + 1) + p) + i) j ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f ((((m + 1) + p) + i) + j))
    ((CompactJoinCapLocalization.localized (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (by omega) hκ hκR).component q)
    ((push (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R))).f q)
    (by simpa only [Category.assoc] using first_source α β r hr (κ := κ) h p T hT i j q hij) hg
  simpa only [component, OriginalFirstHalfCutThenJoinCap.source, push_comp, HomologicalComplex.comp_f,
    OriginalFirstHalfNormalizationCup.normalizedOrder, Category.assoc] using hc

end
end Finsler.FirstInputSelfCutExternalJoin
