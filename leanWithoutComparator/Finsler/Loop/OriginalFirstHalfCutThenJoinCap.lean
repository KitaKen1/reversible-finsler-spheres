module

public import Finsler.Loop.OriginalFirstHalfCutGammaJoinCap
public import Finsler.Loop.OriginalFirstHalfCutOutputJoinGeometry
public import Finsler.Loop.LocalizedCapCupRegradedSource

/-! The genuine gamma-first proper cut cap followed by the actual
normalized join cap of the retained right cut and beta. Its exact
source is the real original cut-first cup cochain. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutThenJoinCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCutOutputJoinData Finsler.OriginalFirstHalfCupOneCochains
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ) (hr : r < 1)

def source : TopCat.of (CompactNearJoinParameters.tube (kept α r hr) β R) ⟶ ambient α β :=
  SupportedCap.subspaceMap (TopCat.of (CompactRotatedCutData.source α r × Q))
    (CompactNearJoinParameters.tube (kept α r hr) β R) ≫ originalTime α r (Q := Q)

theorem source_square : (OriginalFirstHalfCutOutputJoinGeometry.nearIso α β R r hr).hom ≫ source α β R r hr =
    OriginalFirstHalfJointCover.source α β R r :=
  OriginalFirstHalfCutOutputJoinGeometry.original_time_square α β R r hr

theorem source_mono (q : ℕ) : Mono ((push (source α β R r hr)).f q) := by
  have he : source α β R r hr = (OriginalFirstHalfCutOutputJoinGeometry.nearIso α β R r hr).inv ≫
      OriginalFirstHalfJointCover.source α β R r := by
    rw [← source_square α β R r hr, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  haveI : Mono (SupportedCap.subspaceMap (ambient α β) (OriginalFirstHalfJointCover.proper α β R r)) :=
    (TopCat.mono_iff_injective _).mpr Subtype.val_injective
  haveI : Mono (OriginalFirstHalfJointCover.source α β R r) := by
    dsimp only [OriginalFirstHalfJointCover.source, SmallCapSubspaceLift.source]
    infer_instance
  haveI : Mono (source α β R r hr) := by rw [he]; infer_instance
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (source α β R r hr)).app (Opposite.op ⦋q⦌))))

variable {κ δ ρ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

def operation := DegreeLoweringRegrade.regrade
  (DegreeLoweringComposition.compose (OriginalFirstHalfCutGammaJoinCap.operation α β r hr κ h p T hT)
    (CompactJoinCapLocalization.localized (kept α r hr) β (by omega) hκ hκR))
  (((m + 1) + (m + p)) + 1) (by omega)

theorem component_source (q : ℕ) :
    (operation α β R r hr hκ hκR h p T hT).component q ≫ (push (source α β R r hr)).f q =
    (inclusion (ambient α β) (OriginalFirstHalfCutGammaJoinCover.cover α β r hr κ ρ)).f
      ((((m + 1) + (m + p)) + 1) + q) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q
        ((((m + 1) + (m + p)) + 1) + q) rfl
        (OriginalFirstHalfCupOrderCochains.originalOrder α β r hr h p T hκ true) := by
  have hg (q : ℕ) : (CompactJoinCapLocalization.localized (kept α r hr) β (by omega) hκ hκR).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (CompactRotatedCutData.source α r × Q))
        (CompactNearJoinParameters.tube (kept α r hr) β R))).f q =
    (inclusion (TopCat.of (CompactRotatedCutData.source α r × Q))
      (CompactJoinCapLocalization.cover (kept α r hr) β κ)).f ((m + 1) + q) ≫
      absoluteChain (TopCat.of (CompactRotatedCutData.source α r × Q)) (m + 1) q ((m + 1) + q) rfl
        (cochainPullback (originalTime α r (Q := Q)) (m + 1) (join α β hκ)) := by
    rw [OriginalFirstHalfCutProductCochains.source_join]
    exact CompactJoinCapLocalization.source (kept α r hr) β (by omega) hκ hκR q
  have hc := LocalizedCapCupRegradedSource.component_source
    (OriginalFirstHalfCutGammaJoinCover.cover α β r hr κ ρ) (CompactJoinCapLocalization.cover (kept α r hr) β κ)
    (originalTime α r (Q := Q)) (push (SupportedCap.subspaceMap (TopCat.of (CompactRotatedCutData.source α r × Q))
      (CompactNearJoinParameters.tube (kept α r hr) β R)))
    (OriginalFirstHalfCupOneCochains.gamma α β r hr h p T) (join α β hκ)
    (OriginalFirstHalfCutGammaJoinCap.operation α β r hr κ h p T hT)
    (CompactJoinCapLocalization.localized (kept α r hr) β (by omega) hκ hκR)
    (OriginalFirstHalfCutGammaJoinCap.component_source α β r hr κ h p T) hg
    (((m + 1) + (m + p)) + 1) (by omega) q
  rw [← push_comp] at hc
  exact hc

end
end Finsler.OriginalFirstHalfCutThenJoinCap
