module

public import Finsler.Loop.SmallNormalizedCapShuffle
public import Finsler.Loop.OriginalFirstHalfNormalizedCutShuffle
public import Finsler.Loop.OriginalFirstHalfCutThenJoinCap

/-! Strict first-factor cap/external-product factorization on the
actual output-join factor covers, followed by the genuine localized
join cap. This is before applying the self-cut time operation. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizedCutJoinFactor

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCutOutputJoinData

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)

def cutCover : CompactRotatedCutData.source α r → Set (CompactRotatedCutData.source α r) :=
  PairDistanceCover.cover (fun z => Finsler.CompactH1Alignment.basepoint (kept α r hr z)) (κ / 4)

def otherCover : Q → Set Q :=
  PairDistanceCover.cover (fun z => Finsler.CompactH1Alignment.basepoint (β z)) (κ / 4)

variable {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem first_cap (i j : ℕ) :
    SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q) (cutCover α r hr κ) (otherCover β κ) (((m + 1) + p) + i) j ≫
      SmallCapCarrier.smallCap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (kept α r hr) β κ) ((m + 1) + p) (i + j)
        ((((m + 1) + p) + i) + j) (by omega)
        (SingularNormalization.normalize (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
          ((m + 1) + p) (OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q))) =
    (SmallCapCarrier.smallCap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (cutCover α r hr κ)
      ((m + 1) + p) i (((m + 1) + p) + i) rfl
      (OriginalFirstHalfCutNormalizedFactors.normalized α r hr h p T) ▷
        (small (TopCat.of Q) (otherCover β κ)).X j) ≫
      SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q) (cutCover α r hr κ) (otherCover β κ) i j := by
  rw [OriginalFirstHalfCutNormalizedFactors.normalized_projection]
  exact SmallNormalizedCapShuffle.component_cap (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q) (cutCover α r hr κ) (otherCover β κ)
    ((m + 1) + p) i j _ (OriginalFirstHalfCutNormalizedFactors.normalized_degeneracies α r hr h p T)

theorem joined_component {R : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R)
    (i j q : ℕ) (hij : i + j = (m + 1) + q) :
    SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q) (cutCover α r hr κ) (otherCover β κ) (((m + 1) + p) + i) j ≫
      SmallCapCarrier.smallCap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (kept α r hr) β κ) ((m + 1) + p) (i + j)
        ((((m + 1) + p) + i) + j) (by omega)
        (SingularNormalization.normalize (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
          ((m + 1) + p) (OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q))) ≫
      eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (kept α r hr) β κ)).X hij) ≫
      (CompactJoinCapLocalization.localized (kept α r hr) β (by omega) hκ hκR).component q =
    (SmallCapCarrier.smallCap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (cutCover α r hr κ)
      ((m + 1) + p) i (((m + 1) + p) + i) rfl
      (OriginalFirstHalfCutNormalizedFactors.normalized α r hr h p T) ▷
        (small (TopCat.of Q) (otherCover β κ)).X j) ≫
      SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q) (cutCover α r hr κ) (otherCover β κ) i j ≫
      eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactJoinCapLocalization.cover (kept α r hr) β κ)).X hij) ≫
      (CompactJoinCapLocalization.localized (kept α r hr) β (by omega) hκ hκR).component q := by
  simpa only [Category.assoc] using congrArg (fun f => f ≫
    eqToHom (congrArg (small (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (kept α r hr) β κ)).X hij) ≫
    (CompactJoinCapLocalization.localized (kept α r hr) β (by omega) hκ hκR).component q)
    (first_cap α β r hr κ h p T i j)

end
end Finsler.OriginalFirstHalfNormalizedCutJoinFactor
