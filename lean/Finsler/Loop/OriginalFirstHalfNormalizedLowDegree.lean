module

public import Finsler.Loop.SmallNormalizedCapShuffleLowDegree
public import Finsler.Loop.OriginalFirstHalfNormalizationExternalShuffle
public import Finsler.Loop.OriginalFirstHalfNormalizationCup

/-! The actual normalized literal original gamma and cut-first cup
vanish after an external cross with insufficient first-factor degree. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizedLowDegree

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity Finsler.SupportedCapNaturality
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
  (r : ℝ) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem gamma_zero (l j k : ℕ) (hN : ((m + 1) + p) + k = l + j) (hl : l < (m + 1) + p) :
    SingularChainCross.component (TopCat.of (ClosedInterval × P)) (TopCat.of Q) l j ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f (l + j) ≫
      absoluteChain (ambient α β) ((m + 1) + p) k (l + j) hN
        (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) = 0 := by
  have hn := RelativeCapBoundary.absolute_chain_natural
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) ((m + 1) + p) k (l + j) hN
    (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T)
  change absoluteChain (TopCat.of (ClosedInterval × P) ⊗ TopCat.of Q) ((m + 1) + p) k (l + j) hN
      (cochainPullback (OriginalFirstHalfNormalizationExternalShuffle.reorder α β) ((m + 1) + p)
        (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T)) ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f k =
    (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f (l + j) ≫
      absoluteChain (ambient α β) ((m + 1) + p) k (l + j) hN
        (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) at hn
  rw [← hn, OriginalFirstHalfNormalizationExternalShuffle.cochain_factorization,
    ← Category.assoc, NormalizedCapShuffleLowDegree.component_cap_zero
      (TopCat.of (ClosedInterval × P)) (TopCat.of Q) ((m + 1) + p) l j k hN hl _
      (SingularNormalization.normalize_degeneracies _ _ _), zero_comp]

theorem cup_zero {κ : ℝ} (hκ : 0 < κ) (l j q : ℕ)
    (hN : (((m + 1) + (m + p)) + 1) + q = l + j) (hl : l < (m + 1) + p) :
    SingularChainCross.component (TopCat.of (ClosedInterval × P)) (TopCat.of Q) l j ≫
      (push (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)).f (l + j) ≫
      absoluteChain (ambient α β) (((m + 1) + (m + p)) + 1) q (l + j) hN
        (OriginalFirstHalfNormalizationCup.normalizedOrder α β r hr h p T hκ) = 0 := by
  rw [OriginalFirstHalfNormalizationCup.normalizedOrder,
    ← LocalizedCapCupComponentSource.cap_cup_input (ambient α β) ((m + 1) + p) (m + 1)
      (((m + 1) + (m + p)) + 1) q (l + j) (by omega) hN.symm]
  have hz := gamma_zero α β r hr h p T l j ((m + 1) + q) (by omega) hl
  simpa only [Category.assoc, zero_comp] using congrArg
    (fun f => f ≫ absoluteChain (ambient α β) (m + 1) q ((m + 1) + q) rfl (join α β hκ)) hz

end
end Finsler.OriginalFirstHalfNormalizedLowDegree
