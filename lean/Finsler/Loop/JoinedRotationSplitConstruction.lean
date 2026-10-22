module

public import Finsler.Loop.JoinedRotationFilteredSplit
public import Finsler.Loop.JoinedRotationSplitData

/-! Package the actual supplied-collar split, preserving the full and
second-half cap, prism and ambient formulas needed by later comparisons. -/

@[expose] public section
namespace Finsler.JoinedRotationSplitConstruction

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

theorem exists_uniform_on_collar {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ) (hR : R ≤ 1 / 2)
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r < 1)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (ζ : ℝ) (hζ : 0 < ζ)
    (hrot₀ : ∀ s x, FirstInputRotationTimeTrim.sideHomotopy α β R a ha ha1 0 (s, x) ∈
      FirstInputRotationCutCylinder.collar α β R δ)
    (hrot₁ : ∀ s x, FirstInputRotationTimeTrim.sideHomotopy α β R a ha ha1 1 (s, x) ∈
      FirstInputRotationCutCylinder.collar α β R δ)
    (hlength : ∀ z : CompactNearJoinParameters.tube α β R,
      length F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z).val.1 +
      length F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z).val.2 <
        length F (α z.val.1) + length F (β z.val.2) + ε)
    (hadequate : ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : CompactNearJoinParameters.tube α β R, length F (α z.val.1) + length F (β z.val.2) < A) →
      FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) ζ p T)
    (hside₀ : ∀ (i : Fin 2) (s : ClosedInterval) (x : CompactNearJoinParameters.tube α β R),
      distance (m + 1) (JoinedFamilyNaturality.globalMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i.succ ((s, 0), x)) ≤ δ)
    (hside₁ : ∀ (i : Fin 2) (s : ClosedInterval) (x : CompactNearJoinParameters.tube α β R),
      distance (m + 1) (JoinedFamilyNaturality.globalMap
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i.succ ((s, 1), x)) ≤ δ) :
    ∃ θ : ℝ, ∃ hθ : 0 < θ, θ ≤ b ∧ ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : CompactNearJoinParameters.tube α β R, length F (α z.val.1) + length F (β z.val.2) < A) →
      ∃ hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) ζ p T,
      Nonempty (JoinedRotationSplitData.Data α β R r hR hr F a ha ha1 (A - L + 5 * ε) θ ζ hθ hζ p T
        h (by linarith [h.1.trans h.2.2]) hgood hT) := by
  obtain ⟨hf₀, hf₁, hs₀, hs₁, θ, hθ, hθb, η, hη, hηb, hW, hop⟩ :=
    JoinedRotationFilteredSplit.exists_uniform_on_collar m F α β R hR h hρr hr hε hb hradius
      a ha ha1 ζ hζ hrot₀ hrot₁ hlength hadequate hside₀ hside₁
  refine ⟨θ, hθ, hθb, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨hg, d, c, f, k, w, hd, hdc, hi, hc, hf, hk, hw, hsplit, hfull, hfirst, hsecond⟩ :=
    hop p L A T hT hshort hA
  exact ⟨hg, ⟨⟨d, hd, hdc, f, k, hf, hk, hsplit, hfull⟩⟩⟩

end
end Finsler.JoinedRotationSplitConstruction
