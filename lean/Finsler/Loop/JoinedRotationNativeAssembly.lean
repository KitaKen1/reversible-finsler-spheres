module

public import Finsler.Loop.JoinedRotationSplitConstruction
public import Finsler.Loop.JoinedRotationSecondComparison
public import Finsler.Loop.NativeSecondHalfFixedTubeVanishing
public import Finsler.Loop.JoinedRotationSlideCollar
public import Finsler.Loop.CompactJoinUniformTubeLength
import all Finsler.Loop.NativeSecondHalfFixedTubeVanishing
import all Finsler.Loop.JoinedRotationSecondComparison
import all Finsler.Loop.JoinedRotationSplitConstruction

/-! Choose one actual tube and collar before all tested data. The
original full filtered split has a rotation-zero first term; its second
term is the genuine native join-first operation and vanishes on the
required bidegrees, in the identical original A-L+5epsilon target. -/

@[expose] public section
namespace Finsler.JoinedRotationNativeAssembly

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε b c₀ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r < 1)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (hb : 0 < b) (hc₀ : 0 < c₀)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ R > 0, R < c₀ ∧ ∃ hR : R ≤ 1 / 2,
    ∃ κ : ℝ, ∃ hκ : 0 < κ, ∃ hκR : 2 * κ ≤ R,
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
    ∃ θ : ℝ, ∃ hθ : 0 < θ, θ ≤ b ∧ ∃ ζ : ℝ, ∃ hζ : 0 < ζ, ζ ≤ b ∧
    ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x y, length F (α x) + length F (β y) < A) →
      ∃ hg : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) ζ p T,
      ∃ D : JoinedRotationSplitData.Data α β R r hR hr F a ha ha1 (A - L + 5 * ε) θ ζ hθ hζ p T h
        (by linarith [h.1.trans h.2.2]) hg hT,
      ∃ v₂ : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
        (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 5 * ε)))) ((m + 1) + (m + p)),
      (∀ q, v₂.homology q = (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.second).homology q) ∧
      (∀ q, (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.full).homology q =
        (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F (A - L + 5 * ε)
          ζ hζ (by linarith [h.1.trans h.2.2]) hg hT 0).homology q + v₂.homology q) ∧
      ∀ (j k q : ℕ) (htotal : j + k = ((m + 1) + (m + p)) + q), (m + 1) + p < j →
        ((HomologicalComplex.homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q))
          j k (((m + 1) + (m + p)) + q) htotal ≫
        HomologicalComplex.homologyMap (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))
          (((m + 1) + (m + p)) + q)) ≫ v₂.homology q = 0) ∧
        ((HomologicalComplex.homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q))
          j k (((m + 1) + (m + p)) + q) htotal ≫
        HomologicalComplex.homologyMap (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))
          (((m + 1) + (m + p)) + q)) ≫ (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.full).homology q =
          (HomologicalComplex.homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q))
          j k (((m + 1) + (m + p)) + q) htotal ≫
        HomologicalComplex.homologyMap (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))
          (((m + 1) + (m + p)) + q)) ≫ (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F (A - L + 5 * ε)
            ζ hζ (by linarith [h.1.trans h.2.2]) hg hT 0).homology q) := by
  obtain ⟨a, ha, ha1, hcollar⟩ := JoinedRotationSlideCollar.exists_uniform α β h.1
  obtain ⟨κ₀, hκ₀, hκ₀1, hscale⟩ := FirstInputRotationTestedCap.exists_uniform α β r hr F hε hb hradius
  obtain ⟨R₀, hR₀, hR₀1, hlen⟩ := CompactJoinUniformTubeLength.exists_uniform F α β hε
  let R := min (min (R₀ / 2) (κ₀ / 2)) (c₀ / 2)
  have hRpos : 0 < R := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hRc : R < c₀ := (min_le_right _ _).trans_lt (by linarith)
  have hRR₀ : R ≤ R₀ := ((min_le_left _ _).trans (min_le_left _ _)).trans (by linarith)
  have hRκ₀ : R < κ₀ := ((min_le_left _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hR : R ≤ 1 / 2 := hRκ₀.le.trans hκ₀1
  have hR1 : R < 1 := hR.trans_lt (by norm_num)
  obtain ⟨htime, hcorrected⟩ := hlen R hR1 hRR₀
  obtain ⟨hrot₀, hrot₁, hside₀, hside₁⟩ := hcollar R hR
  obtain ⟨ζ, hζ, hζb, hadequate⟩ := hscale R hR hRκ₀
  obtain ⟨θ, hθ, hθb, hsplit⟩ := JoinedRotationSplitConstruction.exists_uniform_on_collar α β R hR h hρr hr F
    hε hb hradius.le a ha ha1 ζ hζ hrot₀ hrot₁ hcorrected hadequate hside₀ hside₁
  obtain ⟨κ, hκ, hκR, η, hη, hηb, hW, σ, hσ, hσb, hsecond⟩ :=
    NativeSecondHalfFixedTubeVanishing.exists_uniform_on_tube m F α β h hρr hr.le hε hb hradius.le R hRpos hR1 htime
  refine ⟨R, hRpos, hRc, hR, κ, hκ, hκR, a, ha, ha1, θ, hθ, hθb, ζ, hζ, hζb, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨hg, ⟨D⟩⟩ := hsplit p L A T hT hshort (fun z => hA z.val.1 z.val.2)
  have hA' : ∀ x y, length F (α x) + length F (β y) < A + ε := by
    intro x y
    exact (hA x y).trans (by linarith)
  have hout := hsecond p L (A + ε) T hT hshort hA'
  dsimp only at hout
  rw [show (A + ε) - L + 4 * ε = A - L + 5 * ε by ring] at hout
  obtain ⟨c₂, hc₂, w₂, v₂, hsource, hw₂, hnative, hv₂, hzero⟩ := hout
  have he₂ (q : ℕ) : v₂.homology q = (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.second).homology q := by
    rw [hv₂]
    exact JoinedRotationSecondComparison.homology_eq m p α β R hR h (by linarith [h.1.trans h.2.2]) hr
      T hT F η (A - L + 5 * ε) hW c₂ hnative a ha ha1 θ ζ hθ hζ hg D hη hc₂ hsource w₂ hw₂
      (fun s x => hside₀ 1 s x) (fun s x => hside₁ 1 s x) (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) q
  have heSplit (q : ℕ) : (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.full).homology q =
      (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F (A - L + 5 * ε)
        ζ hζ (by linarith [h.1.trans h.2.2]) hg hT 0).homology q + v₂.homology q := by
    have he := DegreeLoweringCompositionPostHomology.split (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.full
      (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F (A - L + 5 * ε)
        ζ hζ (by linarith [h.1.trans h.2.2]) hg hT 0) D.second q (D.split q)
    rw [← he₂] at he
    exact he
  refine ⟨hg, D, v₂, he₂, heSplit, ?_⟩
  intro j k q htotal hdegree
  have hz := hzero j k q htotal hdegree
  refine ⟨hz, ?_⟩
  rw [heSplit, Preadditive.comp_add]
  simpa only [Category.assoc, hz, add_zero]

end
end Finsler.JoinedRotationNativeAssembly
