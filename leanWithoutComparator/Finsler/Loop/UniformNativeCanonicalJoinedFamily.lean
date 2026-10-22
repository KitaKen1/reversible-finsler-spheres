module

public import Finsler.Loop.NativeFullTimeCanonicalProduct
public import Finsler.Loop.JoinedNativeCanonicalBudget
public import Finsler.Loop.SingleInputUniformCanonicalGeometry
public import Finsler.Loop.CompactJoinedFamilyUniformLength

/-! One actual native full package identifies D.full with canonical
self-cut after the actual joined family, and on high first degrees with
the genuine canonical-first-factor product. All cut geometry is chosen
before tested data. The original native R/kappa and literal output stay
fixed. Identifying the spatial join with genuine product remains separate. -/

@[expose] public section
namespace Finsler.UniformNativeCanonicalJoinedFamily

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 3000000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε t c₀ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r < 1)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (ht : 0 < t) (hc₀ : 0 < c₀)
    (hradius : r < SelfCutLengthControl.radius F hε) (hm : 1 ≤ m) :
    ∃ R > 0, R < c₀ ∧ ∃ hR : R ≤ 1 / 2,
    ∃ κ : ℝ, ∃ hκ : 0 < κ, ∃ hκR : 2 * κ ≤ R,
    ∃ (a_ha : ℝ) (ha : 0 < a_ha) (ha1 : a_ha < 1 / 2),
    ∃ θ : ℝ, ∃ hθ : 0 < θ, θ ≤ t ∧ ∃ ζ : ℝ, ∃ hζ : 0 < ζ, ζ ≤ t ∧
    ∃ σ > 0, σ ≤ t ∧
    ∃ index : (ClosedInterval × CompactNearJoinParameters.tube α β R) →
      Option (CompactRotatedCutData.source (JoinedNativeCanonicalTime.joinedFamily α β R hR) r),
    ∃ hindex : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆
      FirstInputSelfCutCover.cover (JoinedNativeCanonicalTime.joinedFamily α β R hR) r hr κ ρ (index c),
    ∃ hsmall : SingleInputCutMetricAdequacy.Adequate (JoinedNativeCanonicalTime.joinedFamily α β R hR) r hr F ε σ,
    ∀ (p : ℕ) (L a b A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
      (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F L)) p T = 0)
      (hA : ∀ x, SobolevLength.length F (α x) < a)
      (hβ : ∀ y, SobolevLength.length F (β y) < b) (hab : a + b < A),
      ∃ hg : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) ζ p T,
      ∃ D : JoinedRotationSplitData.Data α β R r hR hr F a_ha ha ha1 (A - L + 5 * ε) θ ζ hθ hζ p T h
        (by linarith [h.1.trans h.2.2]) hg hT,
      ∃ hΓ : ∀ x, SobolevLength.length F (JoinedNativeCanonicalTime.joinedFamily α β R hR x) < A + 2 * ε,
      (∀ q, D.full.homology q =
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
          (push (CompactInputShortMaps.family (JoinedNativeCanonicalTime.joinedFamily α β R hR) F (A + 2 * ε) hΓ))).post
          (eqToHom (congrArg (fun c : ℝ => chains (TopCat.of (SelfCutOscillation.short F c)))
            (show (A + 2 * ε) - L + 3 * ε = A - L + 5 * ε by ring)))).homology q) ∧
      ∀ (i j k : ℕ) (hij : i + j = (m + 1) + k), 1 < i →
        FilteredBilinearLoopProduct.crossMap (TopCat.of P) (TopCat.of Q) ((m + p) + i) j
          (((m + 1) + (m + p)) + k) (by omega) ≫
          (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.full).homology k =
        (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
          (push (CompactInputShortMaps.family α F a hA))).homology i ⊗ₘ
          PoolCap.push (StrictLengthProductFamilies.rightInput β F b hβ) j) ≫
        FilteredBilinearLoopProduct.crossMap (lengthSpace F (a - L + 3 * ε)) (lengthSpace F b) i j ((m + 1) + k) hij ≫
          (StrictLengthProductBudget.operation F (L := L) hab hε (dim_pos m)).homology k := by
  have hρr' : ρ < r := by linarith [h.1.trans h.2.2]
  obtain ⟨u, hu, _hu1, hlength⟩ := CompactJoinedFamilyUniformLength.exists_uniform F α β hε
  let c := min u c₀
  have hc : 0 < c := lt_min hu hc₀
  obtain ⟨R, hRp, hRc, hR, κ, hκ, hκR, s, hs, hs1, θ, hθ, hθt, ζ, hζ, hζt, htested⟩ :=
    NativeFullTimeCanonicalProduct.exists_uniform α β h hρr hr F hε ht hc hradius hm
  have hRu : R ≤ u := hRc.le.trans (min_le_left _ _)
  have hRc₀ : R < c₀ := hRc.trans_le (min_le_right _ _)
  obtain ⟨σ, hσ, hσt, index, hindex, hsmall⟩ := SingleInputUniformCanonicalGeometry.exists_scale
    (JoinedNativeCanonicalTime.joinedFamily α β R hR) r hr hκ hρr' F hε ht
  refine ⟨R, hRp, hRc₀, hR, κ, hκ, hκR, s, hs, hs1, θ, hθ, hθt, ζ, hζ, hζt,
    σ, hσ, hσt, index, hindex, hsmall, ?_⟩
  intro p L a b A T hT hshort hA hβ hab
  obtain ⟨hg, D, hproduct⟩ := htested p L a b A T hT hshort hA hβ hab
  have hpair : ∀ x y, SobolevLength.length F (α x) + SobolevLength.length F (β y) < A :=
    fun x y => (add_lt_add (hA x) (hβ y)).trans hab
  have hΓ : ∀ x, SobolevLength.length F (JoinedNativeCanonicalTime.joinedFamily α β R hR x) < A + 2 * ε := by
    intro x
    exact (hlength R hR hRu A hpair x).trans (by linarith)
  refine ⟨hg, D, hΓ, ?_, hproduct⟩
  intro q
  exact JoinedNativeCanonicalBudget.full_homology α β R r hR hr F s hs hs1 (A - L + 5 * ε) θ ζ hθ hζ
    p T h hρr' hg hT D ε (A + 2 * ε) L hε (by ring) κ σ hσ hradius hsmall index hindex hshort hΓ hm q

end
end Finsler.UniformNativeCanonicalJoinedFamily
