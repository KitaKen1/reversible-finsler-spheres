module

public import Finsler.Loop.RotationTimeCoverIndependence
public import Finsler.Loop.GeometricTimeCoverIndependence
public import Finsler.Loop.UniformNativeCanonicalProduct
public import Finsler.Loop.OriginalFirstHalfUniformCutThenJoinTime
public import Finsler.Loop.JoinedRotationNativeAssembly

/-! The actual native full joined time, on the required high first
homology degrees, is the genuine product(D_T(first),beta) in the literal
coupled short target. Every geometry/refinement choice precedes all
later cochains and individual bounds. Actual independent eta/zeta time
models are compared before using rotation and native second-half zero. -/

@[expose] public section
namespace Finsler.NativeFullTimeCanonicalProduct

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
  obtain ⟨uC, huC, _huC1, hscaleC⟩ := OriginalFirstHalfUniformCutThenJoinTime.exists_uniform α β h hρr' hr F hε ht hradius
  obtain ⟨uP, huP, _huP1, hscaleP⟩ := UniformNativeCanonicalProduct.exists_uniform α β h hρr' hr F hε ht hradius hm
  let c := min (min uC uP) c₀
  have hc : 0 < c := lt_min (lt_min huC huP) hc₀
  obtain ⟨R, hRp, hRc, hR, κ, hκ, hκR, a_ha, ha, ha1, θ, hθ, hθt, ζ, hζ, hζt, htestedN⟩ :=
    JoinedRotationNativeAssembly.exists_uniform α β h hρr hr F hε ht hc hradius
  have hRc₀ : R < c₀ := hRc.trans_le (min_le_right _ _)
  have hRC : R < uC := hRc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hRP : R < uP := hRc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨ηC, hηC, _hηCt, hdataC⟩ := hscaleC R hR hRC
  obtain ⟨hκRC, htestedC⟩ := hdataC κ hκ hκR
  obtain ⟨ηP, hηP, _hηPt, hdataP⟩ := hscaleP R hR hRP
  obtain ⟨hκRP, σP, hσP, _hσPt, indexP, hindexP, firstP, hfirstP, otherP, hotherP, hsmallP, htestedP⟩ := hdataP κ hκ hκR
  refine ⟨R, hRp, hRc₀, hR, κ, hκ, hκR, a_ha, ha, ha1, θ, hθ, hθt, ζ, hζ, hζt, ?_⟩
  intro p L a b A T hT hshort hA hβ hab
  have hpair : ∀ x y, SobolevLength.length F (α x) + SobolevLength.length F (β y) < A :=
    fun x y => (add_lt_add (hA x) (hβ y)).trans hab
  obtain ⟨hg, D, v₂, _hv₂, _hsplit, hnative⟩ := htestedN p L A T hT hshort hpair
  obtain ⟨_goodΓ, oldGoodC, _goodχ, _goodδ, goodC, hcup⟩ := htestedC p L A T hT hshort hpair
  obtain ⟨_goodN, goodP, hproduct⟩ := htestedP p L a b A T hT hshort hA hβ hab
  refine ⟨hg, D, ?_⟩
  intro i j k hij hi
  have hbridge : (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F (A - L + 5 * ε)
      ζ hζ hρr' hg hT 0).homology k =
    (OriginalFirstHalfCutThenJoinTime.operation α β R r ηP hR hr hκ hκRP hηP h hρr' p T F
      (A - L + 5 * ε) goodP hT).homology k :=
    (RotationTimeCoverIndependence.joined_homology α β R r hR hr p T h F (A - L + 5 * ε)
      ζ ηC hζ hηC hρr' hg oldGoodC hT hκ hκR 0 k).trans
      ((FirstInputRotationJoinedTime.homology_eq α β hκ hκR hR hr p T h F (A - L + 5 * ε)
        ηC hηC hρr' oldGoodC hT k).trans
        ((hcup k).trans (GeometricTimeCoverIndependence.geometric_homology α β R r hR hr h p T hκ hκRC F
          (A - L + 5 * ε) ηC ηP hηC hηP hρr' goodC goodP hT k)))
  have hn := (hnative ((m + p) + i) j k (by omega) (by omega)).2
  have hn' : FilteredBilinearLoopProduct.crossMap (TopCat.of P) (TopCat.of Q) ((m + p) + i) j
      (((m + 1) + (m + p)) + k) (by omega) ≫
      (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β (by omega) hκ hκR) D.full).homology k =
    FilteredBilinearLoopProduct.crossMap (TopCat.of P) (TopCat.of Q) ((m + p) + i) j
      (((m + 1) + (m + p)) + k) (by omega) ≫
      (FirstInputRotationJoinedTime.joined α β hκ hκR hR hr p T h F (A - L + 5 * ε)
        ζ hζ hρr' hg hT 0).homology k := by
    simpa only [SmallCrossHomologyBridge.ambient] using hn
  rw [hn', hbridge]
  exact (hproduct k).1 i j hij

end
end Finsler.NativeFullTimeCanonicalProduct
