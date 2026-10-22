module

public import Finsler.Loop.NativeJoinProductVanishing
public import Finsler.Loop.FixedTubeProductTimeHomology
public import Finsler.Loop.CompactJoinCapLocalization
public import Finsler.Loop.DegreeLoweringComposition
import all Finsler.Topology.OriginalSecondHalfTimeModelComparison
import all Finsler.Loop.NativeJoinProductVanishing
import all Finsler.Loop.FixedTubeProductTimeHomology

/-! Construct the native join-first second-half operation with uniform
bidegree vanishing. Accept a supplied positive tube and its actual join-length bound before both source scales,
all tested degrees, cochains and length thresholds. The exact retained
bound A-L+4 epsilon and output degree zero are preserved. -/

@[expose] public section
namespace Finsler.NativeSecondHalfFixedTubeVanishing

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.SecondHalfZeroFaceGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]

theorem exists_uniform_on_tube [CompactSpace P] [CompactSpace Q]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε)
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1)
    (hlength : ∀ z : OriginalSecondHalfCompactTube.tube α β R,
      length F (OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR1) z).2 <
        length F (α z.val.1) + length F (β z.val.2.2) + ε) :
    ∃ κ : ℝ, ∃ hκ : 0 < κ, ∃ hκR : 2 * κ ≤ R,
      let X := CompactNearJoinParameters.tube α β R
      let u := CompactNearJoinParameters.inputs α β R hR1
      ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧
      ∃ hW : ∀ center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u 0 (by norm_num) (by norm_num) ρ 2 ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2,
      ∃ σ : ℝ, ∃ hσ : 0 < σ, σ ≤ b ∧
      ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x y, length F (α x) + length F (β y) < A) →
      let C := TopCat.of (ClosedInterval × X)
      let U := SecondHalfNativeFaceCapDomain.faceCover X η
      let E := chains (TopCat.of (nativeBounded u hr F (A - L + 4 * ε)))
      ∃ c : ∀ q, (small C U).X ((m + 1) + (p + q)) ⟶ E.X q,
      ∃ hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
        (small C U).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q,
      ∃ w : DegreeLoweringHomology.Map (chains (TopCat.of X)) E (m + p),
      ∃ v : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
        (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 4 * ε)))) ((m + 1) + (m + p)),
      (∀ q, c q ≫ (push (FullSecondHalfNativeLift.nativeSource u hr F (A - L + 4 * ε))).f q =
        (inclusion C U).f ((m + 1) + (p + q)) ≫ PartialDoubleCap.cap C (m + 1) p q
          (FullSecondHalfNativeTimeOperation.thom u (by omega) h)
          (FullSecondHalfNativeTimeOperation.tested u hr p T)) ∧
      (∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
        ClosedCapDegreeTransport.align m p
          (CutDomainTimePrism.retracted (TopCat.of X) U
            (FullSecondHalfAnnularInputs.faceCover_open X η) (FullSecondHalfAnnularInputs.faceCover_univ X η hη)
            E m p c) q) ∧
      (∀ q, (SecondHalfNativeFaceCapDomain.faceMap X η ≫
          JoinedLocalizedCutComparison.familySmallMap u 0 (by norm_num) (by norm_num) ρ r 2
            (JoinedFilteredCap.rectangleCover X η) hW).f ((m + 1) + (p + q)) ≫
          SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
            (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
            (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
            (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl =
          c q ≫ (push (FullSecondHalfNativeLift.nativeCutBound u hr F (A - L + 4 * ε))).f q) ∧
      v = FullSecondHalfJoinTimeOperation.joined α β (by omega) hκ hκR hR1 hr F (A - L + 4 * ε) (m + p) w ∧
      ∀ (j k q : ℕ) (htotal : j + k = ((m + 1) + (m + p)) + q), (m + 1) + p < j →
        HomologicalComplex.homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q))
          j k (((m + 1) + (m + p)) + q) htotal ≫
        HomologicalComplex.homologyMap (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))
          (((m + 1) + (m + p)) + q) ≫ v.homology q = 0 := by
  obtain ⟨η, hη, hηb, hW, hnative⟩ := FullSecondHalfNativeTimeOperation.exists_uniform m F
    (CompactNearJoinParameters.inputs α β R hR1) h hρr hr hε hb hradius
  obtain ⟨σ, hσ, hσb, hold⟩ := FixedTubeProductTimeHomology.exists_uniform α β
    (OriginalSecondHalfCompactTube.tube α β R) (OriginalSecondHalfCompactTube.near α β R hR1)
    (OriginalSecondHalfCompactTube.compact α β R) r hr F (by omega) h hρr hε hb hradius
  let κ : ℝ := R / 4
  have hκ : 0 < κ := div_pos hR (by norm_num)
  have hκR : 2 * κ ≤ R := by dsimp only [κ]; linarith
  refine ⟨κ, hκ, hκR, η, hη, hηb, hW, σ, hσ, hσb, ?_⟩
  intro p L A T hT hshort hA
  have hcorrected : ∀ z : CompactNearJoinParameters.tube α β R,
      length F (CompactNearJoinParameters.inputs α β R hR1 z).val.1 +
        length F (CompactNearJoinParameters.inputs α β R hR1 z).val.2 < A + ε := by
    intro z
    rw [FullSecondHalfCompactTimeOperation.corrected_length α β F R hR1 z]
    have hl := hlength (CompactNearJoinParameters.timeMap α β R (0, z))
    have ha := hA z.val.1 z.val.2
    change length F (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R hR1) z) <
      length F (α z.val.1) + length F (β z.val.2) + ε at hl
    linarith
  have holdLength : ∀ z : OriginalSecondHalfCompactTube.tube α β R,
      length F (OriginalSecondHalfFamily.family α β (OriginalSecondHalfCompactTube.tube α β R)
        (OriginalSecondHalfCompactTube.near α β R hR1) z).2 < A + ε := by
    intro z
    have hl := hlength z
    have ha := hA z.val.1 z.val.2.2
    linarith
  have he : (A + ε) - L + 3 * ε = A - L + 4 * ε := by ring
  have hn := hnative p L (A + ε) T hT hshort hcorrected
  dsimp only at hn
  rw [he] at hn
  obtain ⟨c, hc, w, hsource, hw, hlocalized⟩ := hn
  have ho := hold κ hκ (OriginalSecondHalfCompactTube.contains_near α β hκR)
    (m + 1) p L (A + ε) (CompactJoinCocycle.timeCocycle α β (by omega) hκ)
    (CompactJoinCocycle.timeCocycle_closed α β (by omega) hκ)
    (CompactJoinCocycle.timeCocycle_far_zero α β (by omega) hκ) T hT hshort holdLength
  rw [he] at ho
  obtain ⟨C, hu, hzero⟩ := ho
  refine ⟨c, hc, w, FullSecondHalfJoinTimeOperation.joined α β (by omega) hκ hκR hR1 hr F
    (A - L + 4 * ε) (m + p) w, hsource, hw, hlocalized, rfl, ?_⟩
  intro j k q htotal hdegree
  exact NativeJoinProductVanishing.homology_zero α β R hR1 r hr F (A - L + 4 * ε)
    η σ κ hκ hκR hη hσ h p T c hc w hw hsource C hu j k q htotal
    (hzero j k q (by omega) hdegree)

end
end Finsler.NativeSecondHalfFixedTubeVanishing
