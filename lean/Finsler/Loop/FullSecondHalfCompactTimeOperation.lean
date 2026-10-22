module

public import Finsler.Loop.FullSecondHalfNativeTimeOperation
public import Finsler.Loop.CompactNearJoinParameters

/-! Specialize the full native time operation to actual compact original
loop families. The near-pair tube and source scale precede all tested
degrees, cochains and thresholds. The genuine corrected-input join
length estimate gives exactly the original A-L+4epsilon target. -/

@[expose] public section
namespace Finsler.FullSecondHalfCompactTimeOperation

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

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))

theorem tube_compactSpace [CompactSpace P] [CompactSpace Q] (R : ℝ) :
    CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

attribute [local instance] tube_compactSpace

theorem corrected_length (F : ReversibleMetric n) (R : ℝ) (hR : R < 1)
    (z : CompactNearJoinParameters.tube α β R) :
    length F (CompactNearJoinParameters.inputs α β R hR z).val.1 +
      length F (CompactNearJoinParameters.inputs α β R hR z).val.2 =
        length F (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R hR) z) := by
  exact (JoinLengthComparison.length_join F (1 / 2) (by norm_num) (by norm_num)
    (CompactNearJoinParameters.inputs α β R hR z).val.1
    (CompactNearJoinParameters.inputs α β R hR z).val.2
    (CompactNearJoinParameters.inputs α β R hR z).property).symm

theorem exists_uniform [CompactSpace P] [CompactSpace Q]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ R > 0, ∃ hR : R < 1,
      let X := CompactNearJoinParameters.tube α β R
      let u := CompactNearJoinParameters.inputs α β R hR
      ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧
      ∃ hW : ∀ center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u 0 (by norm_num) (by norm_num) ρ 2 ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2,
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
          c q ≫ (push (FullSecondHalfNativeLift.nativeCutBound u hr F (A - L + 4 * ε))).f q) := by
  obtain ⟨R, hR, hR1, hlength⟩ := CompactNearJoinParameters.exists_length_tube α β F hε
  obtain ⟨η, hη, hηb, hW, hop⟩ := FullSecondHalfNativeTimeOperation.exists_uniform m F
    (CompactNearJoinParameters.inputs α β R hR1) h hρr hr hε hb hradius
  refine ⟨R, hR, hR1, η, hη, hηb, hW, ?_⟩
  intro p L A T hT hshort hA
  have hcorrected : ∀ z : CompactNearJoinParameters.tube α β R,
      length F (CompactNearJoinParameters.inputs α β R hR1 z).val.1 +
        length F (CompactNearJoinParameters.inputs α β R hR1 z).val.2 < A + ε := by
    intro z
    rw [corrected_length α β F R hR1 z]
    have hl := hlength z
    have ha := hA z.val.1 z.val.2
    linarith
  have he : (A + ε) - L + 3 * ε = A - L + 4 * ε := by ring
  have hout := hop p L (A + ε) T hT hshort hcorrected
  dsimp only at hout
  rw [he] at hout
  exact hout

end
end Finsler.FullSecondHalfCompactTimeOperation
