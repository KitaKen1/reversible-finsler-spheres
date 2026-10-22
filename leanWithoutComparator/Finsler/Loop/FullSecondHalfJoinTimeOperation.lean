module

public import Finsler.Loop.FullSecondHalfCompactTimeOperation
public import Finsler.Loop.CompactJoinCapLocalization
public import Finsler.Loop.DegreeLoweringComposition

/-! The actual join-first full native second-half time operation.
Compose the genuine localized normalized join cap with the constructed
bounded time operation and retain loops in the identical length sublevel.
The join radius, tube and source scale precede all tested data. -/

@[expose] public section
namespace Finsler.FullSecondHalfJoinTimeOperation

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

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))

def joined (hn : 1 ≤ n) {κ R : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hR : R < 1)
    {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) (d : ℕ)
    (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
      (chains (TopCat.of (nativeBounded (CompactNearJoinParameters.inputs α β R hR) hr F B))) d) :
    DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (n + d) :=
  (DegreeLoweringComposition.compose (CompactJoinCapLocalization.unrefined α β hn hκ hκR) w).post
    (push (FullSecondHalfNativeTimeOperation.retainedOutput (CompactNearJoinParameters.inputs α β R hR) hr F B))

theorem component (hn : 1 ≤ n) {κ R : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hR : R < 1)
    {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) (d : ℕ)
    (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
      (chains (TopCat.of (nativeBounded (CompactNearJoinParameters.inputs α β R hR) hr F B))) d) (q : ℕ) :
    (joined α β hn hκ hκR hR hr F B d w).component q =
      eqToHom (congrArg (chains (TopCat.of (P × Q))).X (Nat.add_assoc n d q)) ≫
        (CompactJoinCapLocalization.unrefined α β hn hκ hκR).component (d + q) ≫
          w.component q ≫
            (push (FullSecondHalfNativeTimeOperation.retainedOutput
              (CompactNearJoinParameters.inputs α β R hR) hr F B)).f q := by
  simp only [joined, DegreeLoweringHomology.Map.post, DegreeLoweringComposition.component, Category.assoc]

theorem homology (hn : 1 ≤ n) {κ R : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (hR : R < 1)
    {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) (d : ℕ)
    (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
      (chains (TopCat.of (nativeBounded (CompactNearJoinParameters.inputs α β R hR) hr F B))) d) (q : ℕ) :
    (joined α β hn hκ hκR hR hr F B d w).homology q =
      eqToHom (congrArg (fun k : ℕ => (chains (TopCat.of (P × Q))).homology k) (Nat.add_assoc n d q)) ≫
        (CompactJoinCapLocalization.unrefined α β hn hκ hκR).homology (d + q) ≫
          w.homology q ≫
            HomologicalComplex.homologyMap (push (FullSecondHalfNativeTimeOperation.retainedOutput
              (CompactNearJoinParameters.inputs α β R hR) hr F B)) q := by
  rw [joined, DegreeLoweringHomology.Map.post_homology, DegreeLoweringComposition.homology]
  simp only [Category.assoc]

theorem exists_uniform [CompactSpace P] [CompactSpace Q]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ R > 0, ∃ hR : R < 1, ∃ κ : ℝ, ∃ hκ : 0 < κ, ∃ hκR : 2 * κ ≤ R,
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
      v = joined α β (by omega) hκ hκR hR hr F (A - L + 4 * ε) (m + p) w := by
  obtain ⟨R, hR, hR1, η, hη, hηb, hW, hop⟩ :=
    FullSecondHalfCompactTimeOperation.exists_uniform m F α β h hρr hr hε hb hradius
  let κ : ℝ := R / 4
  have hκ : 0 < κ := div_pos hR (by norm_num)
  have hκR : 2 * κ ≤ R := by dsimp only [κ]; linarith
  refine ⟨R, hR, hR1, κ, hκ, hκR, η, hη, hηb, hW, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨c, hc, w, hsource, hcomponent, hlocalized⟩ := hop p L A T hT hshort hA
  exact ⟨c, hc, w, joined α β (by omega) hκ hκR hR1 hr F (A - L + 4 * ε) (m + p) w,
    hsource, hcomponent, hlocalized, rfl⟩

end
end Finsler.FullSecondHalfJoinTimeOperation
