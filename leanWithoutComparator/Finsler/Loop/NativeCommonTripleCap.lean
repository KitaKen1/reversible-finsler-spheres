module

public import Finsler.Loop.OriginalNativeCommonCover
public import Finsler.Loop.FullSecondHalfCompactTimeOperation
public import Finsler.Loop.DegreeLoweringComposition

/-! Compose the actual common-cover first cap with the genuine bounded
native two-cap lift, before taking a time prism. The resulting closed
three-stage operation already takes values in the exact bounded cut
domain. Its common cover and all scales precede tested data. -/

@[expose] public section
namespace Finsler.NativeCommonTripleCap

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
set_option maxHeartbeats 1500000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R η σ κ : ℝ)
  (hn : 1 ≤ n) (hκ : 0 < κ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
    (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X (n + (p + q)) ⟶ E.X q)
  (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
        (n + (p + (q + 1))) (n + (p + q)) ≫ c q)

def operation : DegreeLoweringHomology.Map
    (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ))
    E (n + (n + p)) :=
  DegreeLoweringComposition.compose (OriginalNativeCommonCover.cap α β R η σ κ hn hκ)
    (NestedCapHomology.operation n p c hc)

theorem component (q : ℕ) : (operation α β R η σ κ hn hκ E p c hc).component q =
    eqToHom (congrArg
      (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ)).X
      (Nat.add_assoc n (n + p) q)) ≫
        (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component ((n + p) + q) ≫
          eqToHom (congrArg
            (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
              (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X
            (Nat.add_assoc n p q)) ≫ c q := rfl

theorem component_source (Y : TopCat.{0}) (j : E ⟶ chains Y)
    (φ : singularCochainGroup (ZMod 2) Y n) (ψ : singularCochainGroup (ZMod 2) Y p)
    (f : TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R) ⟶ Y)
    (hi : ∀ q, c q ≫ j.f q =
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫
          (push f).f (n + (p + q)) ≫ PartialDoubleCap.cap Y n p q φ ψ) (q : ℕ) :
    (operation α β R η σ κ hn hκ E p c hc).component q ≫ j.f q =
      eqToHom (congrArg
        (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ)).X
        (Nat.add_assoc n (n + p) q)) ≫
          (OriginalNativeCommonCover.cap α β R η σ κ hn hκ).component ((n + p) + q) ≫
            eqToHom (congrArg
              (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
                (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X
              (Nat.add_assoc n p q)) ≫
                (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
                  (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫
                    (push f).f (n + (p + q)) ≫ PartialDoubleCap.cap Y n p q φ ψ := by
  rw [component]
  simp only [Category.assoc]
  rw [hi q]

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
      ∀ (κ σ : ℝ) (hκ : 0 < κ) (hκR : κ < R) (hσ : 0 < σ),
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
      ∃ v : DegreeLoweringHomology.Map
        (small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ))
        E ((m + 1) + ((m + 1) + p)),
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
      v = operation α β R η σ κ (by omega) hκ E p c hc := by
  obtain ⟨R, hR, hR1, η, hη, hηb, hW, hop⟩ :=
    FullSecondHalfCompactTimeOperation.exists_uniform m F α β h hρr hr hε hb hradius
  refine ⟨R, hR, hR1, η, hη, hηb, hW, ?_⟩
  intro κ σ hκ hκR hσ p L A T hT hshort hA
  obtain ⟨c, hc, w, hsource, hcomponent, hlocalized⟩ := hop p L A T hT hshort hA
  let E := chains (TopCat.of (nativeBounded (CompactNearJoinParameters.inputs α β R hR1) hr F (A - L + 4 * ε)))
  exact ⟨c, hc, w, operation α β R η σ κ (by omega) hκ E p c hc,
    hsource, hcomponent, hlocalized, rfl⟩

end
end Finsler.NativeCommonTripleCap
