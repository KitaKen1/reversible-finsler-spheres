module

public import Finsler.Loop.FullSecondHalfAnnularInputs

/-! Construct the actual full native second-half time operation in its
length-bounded cut domain. The genuine annular cocycle supplies both
endpoint zeros; no endpoint hypothesis or global closure of a tested
zero extension is assumed. The source scale precedes every tested
degree, cochain and length threshold. -/

@[expose] public section
namespace Finsler.FullSecondHalfNativeTimeOperation

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
set_option maxHeartbeats 1600000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n))

def thom (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) n :=
  cochainPullback (planeFace (TopCat.of X) 1) n
    (SupportedSelfCutAdequacy.extension (tube X) (family u 0 (by norm_num) (by norm_num)) 2 n
      (AnnularSelfCut.cocycle n hn h))

def tested {r : ℝ} (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) p :=
  cochainPullback (planeFace (TopCat.of X) 1) p
    (testedExtension (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) (fun _ => hr) 2 p T)

def retainedOutput {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) :
    TopCat.of (nativeBounded u hr F B) ⟶ TopCat.of (JoinedFilteredCap.sublevel F B) :=
  restriction (nativeRetained u hr) (nativeBounded u hr F B)
    (JoinedFilteredCap.sublevel F B) (fun _ hz => hz)

theorem exists_uniform (m : ℕ) (F : ReversibleMetric (m + 1))
    (u : C(X, H1JoinContinuity.composable (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧
      ∃ hW : ∀ center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u 0 (by norm_num) (by norm_num) ρ 2 ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2,
      ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      let C := TopCat.of (ClosedInterval × X)
      let U := SecondHalfNativeFaceCapDomain.faceCover X η
      let E := chains (TopCat.of (nativeBounded u hr F (A - L + 3 * ε)))
      ∃ c : ∀ q, (small C U).X ((m + 1) + (p + q)) ⟶ E.X q,
      ∃ hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
        (small C U).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q,
      ∃ w : DegreeLoweringHomology.Map (chains (TopCat.of X)) E (m + p),
      (∀ q, c q ≫ (push (FullSecondHalfNativeLift.nativeSource u hr F (A - L + 3 * ε))).f q =
        (inclusion C U).f ((m + 1) + (p + q)) ≫ PartialDoubleCap.cap C (m + 1) p q
          (thom u (by omega) h) (tested u hr p T)) ∧
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
          c q ≫ (push (FullSecondHalfNativeLift.nativeCutBound u hr F (A - L + 3 * ε))).f q) := by
  obtain ⟨η, hη, hηb, hW, hop⟩ := FullSecondHalfNativeLift.exists_uniform u F
    (h.1.trans h.2.2) hρr hr hε hb hradius
  refine ⟨η, hη, hηb, hW, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨c, he⟩ := hop (m + 1) p L A
    (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSelfCut.cocycle_closed (m + 1) (by omega) h)
    (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) T hT hshort hA
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let U := SecondHalfNativeFaceCapDomain.faceCover X η
  let E := chains (TopCat.of (nativeBounded u hr F (A - L + 3 * ε)))
  let c' : ∀ q, (small C U).X ((m + 1) + (p + q)) ⟶ E.X q := c
  have hc : ∀ q, c' (q + 1) ≫ E.d (q + 1) q =
      (small C U).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c' q := fun q => (he q).2.1
  let j := push (FullSecondHalfNativeLift.nativeSource u hr F (A - L + 3 * ε))
  have hj : ∀ q, Mono (j.f q) := FullSecondHalfAnnularInputs.projection_mono u hr F (A - L + 3 * ε)
  have hi : ∀ q, c' q ≫ j.f q = (inclusion C U).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap C (m + 1) p q (thom u (by omega) h) (tested u hr p T) := fun q => (he q).1
  have hφ := FullSecondHalfAnnularInputs.annular_inner_zero u (by omega : 1 ≤ m + 1) h
  have h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ FullSecondHalfAnnularInputs.collar u δ := by
    intro x
    change distance (m + 1) (JoinedHalfCollars.secondFamily u (0, x)) ≤ δ
    rw [FullSecondHalfAnnularInputs.distance_zero]
    exact h.1.le
  have h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ FullSecondHalfAnnularInputs.collar u δ := by
    intro x
    change distance (m + 1) (JoinedHalfCollars.secondFamily u (1, x)) ≤ δ
    rw [FullSecondHalfAnnularInputs.distance_one]
    exact h.1.le
  let w : DegreeLoweringHomology.Map (chains (TopCat.of X)) E (m + p) :=
    CutDomainTimePrism.operation (TopCat.of X) U
      (FullSecondHalfAnnularInputs.faceCover_open X η) (FullSecondHalfAnnularInputs.faceCover_univ X η hη)
      E m p c' (FullSecondHalfAnnularInputs.collar u δ)
      (thom u (by omega) h) (tested u hr p T) hφ j hj hi hc h₀ h₁
  exact ⟨c', hc, w, hi, fun _ => rfl, fun q => (he q).2.2⟩

end
end Finsler.FullSecondHalfNativeTimeOperation
