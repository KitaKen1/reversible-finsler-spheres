module

public import Finsler.Loop.SecondHalfZeroFaceGeometry
import all Finsler.Loop.SecondHalfNativeFaceCapDomain

/-! Construct a closed actual bounded native second-half two-cap lift
on the full untrimmed time cylinder. The scale is chosen before all
tested degrees/cochains/thresholds. Its original localized supported
cut is identified before retaining loops, in the exact same target. -/

@[expose] public section
namespace Finsler.FullSecondHalfNativeLift

open CategoryTheory AlgebraicTopology SphereOddDegree
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

def nativeSource {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) :
    TopCat.of (nativeBounded u hr F B) ⟶ TopCat.of (ClosedInterval × X) :=
  SupportedCap.subspaceMap (TopCat.of (nativeDomain u r)) (nativeBounded u hr F B) ≫
    SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (nativeDomain u r)

def nativeCutBound {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) :
    TopCat.of (nativeBounded u hr F B) ⟶ TopCat.of (neighborhood n r) :=
  SupportedCap.subspaceMap (TopCat.of (nativeDomain u r)) (nativeBounded u hr F B) ≫ nativeCut u r

theorem exists_uniform (F : ReversibleMetric n)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∃ hW : ∀ center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u 0 (by norm_num) (by norm_num) ρ 2 ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2,
      ∀ (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0)
      (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
      let h := planeFace (TopCat.of X) 1
      let U := SecondHalfNativeFaceCapDomain.faceCover X η
      let B := A - L + 3 * ε
      ∃ c : ∀ q, (small C U).X (k + (p + q)) ⟶ (chains (TopCat.of (nativeBounded u hr F B))).X q,
      ∀ q,
        (c q ≫ (push (nativeSource u hr F B)).f q =
          (inclusion C U).f (k + (p + q)) ≫ PartialDoubleCap.cap C k p q
            (cochainPullback h k (SupportedSelfCutAdequacy.extension (tube X) (family u 0 (by norm_num) (by norm_num)) 2 k φ))
            (cochainPullback h p (testedExtension (tube X) (family u 0 (by norm_num) (by norm_num))
              (fun _ => r) (fun _ => hr) 2 p T))) ∧
        (c (q + 1) ≫ (chains (TopCat.of (nativeBounded u hr F B))).d (q + 1) q =
          (small C U).d (k + (p + (q + 1))) (k + (p + q)) ≫ c q) ∧
        ((SecondHalfNativeFaceCapDomain.faceMap X η ≫
          JoinedLocalizedCutComparison.familySmallMap u 0 (by norm_num) (by norm_num) ρ r 2
            (JoinedFilteredCap.rectangleCover X η) hW).f (k + (p + q)) ≫
          SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
            k p φ hfar (NormalizedSelfCut.testedCocycle n p hr T) q (k + (p + q)) rfl =
          c q ≫ (push (nativeCutBound u hr F B)).f q) := by
  obtain ⟨η, hη, hηb, hW, hop⟩ := SecondHalfNativeFaceCapDomain.exists_native_closed_lifts F u
    0 (by norm_num) (by norm_num) hρ hρr hr hε hb hradius
  refine ⟨η, hη, hηb, hW, ?_⟩
  intro k p L A φ hφ hfar T hT hshort hA
  obtain ⟨c, hc⟩ := hop k p L A φ hφ hfar T hT hshort hA
  let O : TopCat.{0} := TopCat.of (Outer X)
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let h : C ⟶ O := planeFace (TopCat.of X) 1
  let U := SecondHalfNativeFaceCapDomain.faceCover X η
  let D : Set O := domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2
  let f := retainedMap (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) (fun _ => hr) 2
  let B := A - L + 3 * ε
  let E := PartialDoubleCapDomainFiltered.boundedDomain C (TopCat.of (SphereLoop n)) (h ⁻¹' D)
    (DoubleCapEmbeddingPullback.retained h D f) (JoinedFilteredCap.sublevel F B)
  let m : TopCat.of E ⟶ TopCat.of (nativeBounded u hr F B) := boundedToNative u hr F B
  let c' := fun q => c q ≫ (push m).f q
  have hs : m ≫ nativeSource u hr F B =
      SupportedCap.subspaceMap (TopCat.of (h ⁻¹' D)) E ≫ SupportedCap.subspaceMap C (h ⁻¹' D) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  refine ⟨c', ?_⟩
  intro q
  refine ⟨?_, ?_, ?_⟩
  · have hs' := congrArg (fun f : TopCat.of E ⟶ C => (push f).f q) hs
    simp only [push_comp, HomologicalComplex.comp_f] at hs'
    dsimp only [c']
    rw [Category.assoc, hs']
    exact (hc q).1
  · dsimp only [c']
    rw [Category.assoc, (push m).comm, ← Category.assoc, (hc q).2.1, Category.assoc]
  · have hm : m ≫ nativeCutBound u hr F B =
        SupportedCap.subspaceMap (TopCat.of (h ⁻¹' D)) E ≫ DoubleCapEmbeddingPullback.domainMap h D ≫
          toCut (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2 :=
      bounded_cut u hr F B
    have hm' := congrArg (fun f : TopCat.of E ⟶ TopCat.of (neighborhood n r) => (push f).f q) hm
    simp only [push_comp, HomologicalComplex.comp_f] at hm'
    dsimp only [c']
    rw [Category.assoc, hm']
    exact (hc q).2.2

end
end Finsler.FullSecondHalfNativeLift
