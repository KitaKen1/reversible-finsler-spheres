module

public import Finsler.Topology.FirstHalfInteriorFaceDomain
public import Finsler.Topology.DoubleCapEmbeddingBoundary
public import Finsler.Topology.DoubleCapEmbeddingFactor
public import Finsler.Topology.JoinedLocalizedCutComparison

/-! Construct actual closed bounded cut-domain lifts on the genuine
last face of the second-half time square. Allow a=0, so the original
full second-half cylinder is covered. A single source scale precedes
all tested cochains, degrees and length thresholds. The actual
localized supported cap and its bounded native cut diagram agree. -/

@[expose] public section
namespace Finsler.SecondHalfNativeFaceCapDomain

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000

def faceCover (X : Type) [PseudoMetricSpace X] (η : ℝ) :
    ((ClosedInterval × ClosedInterval) × X) → Set (ClosedInterval × X) :=
  DoubleCapEmbeddingPullback.cover (planeFace (TopCat.of X) 1) (JoinedFilteredCap.rectangleCover X η)

def faceMap (X : Type) [PseudoMetricSpace X] (η : ℝ) :
    small (TopCat.of (ClosedInterval × X)) (faceCover X η) ⟶
      small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) :=
  SmallRetractionComparison.map (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
    (faceCover X η) (JoinedFilteredCap.rectangleCover X η) (planeFace (TopCat.of X) 1) id
    (fun i z hz => show planeFace (TopCat.of X) 1 z ∈ JoinedFilteredCap.rectangleCover X η i from hz)

theorem exists_native_closed_lifts {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∃ hW : ∀ center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ 2 ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) 2,
      ∀ (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0)
      (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      let O : TopCat.{0} := TopCat.of (Outer X)
      let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
      let h : C ⟶ O := planeFace (TopCat.of X) 1
      let W : ((ClosedInterval × ClosedInterval) × X) → Set O := JoinedFilteredCap.rectangleCover X η
      let U : ((ClosedInterval × ClosedInterval) × X) → Set C := faceCover X η
      let D : Set O := domain (tube X) (family u a ha ha1) (fun _ => r) 2
      let f : TopCat.of D ⟶ TopCat.of (SphereLoop n) :=
        retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) 2
      let B : Set (SphereLoop n) := JoinedFilteredCap.sublevel F (A - L + 3 * ε)
      let E : Set (TopCat.of (h ⁻¹' D)) := PartialDoubleCapDomainFiltered.boundedDomain C (TopCat.of (SphereLoop n))
        (h ⁻¹' D) (DoubleCapEmbeddingPullback.retained h D f) B
      let M : small C U ⟶ small O W := faceMap X η
      ∃ c : ∀ q, (small C U).X (k + (p + q)) ⟶ (chains (TopCat.of E)).X q,
      ∀ q,
        (c q ≫ (push (SupportedCap.subspaceMap (TopCat.of (h ⁻¹' D)) E)).f q ≫
          (push (SupportedCap.subspaceMap C (h ⁻¹' D))).f q =
          (inclusion C U).f (k + (p + q)) ≫ PartialDoubleCap.cap C k p q
            (cochainPullback h k (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) 2 k φ))
            (cochainPullback h p (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) 2 p T))) ∧
        (c (q + 1) ≫ (chains (TopCat.of E)).d (q + 1) q =
          (small C U).d (k + (p + (q + 1))) (k + (p + q)) ≫ c q) ∧
        ((M ≫ JoinedLocalizedCutComparison.familySmallMap u a ha ha1 ρ r 2 W hW).f (k + (p + q)) ≫
          SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
            k p φ hfar (NormalizedSelfCut.testedCocycle n p hr T) q (k + (p + q)) rfl =
          c q ≫ (push (SupportedCap.subspaceMap (TopCat.of (h ⁻¹' D)) E)).f q ≫
            (push (DoubleCapEmbeddingPullback.domainMap h D)).f q ≫
              (push (toCut (tube X) (family u a ha ha1) (fun _ => r) 2)).f q) := by
  have htwo : 2 * ρ < r := by linarith
  obtain ⟨η₀, hη₀, hη₀b, hrefine⟩ := JoinedRectangleRefinement.exists_scale u a ha ha1 hρ htwo hb
  obtain ⟨η, hη, hηη₀, had⟩ := JoinedCapAdequacy.exists_filtered_scale F u a ha ha1
    hρ hρr hr hε hη₀ hradius
  have hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ 2 ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) 2 := by
    intro center
    rcases hrefine 2 center with hf | hn
    · exact Or.inl ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hf)
    · exact Or.inr ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hn)
  refine ⟨η, hη, hηη₀.trans hη₀b, hW, ?_⟩
  intro k p L A φ hφ hfar T hT hshort hA
  let O : TopCat.{0} := TopCat.of (Outer X)
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let h : C ⟶ O := planeFace (TopCat.of X) 1
  let W := JoinedFilteredCap.rectangleCover X η
  let U := faceCover X η
  let D := domain (tube X) (family u a ha ha1) (fun _ => r) 2
  let f := retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) 2
  let B := JoinedFilteredCap.sublevel F (A - L + 3 * ε)
  let φ' := SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) 2 k φ
  let ψ' := testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) 2 p T
  have hgood : ∀ q (σ : (O.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
      (TopCat.toSSet.obj O).ιChainComplex σ.val ≫ PartialDoubleCap.cap O k p q φ' ψ' ≠ 0 →
      ∀ z ∈ Set.range (O.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B := by
    intro q σ hcap z hz
    obtain ⟨center, hc⟩ := (TopCat.mem_smallSingularSubcomplex_iff O W σ.val).mp σ.property
    have hcap' : ((TopCat.toSSet.obj O).ιChainComplex σ.val ≫
        RelativeCapAssociativity.absoluteChain O k (p + q) (k + (p + q)) rfl φ') ≫
          RelativeCapAssociativity.absoluteChain O p q (p + q) rfl ψ' ≠ 0 := by
      simpa only [PartialDoubleCap.cap, Category.assoc] using hcap
    exact had center.1 center.2 (Set.range (O.toSSetObjEquiv _ σ.val)) hc 2 k p q L A φ hfar T hshort
      (fun w _ => hA w.2) σ.val Set.Subset.rfl hcap' z hz
  have hmono : ∀ q, Mono ((push h).f q) := FirstHalfInteriorFaceDomain.push_face_mono (TopCat.of X)
  have hgoodC : ∀ q (σ : (C.smallSingularSubcomplex U : SSet) _⦋k + (p + q)⦌),
      (TopCat.toSSet.obj C).ιChainComplex σ.val ≫
        PartialDoubleCap.cap C k p q (cochainPullback h k φ') (cochainPullback h p ψ') ≠ 0 →
      ∀ z ∈ Set.range (C.toSSetObjEquiv _ σ.val),
        ∃ hz : z ∈ h ⁻¹' D, DoubleCapEmbeddingPullback.retained h D f ⟨z, hz⟩ ∈ B :=
    DoubleCapEmbeddingPullback.good (Z := C) (X := O) (Y := TopCat.of (SphereLoop n))
      h W D f B k p φ' ψ' hmono hgood
  let c := PartialDoubleCapDomainFiltered.component C (TopCat.of (SphereLoop n)) U
    (h ⁻¹' D) (DoubleCapEmbeddingPullback.retained h D f) B k p
    (cochainPullback h k φ') (cochainPullback h p ψ') hgoodC
  have hcap := JoinedCochainBoundary.boundary u a ha ha1 η ρ r hr 2 hW k p φ hφ hfar T hT
  have hcommO : ∀ q, ((inclusion O W).f (k + (p + (q + 1))) ≫
      PartialDoubleCap.cap O k p (q + 1) φ' ψ') ≫ (chains O).d (q + 1) q =
        (small O W).d (k + (p + (q + 1))) (k + (p + q)) ≫
          ((inclusion O W).f (k + (p + q)) ≫ PartialDoubleCap.cap O k p q φ' ψ') := by
    intro q
    simpa only [Category.assoc] using hcap q
  refine ⟨c, ?_⟩
  intro q
  refine ⟨PartialDoubleCapDomainFiltered.source_inclusion C (TopCat.of (SphereLoop n)) U
      (h ⁻¹' D) (DoubleCapEmbeddingPullback.retained h D f) B k p
      (cochainPullback h k φ') (cochainPullback h p ψ') hgoodC q,
    PartialDoubleCapDomainFiltered.component_boundary C (TopCat.of (SphereLoop n)) U
      (h ⁻¹' D) (DoubleCapEmbeddingPullback.retained h D f) B k p
      (cochainPullback h k φ') (cochainPullback h p ψ') hgoodC
      (DoubleCapEmbeddingBoundary.boundary (Z := C) (X := O) h W hmono k p φ' ψ' hcommO) q, ?_⟩
  have hn := JoinedLocalizedCutComparison.domain_agreement u a ha ha1 ρ r 2 W hW k p q φ hfar
    (NormalizedSelfCut.testedCocycle n p hr T)
    (PartialDoubleCapFiltered.domainComponent O (TopCat.of (SphereLoop n)) W D f B k p φ' ψ' hgood q)
    (by simpa only [O, D, φ', ψ', JoinedLocalizedCutComparison.tested_pullback, testedExtension] using
      PartialDoubleCapFiltered.domain_inclusion O (TopCat.of (SphereLoop n)) W D f B k p φ' ψ' hgood q)
  have hf := DoubleCapEmbeddingFactor.domain_factor (Z := C) (X := O) (Y := TopCat.of (SphereLoop n))
    h W D f B k p φ' ψ' hmono hgood q
  rw [HomologicalComplex.comp_f, Category.assoc, hn, ← Category.assoc]
  simpa only [Category.assoc, c, faceMap, faceCover, U, C, O, h, W] using
    (congrArg (fun g => g ≫ (push (toCut (tube X) (family u a ha ha1) (fun _ => r) 2)).f q) hf).symm

end
end Finsler.SecondHalfNativeFaceCapDomain
