module

public import Finsler.Topology.FirstHalfInteriorCapDomain
public import Finsler.Topology.FirstHalfBoundedCapDeformation

/-! One uniform scale supplies actual closed lifts of the original
supported Thom/tested stages and their retained-output deformation
entirely within the prescribed retained-length sublevel. This is a
two-cap statement; source-approximation comparison and time-prism
descent are subsequent steps. -/

@[expose] public section
namespace Finsler.FirstHalfNativeCapDeformation

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

def nativeCut {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ) :
    FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F A ⟶ TopCat.of (neighborhood n r) :=
  SupportedCap.subspaceMap
    (TopCat.of ((planeFace (TopCat.of X) 1) ⁻¹'
      domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1))
    (FirstHalfBoundedCapDeformation.boundedSet u a ha ha1 hr F A) ≫
  DoubleCapEmbeddingPullback.domainMap (planeFace (TopCat.of X) 1)
    (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1) ≫
  toCut (tube X) (family u a ha.le ha1.le) (fun _ => r) 1

theorem exists_uniform_deformation {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∃ hW : ∀ center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha.le ha1.le ρ 1 ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1,
      ∀ (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0)
      (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      ∃ c : ∀ q,
        (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η)).X (k + (p + q)) ⟶
          (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F (A - L + 3 * ε))).X q,
      ∃ hc : ∀ q, c (q + 1) ≫
        (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F (A - L + 3 * ε))).d (q + 1) q =
          (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η)).d
            (k + (p + (q + 1))) (k + (p + q)) ≫ c q,
      ∀ q,
        (((FirstHalfInteriorCapDomain.faceMap X η) ≫
          JoinedLocalizedCutComparison.familySmallMap u a ha.le ha1.le ρ r 1
            (JoinedFilteredCap.rectangleCover X η) hW).f (k + (p + q)) ≫
          SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
            k p φ hfar (NormalizedSelfCut.testedCocycle n p hr T) q (k + (p + q)) rfl =
          c q ≫ (push (nativeCut u a ha ha1 hr F (A - L + 3 * ε))).f q) ∧
        (((NestedCapHomology.operation k p c hc).post
          (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F (A - L + 3 * ε)))).homology q =
          ((NestedCapHomology.operation k p c hc).post
            (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F (A - L + 3 * ε) 1))).homology q) := by
  obtain ⟨η, hη, hηb, hW, hop⟩ := FirstHalfInteriorCapDomain.exists_native_closed_lifts
    F u a ha ha1 hρ hρr hr hε hb hradius
  refine ⟨η, hη, hηb, hW, ?_⟩
  intro k p L A φ hφ hfar T hT hshort hA
  obtain ⟨c, he⟩ := hop k p L A φ hφ hfar T hT hshort hA
  let c' : ∀ q,
      (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η)).X (k + (p + q)) ⟶
        (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F (A - L + 3 * ε))).X q := c
  have hc : ∀ q, c' (q + 1) ≫
      (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F (A - L + 3 * ε))).d (q + 1) q =
        (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η)).d
          (k + (p + (q + 1))) (k + (p + q)) ≫ c' q := fun q => (he q).2.1
  refine ⟨c', hc, ?_⟩
  intro q
  refine ⟨?_, FirstHalfBoundedCapDeformation.homology_eq u a ha ha1 hr F (A - L + 3 * ε) k p c' hc q⟩
  simpa only [nativeCut, push_comp, HomologicalComplex.comp_f, Category.assoc, c',
    FirstHalfBoundedCapDeformation.boundedSet] using (he q).2.2

end
end Finsler.FirstHalfNativeCapDeformation
