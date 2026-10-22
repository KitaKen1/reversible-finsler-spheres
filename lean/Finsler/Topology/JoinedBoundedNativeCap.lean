module

public import Finsler.Topology.JoinedBoundedCutDomain
public import Finsler.Topology.JoinedLocalizedCutComparison

/-! The original supported Thom/tested stages themselves factor through
the genuine cut domain with its retained-length bound. The identification
holds before postcomposing the retained map and before homology. -/

@[expose] public section
namespace Finsler.JoinedBoundedNativeCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

theorem exists_native_domain_lifts {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∃ hW : ∀ (i : Fin 3) center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ i ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i,
      ∀ (i : Fin 3) (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0)
      (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      let Z := TopCat.of (Outer X)
      let D := domain (tube X) (family u a ha ha1) (fun _ => r) i
      let f := retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i
      let B := JoinedFilteredCap.sublevel F (A - L + 3 * ε)
      let E := PartialDoubleCapDomainFiltered.boundedDomain Z (TopCat.of (SphereLoop n)) D f B
      ∃ e : ∀ q, (small Z (JoinedFilteredCap.rectangleCover X η)).X (k + (p + q)) ⟶
          (chains (TopCat.of E)).X q,
      ∀ q,
        ((JoinedLocalizedCutComparison.familySmallMap u a ha ha1 ρ r i
          (JoinedFilteredCap.rectangleCover X η) (hW i)).f (k + (p + q)) ≫
          SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
            k p φ hfar (NormalizedSelfCut.testedCocycle n p hr T) q (k + (p + q)) rfl =
          e q ≫ (push (SupportedCap.subspaceMap (TopCat.of D) E)).f q ≫
            (push (toCut (tube X) (family u a ha ha1) (fun _ => r) i)).f q) ∧
        (e (q + 1) ≫ (chains (TopCat.of E)).d (q + 1) q =
          (small Z (JoinedFilteredCap.rectangleCover X η)).d
            (k + (p + (q + 1))) (k + (p + q)) ≫ e q) := by
  obtain ⟨η, hη, hηb, hW, hop⟩ := JoinedBoundedCutDomain.exists_closed_domain_operators
    F u a ha ha1 hρ hρr hr hε hb hradius
  refine ⟨η, hη, hηb, hW, ?_⟩
  intro i k p L A φ hφ hfar T hT hshort hA
  obtain ⟨e, he⟩ := hop i k p L A φ hφ hfar T hT hshort hA
  refine ⟨e, ?_⟩
  intro q
  refine ⟨?_, (he q).2⟩
  have hc := JoinedLocalizedCutComparison.domain_agreement u a ha ha1 ρ r i
    (JoinedFilteredCap.rectangleCover X η) (hW i) k p q φ hfar
    (NormalizedSelfCut.testedCocycle n p hr T)
    (e q ≫ (push (SupportedCap.subspaceMap
      (TopCat.of (domain (tube X) (family u a ha ha1) (fun _ => r) i))
      (PartialDoubleCapDomainFiltered.boundedDomain (TopCat.of (Outer X)) (TopCat.of (SphereLoop n))
        (domain (tube X) (family u a ha ha1) (fun _ => r) i)
        (retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i)
        (JoinedFilteredCap.sublevel F (A - L + 3 * ε))))).f q)
    (by simpa only [Category.assoc, JoinedLocalizedCutComparison.tested_pullback,
      testedExtension] using (he q).1)
  simpa only [Category.assoc] using hc

end
end Finsler.JoinedBoundedNativeCap
