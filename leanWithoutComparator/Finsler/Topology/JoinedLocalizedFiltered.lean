module

public import Finsler.Topology.JoinedLocalizedCutComparison
public import Finsler.Topology.JoinedFilteredCapClosed

/-! The original localized supported tested output, on the actual
three-family small-chain map, factors through the genuine retained
length sublevel. One scale precedes every cochain and degree, and the
resulting filtered components commute with boundary in all degrees.
No comparison of the original full retractions is asserted here. -/

@[expose] public section
namespace Finsler.JoinedLocalizedFiltered

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem exists_closed_filtered_output {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
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
      ∃ d : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X
          (k + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).X q,
      ∀ q,
        (d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
          (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q =
          (JoinedLocalizedCutComparison.familySmallMap u a ha ha1 ρ r i
            (JoinedFilteredCap.rectangleCover X η) (hW i)).f (k + (p + q)) ≫
          SupportedDoubleCap.localized (parameters n) (exterior n ρ) (neighborhood n r)
            k p φ hfar (NormalizedSelfCut.testedCocycle n p hr T) q (k + (p + q)) rfl ≫
          (push (TopCat.ofHom (retained n hr))).f q) ∧
        (d (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
          (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
            (k + (p + (q + 1))) (k + (p + q)) ≫ d q) := by
  have htwo : 2 * ρ < r := by linarith
  obtain ⟨η₀, hη₀, hη₀b, hrefine⟩ := JoinedRectangleRefinement.exists_scale u a ha ha1 hρ htwo hb
  obtain ⟨η, hη, hηη₀, hop⟩ := JoinedFilteredCapClosed.exists_closed_filtered_operators F u a ha ha1
    hρ hρr hr hε hη₀ hradius
  have hW : ∀ (i : Fin 3) center,
      JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ i ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i := by
    intro i center
    rcases hrefine i center with hf | hn
    · exact Or.inl ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hf)
    · exact Or.inr ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hn)
  refine ⟨η, hη, hηη₀.trans hη₀b, hW, ?_⟩
  intro i k p L A φ hφ hfar T hT hshort hA
  obtain ⟨c, d, hid⟩ := hop i k p L A φ hφ hfar T hT hshort hA
  refine ⟨d, ?_⟩
  intro q
  refine ⟨?_, (hid q).2.2⟩
  rw [(hid q).2.1]
  exact (JoinedLocalizedCutComparison.output_agreement u a ha ha1 ρ r i
    (JoinedFilteredCap.rectangleCover X η) (hW i) hr k p q φ hfar T (c q) (hid q).1).symm

end
end Finsler.JoinedLocalizedFiltered
