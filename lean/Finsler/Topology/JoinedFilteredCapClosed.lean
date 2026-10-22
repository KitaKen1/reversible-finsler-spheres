module

public import Finsler.Topology.JoinedCochainBoundary

/-! Actual linear retained-length filtered successive caps commute with
boundary in every output degree. One common scale is chosen before all
cochain degrees and representatives, using only local closure for the
tested zero extension. Original supported-cut comparison remains separate. -/

@[expose] public section
namespace Finsler.JoinedFilteredCapClosed

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

theorem exists_closed_filtered_operators {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∀ (i : Fin 3) (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0)
      (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      ∃ (c : ∀ q, (small (TopCat.of (Outer X))
          (JoinedFilteredCap.rectangleCover X η)).X
            (k + (p + q)) ⟶ (chains (TopCat.of (domain (tube X) (family u a ha ha1) (fun _ => r) i))).X q)
        (d : ∀ q, (small (TopCat.of (Outer X))
          (JoinedFilteredCap.rectangleCover X η)).X
            (k + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).X q),
      ∀ q,
        (c q ≫ (push (SupportedCap.subspaceMap (TopCat.of (Outer X))
          (domain (tube X) (family u a ha ha1) (fun _ => r) i))).f q =
          (inclusion (TopCat.of (Outer X))
            (JoinedFilteredCap.rectangleCover X η)).f
              (k + (p + q)) ≫ PartialDoubleCap.cap (TopCat.of (Outer X)) k p q
                (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
                (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T)) ∧
        (d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q =
          c q ≫ (push (retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i)).f q) ∧
        (d (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
          (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
            (k + (p + (q + 1))) (k + (p + q)) ≫ d q) := by
  have htwo : 2 * ρ < r := by linarith
  obtain ⟨η₀, hη₀, hη₀b, hrefine⟩ := JoinedRectangleRefinement.exists_scale u a ha ha1 hρ htwo hb
  obtain ⟨η, hη, hηη₀, hop⟩ := JoinedFilteredCap.exists_filtered_operators F u a ha ha1
    hρ hρr hr hε hη₀ hradius
  refine ⟨η, hη, hηη₀.trans hη₀b, ?_⟩
  intro i k p L A φ hφ hfar T hT hshort hA
  obtain ⟨c, d, hid⟩ := hop i k p L A φ hfar T hshort hA
  have hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ i ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i := by
    intro center
    rcases hrefine i center with hf | hn
    · exact Or.inl ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hf)
    · exact Or.inr ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hn)
  have hcap := JoinedCochainBoundary.boundary u a ha ha1 η ρ r hr i hW k p φ hφ hfar T hT
  let D := domain (tube X) (family u a ha ha1) (fun _ => r) i
  let f := retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i
  have hccomm (q : ℕ) : c (q + 1) ≫ (chains (TopCat.of D)).d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
        (k + (p + (q + 1))) (k + (p + q)) ≫ c q := by
    haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (Outer X)) D)).f q) :=
      SupportedCap.subspacePush_mono (TopCat.of (Outer X)) D q
    apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (Outer X)) D)).f q)).mp
    rw [Category.assoc, ← (push (SupportedCap.subspaceMap (TopCat.of (Outer X)) D)).comm,
      ← Category.assoc, (hid (q + 1)).1]
    simp only [Category.assoc]
    rw [(hid q).1]
    simpa only [Category.assoc] using hcap q
  refine ⟨c, d, ?_⟩
  intro q
  refine ⟨(hid q).1, (hid q).2, ?_⟩
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
      (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q) := SupportedCap.subspacePush_mono (TopCat.of (SphereLoop n)) (JoinedFilteredCap.sublevel F (A - L + 3 * ε)) q
  apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
    (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q)).mp
  rw [Category.assoc, ← (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
    (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).comm, ← Category.assoc, (hid (q + 1)).2,
    Category.assoc, (push f).comm, ← Category.assoc, hccomm q]
  simp only [Category.assoc]
  rw [(hid q).2]

end
end Finsler.JoinedFilteredCapClosed
