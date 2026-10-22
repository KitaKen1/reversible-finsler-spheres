module

public import Finsler.Topology.JoinedRefinedComparisons
public import Finsler.Topology.JoinedHalfTrim

/-! Simultaneously select a genuine common interior time and one common
rectangle refinement before every tested degree and cocycle. The actual
triangle and both actual double-prism comparisons then live in the same
retained-length sublevel and satisfy their explicit filtered boundaries.
Matching the distinct refined endpoint faces remains separate. -/

@[expose] public section
namespace Finsler.JoinedRefinedPackage

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength
open Finsler.JoinedComparisonAdequacy Finsler.JoinedComparisonSource Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

theorem exists_common_comparisons {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (u : C(X, H1JoinContinuity.composable (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      ∃ η > 0, η ≤ b ∧
      ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      ∃ v : Fin 3 → ∀ q, (chains (TopCat.of (Outer X))).X ((m + p) + q + 1) ⟶
        (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).X q,
      (∀ (i : Fin 3) q,
        (v i q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q =
          (TauCeti.singularSmallApprox (X := TopCat.of (Outer X)) coeff
            (JoinedFilteredCap.rectangleCover X η)).f ((m + p) + q + 1) ≫
          (push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i)).f ((m + p) + q + 1) ≫
          AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q) ∧
        (v i (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
          (chains (TopCat.of (Outer X))).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ v i q)) ∧
      (∀ q,
        ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫
          triangleSource (TopCat.of X) ((m + p) + q) ≫ v 0 (q + 1)) ≫
          (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
        (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
          (CappedTimeSplit.component (((TopCat.of X) ◁ IntervalTriangle.secondMap) ≫ triangleLift (TopCat.of X)) (m + p) (v 0) q +
          CappedTimeSplit.component (triangleLift (TopCat.of X)) (m + p) (v 0) q +
          CappedTimeSplit.component (((TopCat.of X) ◁ IntervalTriangle.firstMap) ≫ triangleLift (TopCat.of X)) (m + p) (v 0) q)) ∧
      (∀ (i : Fin 2) q,
        ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫ AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q)) ≫
          (((push (planeFace (TopCat.of X) 0)).f ((m + p) + q + 1) -
            (push (planeFace (TopCat.of X) 1)).f ((m + p) + q + 1)) ≫ v i.succ q) =
        ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫
          squareSource (TopCat.of X) ((m + p) + q) ≫ v i.succ (q + 1)) ≫
          (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q) := by
  classical
  obtain ⟨a, ha, ha1, hf₀, hf₁, hs₀, hs₁⟩ := JoinedHalfTrim.family_slide_sides_small u h.1
  obtain ⟨η, hη, hηb, hop⟩ := JoinedRefinedCut.exists_closed_filtered_components m F u a ha.le ha1.le
    h hρr hr hε hb hradius
  refine ⟨a, ha, ha1, η, hη, hηb, ?_⟩
  intro p L A T hT hshort hA
  choose v hv using (fun i : Fin 3 => hop i p L A T hT hshort hA)
  refine ⟨v, hv, ?_, ?_⟩
  · intro q
    exact triangle_boundary (TopCat.of X) (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))
      (m + p) (v 0) (fun q => (hv 0 q).2) q
  · intro i q
    apply square_boundary m p h (show ρ < r by linarith [h.1.trans h.2.2]) hr T hT
      (TopCat.of X) (JoinedFilteredCap.rectangleCover X η)
      (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i.succ)
      (JoinedFilteredCap.sublevel F (A - L + 3 * ε)) (v i.succ)
      (fun q => (hv i.succ q).1) (fun q => (hv i.succ q).2) ?_ ?_ q
    · fin_cases i
      · exact hf₀
      · exact hs₀
    · fin_cases i
      · exact hf₁
      · exact hs₁

end
end Finsler.JoinedRefinedPackage
