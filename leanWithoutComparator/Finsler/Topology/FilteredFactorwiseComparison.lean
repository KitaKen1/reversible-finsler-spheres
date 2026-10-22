module

public import Finsler.Topology.JoinedRefinedCut
public import Finsler.Topology.JoinedFactorwiseFiltered
public import Finsler.Topology.TimePrismComparison

/-! The actual product/factorwise comparison already takes values in
the genuine small-chain complex. Postcompose it with the constructed
closed filtered cap to obtain a comparison entirely in the retained
length sublevel. No additional ambient prism carrier assumption is used. -/

@[expose] public section
namespace Finsler.FilteredFactorwiseComparison

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem cap_boundary {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f g : C ⟶ D} (H : Homotopy f g) (k p : ℕ)
    (u : ∀ q, D.X (k + (p + q)) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      D.d (k + (p + (q + 1))) (k + (p + q)) ≫ u q) (q : ℕ) :
    C.iCycles (k + (p + q)) ≫ ((f.f (k + (p + q)) - g.f (k + (p + q))) ≫ u q) =
      (C.iCycles (k + (p + q)) ≫ H.hom (k + (p + q)) (k + (p + q) + 1) ≫ u (q + 1)) ≫ E.d (q + 1) q := by
  have hc := TimePrismComparison.cycles_prism_boundary H (k + (p + q))
  have hu' : u (q + 1) ≫ E.d (q + 1) q = D.d (k + (p + q) + 1) (k + (p + q)) ≫ u q := hu q
  calc
    _ = (((C.iCycles (k + (p + q)) ≫ H.hom (k + (p + q)) (k + (p + q) + 1)) ≫
        D.d (k + (p + q) + 1) (k + (p + q))) ≫ u q) := by
      rw [hc, Category.assoc]
    _ = _ := by
      simp only [Category.assoc]
      rw [← hu']

def comparison (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    Homotopy (SmallRectangleCross.ambient (TopCat.of (ClosedInterval × ClosedInterval)) (TopCat.of X) ≫
      JoinedRefinedCut.retraction X η hη) (JoinedFactorwiseFiltered.subdivision X η hη) :=
  FactorwiseSubdivisionComparison.comparison
    (X := TopCat.of (ClosedInterval × ClosedInterval)) (Y := TopCat.of X)
    (PairDistanceCover.cover (id : ClosedInterval × ClosedInterval → ClosedInterval × ClosedInterval) η)
    (PairDistanceCover.cover (id : X → X) η)
    (PairDistanceCover.cover_open id continuous_id η) (PairDistanceCover.cover_univ id hη)
    (PairDistanceCover.cover_open id continuous_id η) (PairDistanceCover.cover_univ id hη)

theorem exists_filtered_comparison {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (u : C(X, H1JoinContinuity.composable (m + 1)))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η, ∃ hη : 0 < η, η ≤ b ∧
      ∀ (i : Fin 3) (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      ∃ d : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X
          ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).X q,
      (∀ q,
        (d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q =
          (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f ((m + 1) + (p + q)) ≫
          (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
          AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q) ∧
        (d (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
          (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
            ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d q)) ∧
      (∀ q,
        (chains (TopCat.of (ClosedInterval × ClosedInterval)) ⊗ chains (TopCat.of X)).iCycles ((m + 1) + (p + q)) ≫
          (((SmallRectangleCross.ambient (TopCat.of (ClosedInterval × ClosedInterval)) (TopCat.of X) ≫
            JoinedRefinedCut.retraction X η hη).f ((m + 1) + (p + q)) -
            (JoinedFactorwiseFiltered.subdivision X η hη).f ((m + 1) + (p + q))) ≫ d q) =
        ((chains (TopCat.of (ClosedInterval × ClosedInterval)) ⊗ chains (TopCat.of X)).iCycles ((m + 1) + (p + q)) ≫
          (comparison X η hη).hom ((m + 1) + (p + q)) ((m + 1) + (p + q) + 1) ≫ d (q + 1)) ≫
          (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q) := by
  obtain ⟨η, hη, hηb, hop⟩ := JoinedAnnularFiltered.exists_closed_filtered_output m F u a ha ha1
    h hρr hr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro i p L A T hT hshort hA
  obtain ⟨d, hid⟩ := hop i p L A T hT hshort hA
  refine ⟨d, hid, ?_⟩
  intro q
  exact cap_boundary (comparison X η hη) (m + 1) p d (fun q => (hid q).2) q

end
end Finsler.FilteredFactorwiseComparison
