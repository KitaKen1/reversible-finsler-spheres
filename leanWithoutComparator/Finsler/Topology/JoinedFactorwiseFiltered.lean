module

public import Finsler.Topology.JoinedAnnularFiltered
public import Finsler.Topology.FactorwiseSubdivisionComparison

/-! Use the same actual factorwise subdivisions of the two-time plane
and the compact loop parameter space for all three original annular
families. Their original cut outputs have closed filtered components.
Applications to the specified triangle and double prisms are separate. -/

@[expose] public section
namespace Finsler.JoinedFactorwiseFiltered

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def subdivision (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    chains (TopCat.of (ClosedInterval × ClosedInterval)) ⊗ chains (TopCat.of X) ⟶
      small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) :=
  FactorwiseSubdivisionComparison.factorwise
    (X := TopCat.of (ClosedInterval × ClosedInterval)) (Y := TopCat.of X)
    (PairDistanceCover.cover (id : ClosedInterval × ClosedInterval → ClosedInterval × ClosedInterval) η)
    (PairDistanceCover.cover (id : X → X) η)
    (PairDistanceCover.cover_open id continuous_id η) (PairDistanceCover.cover_univ id hη)
    (PairDistanceCover.cover_open id continuous_id η) (PairDistanceCover.cover_univ id hη)

theorem subdivision_inclusion (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    subdivision X η hη ≫ inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) =
      (TauCeti.singularSmallApprox (X := TopCat.of (ClosedInterval × ClosedInterval)) coeff
        (PairDistanceCover.cover (id : ClosedInterval × ClosedInterval → ClosedInterval × ClosedInterval) η) ⊗ₘ
      TauCeti.singularSmallApprox (X := TopCat.of X) coeff (PairDistanceCover.cover (id : X → X) η)) ≫
      SmallRectangleCross.ambient (TopCat.of (ClosedInterval × ClosedInterval)) (TopCat.of X) := by
  have hc : SmallRectangleCross.cross
      (X := TopCat.of (ClosedInterval × ClosedInterval)) (Y := TopCat.of X)
      (PairDistanceCover.cover (id : ClosedInterval × ClosedInterval → ClosedInterval × ClosedInterval) η)
      (PairDistanceCover.cover (id : X → X) η) ≫
      inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) =
      (inclusion (TopCat.of (ClosedInterval × ClosedInterval))
        (PairDistanceCover.cover (id : ClosedInterval × ClosedInterval → ClosedInterval × ClosedInterval) η) ⊗ₘ
      inclusion (TopCat.of X) (PairDistanceCover.cover (id : X → X) η)) ≫
      SmallRectangleCross.ambient (TopCat.of (ClosedInterval × ClosedInterval)) (TopCat.of X) :=
    SmallRectangleCross.cross_inclusion _ _
  unfold subdivision FactorwiseSubdivisionComparison.factorwise
  rw [Category.assoc, hc, ← Category.assoc,
    tensorHom_comp_tensorHom, TauCeti.smallSingularRetraction_comp_ι,
    TauCeti.smallSingularRetraction_comp_ι]

theorem exists_closed_filtered_output {X : Type} [PseudoMetricSpace X] [CompactSpace X]
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
      ∃ d : ∀ q, (chains (TopCat.of (ClosedInterval × ClosedInterval)) ⊗ chains (TopCat.of X)).X
          ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).X q,
      ∀ q,
        (d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q =
          (subdivision X η hη).f ((m + 1) + (p + q)) ≫
          (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f ((m + 1) + (p + q)) ≫
          (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
          AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q) ∧
        (d (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
          (chains (TopCat.of (ClosedInterval × ClosedInterval)) ⊗ chains (TopCat.of X)).d
            ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d q) := by
  obtain ⟨η, hη, hηb, hop⟩ := JoinedAnnularFiltered.exists_closed_filtered_output m F u a ha ha1
    h hρr hr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro i p L A T hT hshort hA
  obtain ⟨d, hid⟩ := hop i p L A T hT hshort hA
  refine ⟨fun q => (subdivision X η hη).f ((m + 1) + (p + q)) ≫ d q, ?_⟩
  intro q
  constructor
  · rw [Category.assoc, (hid q).1]
  · rw [Category.assoc, (hid q).2, ← Category.assoc, (subdivision X η hη).comm, Category.assoc]

end
end Finsler.JoinedFactorwiseFiltered
