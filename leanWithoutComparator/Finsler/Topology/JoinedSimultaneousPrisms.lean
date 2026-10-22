module

public import Finsler.Topology.JoinedCommonInputRefinement

/-! Both actual half-time/square-start pairs have bounded naturality
correction chains on the same genuine base input cover. The target is
the given actual loop sublevel, and only genuine base cycles are used. -/

@[expose] public section
namespace Finsler.JoinedSimultaneousPrisms

open CategoryTheory CategoryTheory.Limits AlgebraicTopology TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.JoinedComparisonAdequacy
open Finsler.JoinedCommonInputRefinement

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

theorem rectangles_open (X : Type) [PseudoMetricSpace X] (η : ℝ) (center : Outer X) :
    IsOpen (JoinedFilteredCap.rectangleCover X η center) :=
  (PairDistanceCover.cover_open id continuous_id η center.1).prod
    (PairDistanceCover.cover_open id continuous_id η center.2)

theorem rectangles_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ center, JoinedFilteredCap.rectangleCover X η center = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  refine Set.mem_iUnion.mpr ⟨z, ?_, ?_⟩
  · change dist z.1 z.1 < η
    simpa only [dist_self] using hη
  · change dist z.2 z.2 < η
    simpa only [dist_self] using hη

def retraction (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    chains (TopCat.of (Outer X)) ⟶ small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) :=
  smallSingularRetraction (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η)
    (rectangles_open X η) (rectangles_univ X η hη)

def comparison (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) (i : Fin 5) :
    Homotopy
      (push (maps (TopCat.of X) i) ≫ retraction X η hη)
      (smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff (cover X η)
        (cover_open X η) (cover_univ X η hη) ≫
        FinitePullbackCover.map (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
          (JoinedFilteredCap.rectangleCover X η) (maps (TopCat.of X)) i) :=
  SmallRetractionComparison.comparison
    (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
    (cover X η) (JoinedFilteredCap.rectangleCover X η)
    (cover_open X η) (cover_univ X η hη) (rectangles_open X η) (rectangles_univ X η hη)
    (maps (TopCat.of X) i) (fun center => center i) (FinitePullbackCover.maps _ _ i)

def sourceCycle (X : Type) [PseudoMetricSpace X] (η : ℝ) (j : ℕ) :
    (small (TopCat.of X) (inputCover X η)).cycles j ⟶
      (chains (TopCat.of (ClosedInterval × X))).X (j + 1) :=
  (small (TopCat.of X) (inputCover X η)).iCycles j ≫
    (inclusion (TopCat.of X) (inputCover X η)).f j ≫ AnnularTimeTrim.prism (TopCat.of X) j

theorem paired_boundaries {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (η : ℝ) (hη : 0 < η) (B : Set (SphereLoop n)) (k : ℕ)
    (c : ∀ q, (chains (Finsler.SelfCutThomCocycle.parameters n)).X (k + q + 1) ⟶
      (chains (TopCat.of (SphereLoop n))).X q)
    (v : Fin 3 → ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X (k + q + 1) ⟶
      (chains (TopCat.of B)).X q)
    (hv : ∀ i q, v i q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) B)).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f (k + q + 1) ≫
        (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f (k + q + 1) ≫ c q)
    (hc : ∀ i q, v i (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d (k + q + 2) (k + q + 1) ≫ v i q) :
    ∃ P : Fin 2 → ∀ q, (small (TopCat.of X) (inputCover X η)).cycles (k + q) ⟶
        (chains (TopCat.of B)).X (q + 1),
      ∀ (i : Fin 2) q,
      sourceCycle X η (k + q) ≫
        (((push (maps (TopCat.of X) ⟨i.val + 1, by omega⟩)).f (k + q + 1) ≫
          (retraction X η hη).f (k + q + 1) ≫ v 0 q) -
         ((push (maps (TopCat.of X) 3)).f (k + q + 1) ≫
          (retraction X η hη).f (k + q + 1) ≫ v i.succ q)) =
        P i q ≫ (chains (TopCat.of B)).d (q + 1) q := by
  let P : Fin 2 → ∀ q, (small (TopCat.of X) (inputCover X η)).cycles (k + q) ⟶
      (chains (TopCat.of B)).X (q + 1) := fun i q =>
    sourceCycle X η (k + q) ≫
      ((comparison X η hη ⟨i.val + 1, by omega⟩).hom (k + q + 1) (k + q + 2) ≫ v 0 (q + 1) -
       (comparison X η hη 3).hom (k + q + 1) (k + q + 2) ≫ v i.succ (q + 1))
  refine ⟨P, ?_⟩
  intro i q
  have he (q : ℕ) := half_outputs_eq u a ha ha1 η B (k + q + 1) q (c q)
    (fun j => v j q) (fun j => hv j q) i
  simpa only [P, sourceCycle, inputCover, comparison, retraction, HomologicalComplex.comp_f, Category.assoc] using
    PairedPrismComparison.paired_boundary (TopCat.of X) (cover X η) (TopCat.of (Outer X))
      (JoinedFilteredCap.rectangleCover X η) (cover_open X η) (cover_univ X η hη)
      (rectangles_open X η) (rectangles_univ X η hη)
      (maps (TopCat.of X) ⟨i.val + 1, by omega⟩) (maps (TopCat.of X) 3)
      (fun center => center ⟨i.val + 1, by omega⟩) (fun center => center 3)
      (FinitePullbackCover.maps _ _ _) (FinitePullbackCover.maps _ _ _)
      (chains (TopCat.of B)) k (v 0) (v i.succ) (hc 0) (hc i.succ) he q

end
end Finsler.JoinedSimultaneousPrisms
