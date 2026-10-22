module

public import Finsler.Loop.FirstInputRotationFilteredCap
public import Finsler.Topology.SmallRetractionComparison

/-! Actual small-chain endpoint models for the bounded rotating cap.
The endpoint maps use genuine pullback covers and retractions; their
homology comparison stays inside the identical retained sublevel. -/

@[expose] public section
namespace Finsler.FirstInputRotationEndpoints

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCochains Finsler.FirstInputRotationFilteredCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)

def stage (s : _root_.unitInterval) :
    TopCat.of (FirstInputRotatingCut.source α β R r) ⟶ space α β R r :=
  TopCat.ofHom ⟨fun z => (s, z), continuous_const.prodMk continuous_id⟩

def homotopy : TopCat.Homotopy (stage α β R r 0) (stage α β R r 1) where
  toFun z := (z.1, z.2)
  continuous_toFun := continuous_fst.prodMk continuous_snd
  map_zero_left _ := rfl
  map_one_left _ := rfl

def cover (η : ℝ) (s : _root_.unitInterval) (center : space α β R r) :
    Set (FirstInputRotatingCut.source α β R r) :=
  stage α β R r s ⁻¹' rectangle α β R r η center

theorem cover_open (η : ℝ) (s : _root_.unitInterval) (center : space α β R r) :
    IsOpen (cover α β R r η s center) :=
  (rectangle_open α β R r η center).preimage (stage α β R r s).hom.continuous

theorem cover_univ {η : ℝ} (hη : 0 < η) (s : _root_.unitInterval) :
    ⋃ center, cover α β R r η s center = Set.univ := by
  simp only [cover, ← Set.preimage_iUnion, rectangle_univ α β R r hη, Set.preimage_univ]

def smallStage (η : ℝ) (s : _root_.unitInterval) :
    small (TopCat.of (FirstInputRotatingCut.source α β R r)) (cover α β R r η s) ⟶
      small (space α β R r) (rectangle α β R r η) :=
  SmallRetractionComparison.map (cover α β R r η s) (rectangle α β R r η)
    (stage α β R r s) id (fun _ _ hz => hz)

theorem smallStage_inclusion (η : ℝ) (s : _root_.unitInterval) :
    smallStage α β R r η s ≫ inclusion (space α β R r) (rectangle α β R r η) =
      inclusion (TopCat.of (FirstInputRotatingCut.source α β R r)) (cover α β R r η s) ≫
        push (stage α β R r s) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

variable (hR : R ≤ 1 / 2) (hr : r < 1) (hn : 1 ≤ n) {δ ρ : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (F : ReversibleMetric n) (B η : ℝ) (hη : 0 < η)
  (hgood : Adequate α β R r hR hr hn h p T F B η)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)

def endpoint (s : _root_.unitInterval) :
    DegreeLoweringHomology.Map (chains (TopCat.of (FirstInputRotatingCut.source α β R r)))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (n + p) :=
  ((retainedOperation α β R r hR hr hn h p T F B η hgood hT).pre
    (smallStage α β R r η s)).pre
      (TauCeti.smallSingularRetraction (X := TopCat.of (FirstInputRotatingCut.source α β R r)) coeff (cover α β R r η s)
        (cover_open α β R r η s) (cover_univ α β R r hη s))

theorem endpoint_homology (s : _root_.unitInterval) (q : ℕ) :
    (endpoint α β R r hR hr hn h p T F B η hη hgood hT s).homology q =
      HomologicalComplex.homologyMap (push (stage α β R r s)) ((n + p) + q) ≫
        ((retainedOperation α β R r hR hr hn h p T F B η hgood hT).pre
          (TauCeti.smallSingularRetraction (X := space α β R r) coeff (rectangle α β R r η)
            (rectangle_open α β R r η) (rectangle_univ α β R r hη))).homology q := by
  have he := SmallRetractionHomology.homology_naturality
    (X := TopCat.of (FirstInputRotatingCut.source α β R r)) (Y := space α β R r)
    (cover α β R r η s) (rectangle α β R r η)
    (cover_open α β R r η s) (cover_univ α β R r hη s)
    (rectangle_open α β R r η) (rectangle_univ α β R r hη)
    (stage α β R r s) id (fun _ _ hz => hz) ((n + p) + q)
  dsimp only [endpoint]
  rw [DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology,
    DegreeLoweringHomology.Map.pre_homology]
  simpa only [smallStage, SmallRetractionComparison.map, push, Category.assoc] using
    congrArg (fun g => g ≫ (retainedOperation α β R r hR hr hn h p T F B η hgood hT).homology q) he

theorem homology_eq (q : ℕ) :
    (endpoint α β R r hR hr hn h p T F B η hη hgood hT 0).homology q =
      (endpoint α β R r hR hr hn h p T F B η hη hgood hT 1).homology q := by
  rw [endpoint_homology, endpoint_homology]
  have he := ((homotopy α β R r).toSSet.chainComplexMap coeff).homologyMap_eq ((n + p) + q)
  exact congrArg (fun g => g ≫
    ((retainedOperation α β R r hR hr hn h p T F B η hgood hT).pre
      (TauCeti.smallSingularRetraction (X := space α β R r) coeff (rectangle α β R r η)
        (rectangle_open α β R r η) (rectangle_univ α β R r hη))).homology q) he

end
end Finsler.FirstInputRotationEndpoints
