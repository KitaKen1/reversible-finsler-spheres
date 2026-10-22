module

public import Finsler.Loop.FirstInputRotationAmbientCap
public import Finsler.Topology.CutDomainTimePrism
public import Finsler.Topology.SmallRetractionComparison

/-! Reorder the actual rotating ambient cylinder so cut time is the
outer interval. Pull back the genuine full cover and annular inner
collar without changing the bounded target. -/

@[expose] public section
namespace Finsler.FirstInputRotationCutCylinder

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationAmbientCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R : ℝ)

abbrev input : TopCat.{0} :=
  TopCat.of (_root_.unitInterval × CompactNearJoinParameters.tube α β R)

abbrev cylinder : TopCat.{0} := TopCat.of (ClosedInterval × input α β R)

def reorderHomeo : (cylinder α β R) ≃ₜ ambient α β R where
  toFun z := (z.2.1, (z.1, z.2.2))
  invFun z := (z.2.1, (z.1, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def reorderIso : cylinder α β R ≅ ambient α β R := TopCat.isoOfHomeo (reorderHomeo α β R)

def reorder : cylinder α β R ⟶ ambient α β R := (reorderIso α β R).hom

def restore : ambient α β R ⟶ cylinder α β R := (reorderIso α β R).inv

theorem reorder_restore : reorder α β R ≫ restore α β R = 𝟙 _ := (reorderIso α β R).hom_inv_id

theorem restore_reorder : restore α β R ≫ reorder α β R = 𝟙 _ := (reorderIso α β R).inv_hom_id

def cover (r η ρ : ℝ) (i : Option (FirstInputRotationCochains.space α β R r)) : Set (cylinder α β R) :=
  reorder α β R ⁻¹' FirstInputRotationAmbientCover.cover α β R r η ρ i

theorem cover_open (r η ρ : ℝ) (i : Option (FirstInputRotationCochains.space α β R r)) :
    IsOpen (cover α β R r η ρ i) :=
  (FirstInputRotationAmbientCover.cover_open α β R r η ρ i).preimage (reorder α β R).hom.continuous

theorem cover_univ (r η : ℝ) (hη : 0 < η) {ρ : ℝ} (hρr : ρ < r) :
    ⋃ i, cover α β R r η ρ i = Set.univ := by
  simp only [cover, ← Set.preimage_iUnion,
    FirstInputRotationAmbientCover.cover_univ α β R r η hη hρr, Set.preimage_univ]

def smallReorder (r η ρ : ℝ) :
    small (cylinder α β R) (cover α β R r η ρ) ⟶
      small (ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ) :=
  SmallRetractionComparison.map (X := cylinder α β R) (Y := ambient α β R)
    (cover α β R r η ρ) (FirstInputRotationAmbientCover.cover α β R r η ρ)
      (reorder α β R) id (fun _ _ hz => hz)

theorem smallReorder_inclusion (r η ρ : ℝ) :
    smallReorder α β R r η ρ ≫ inclusion (ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ) =
      inclusion (cylinder α β R) (cover α β R r η ρ) ≫ push (reorder α β R) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

def thom (hR : R ≤ 1 / 2) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (cylinder α β R) n :=
  cochainPullback (reorder α β R) n (ambientThom α β R hR hn h)

def tested (r : ℝ) (hR : R ≤ 1 / 2) (hr : r < 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (cylinder α β R) p :=
  cochainPullback (reorder α β R) p (FirstInputRotationAmbientCap.ambientTested α β R r hR hr p T)

def collar (δ : ℝ) : Set (cylinder α β R) := {z | distance n (z.1, α z.2.2.val.1) ≤ δ}

theorem thom_inner_zero (hR : R ≤ 1 / 2) (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (SupportedCap.subspaceMap (cylinder α β R) (collar α β R δ)) n
      (thom α β R hR hn h) = 0 := by
  have he : thom α β R hR hn h =
      cochainPullback (reorder α β R ≫ ambientEvaluation α β R hR) n (AnnularSelfCut.cocycle n hn h) :=
    (pullback_comp (reorder α β R) (ambientEvaluation α β R hR) n (AnnularSelfCut.cocycle n hn h)).symm
  rw [he]
  apply pullback_support (reorder α β R ≫ ambientEvaluation α β R hR) (collar α β R δ)
    {z | distance n z ≤ δ} _ n (AnnularSelfCut.cocycle n hn h)
    (AnnularSelfCut.cocycle_small_zero n hn h)
  intro z hz
  change distance n (ambientEvaluation α β R hR (reorder α β R z)) ≤ δ
  rw [evaluation_gap]
  exact hz

theorem collar_zero {δ : ℝ} (hδ : 0 ≤ δ) (x : input α β R) :
    ((0 : ClosedInterval), x) ∈ collar α β R δ := by
  change distance n (0, α x.2.val.1) ≤ δ
  calc
    _ = 0 := UniformSelfCutCollar.distance_zero α x.2.val.1
    _ ≤ δ := hδ

theorem collar_one {δ : ℝ} (hδ : 0 ≤ δ) (x : input α β R) :
    ((1 : ClosedInterval), x) ∈ collar α β R δ := by
  change distance n (1, α x.2.val.1) ≤ δ
  calc
    _ = 0 := UniformSelfCutCollar.distance_one α x.2.val.1
    _ ≤ δ := hδ

end
end Finsler.FirstInputRotationCutCylinder
