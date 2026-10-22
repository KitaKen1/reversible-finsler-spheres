module

public import Finsler.Loop.OriginalFirstHalfAnnularCommonCover
public import Finsler.Topology.PullbackPairCover

/-! One genuine spatial input cover is small for the spatial join
and both time endpoints of the fine common cylinder cover. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfAnnularInputRefinement

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η κ ρ : ℝ)

def endpoints := PullbackPairCover.cover (X := TopCat.of (P × Q))
  (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
  (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
  (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0) (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1)

def cover := CylinderCommonCover.cover (CompactJoinCapLocalization.cover α β κ)
  (endpoints α β R r η κ ρ) (𝟙 (TopCat.of (P × Q)))

theorem cover_open (i) : IsOpen (cover α β R r η κ ρ i) :=
  CylinderCommonCover.cover_open _ _ _ (CompactJoinCapLocalization.cover_open α β κ)
    (PullbackPairCover.isOpen _ _ _ _ (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)
      (OriginalFirstHalfAnnularCommonCover.cover_open α β R r η κ ρ)) i

theorem cover_univ (hη : 0 < η) (hκ : 0 < κ) (hκR : κ < R) (hρr : ρ < r) :
    ⋃ i, cover α β R r η κ ρ i = Set.univ :=
  CylinderCommonCover.cover_univ _ _ _ (CompactJoinCapLocalization.cover_univ α β hκ)
    (PullbackPairCover.covers _ _ _ _ (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr)
      (OriginalFirstHalfAnnularCommonCover.cover_univ α β R r η κ ρ hη hκ hκR hρr))

def toSpatial : small (TopCat.of (P × Q)) (cover α β R r η κ ρ) ⟶
    small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ) := CylinderCommonCover.toSource _ _ _

theorem toSpatial_inclusion : toSpatial α β R r η κ ρ ≫
    inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ) =
      inclusion (TopCat.of (P × Q)) (cover α β R r η κ ρ) := CylinderCommonCover.toSource_inclusion _ _ _

def toEndpoints : small (TopCat.of (P × Q)) (cover α β R r η κ ρ) ⟶
    small (TopCat.of (P × Q)) (endpoints α β R r η κ ρ) :=
  SmallRefinementComparison.refinement (cover α β R r η κ ρ) (endpoints α β R r η κ ρ)
    Prod.snd (fun _ _ hz => hz.2)

theorem toEndpoints_inclusion : toEndpoints α β R r η κ ρ ≫
    inclusion (TopCat.of (P × Q)) (endpoints α β R r η κ ρ) =
      inclusion (TopCat.of (P × Q)) (cover α β R r η κ ρ) :=
  SmallRefinementComparison.refinement_inclusion (cover α β R r η κ ρ) (endpoints α β R r η κ ρ)
    Prod.snd (fun _ _ hz => hz.2)

def zero := toEndpoints α β R r η κ ρ ≫ PullbackPairCover.leftMap (X := TopCat.of (P × Q))
  (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
  (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
  (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0) (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1)

def one := toEndpoints α β R r η κ ρ ≫ PullbackPairCover.rightMap (X := TopCat.of (P × Q))
  (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
  (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ)
  (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0) (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1)

theorem zero_inclusion : zero α β R r η κ ρ ≫
    inclusion (OriginalFirstHalfCupOneCochains.ambient α β) (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ) =
    inclusion (TopCat.of (P × Q)) (cover α β R r η κ ρ) ≫ push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0) := by
  rw [zero, Category.assoc, PullbackPairCover.leftMap_inclusion, ← Category.assoc]
  simpa only [endpoints] using congrArg (fun k => k ≫ push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0))
    (toEndpoints_inclusion α β R r η κ ρ)

theorem one_inclusion : one α β R r η κ ρ ≫
    inclusion (OriginalFirstHalfCupOneCochains.ambient α β) (OriginalFirstHalfAnnularCommonCover.cover α β R r η κ ρ) =
    inclusion (TopCat.of (P × Q)) (cover α β R r η κ ρ) ≫ push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1) := by
  rw [one, Category.assoc, PullbackPairCover.rightMap_inclusion, ← Category.assoc]
  simpa only [endpoints] using congrArg (fun k => k ≫ push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1))
    (toEndpoints_inclusion α β R r η κ ρ)

end
end Finsler.OriginalFirstHalfAnnularInputRefinement
