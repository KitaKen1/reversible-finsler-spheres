module

public import Finsler.Loop.OriginalFirstHalfAnnularJoinCap
public import Finsler.Loop.OriginalFirstHalfLocalizedJoinCap
public import Finsler.Loop.CylinderCommonCover

/-! A real common original cylinder cover for the whole-interval
coarse join cap and the actual sequential gamma carrier. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfAnnularCommonCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η κ ρ : ℝ)

def cover := CylinderCommonCover.cover (OriginalFirstHalfAnnularJoinCover.cover α β κ)
  (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) (𝟙 (ambient α β))

theorem cover_open (i) : IsOpen (cover α β R r η κ ρ i) :=
  CylinderCommonCover.cover_open _ _ _ (OriginalFirstHalfAnnularJoinCover.cover_open α β κ)
    (OriginalFirstHalfJoinTimeCover.cover_open α β R r η ρ κ) i

theorem cover_univ (hη : 0 < η) (hκ : 0 < κ) (hκR : κ < R) (hρr : ρ < r) :
    ⋃ i, cover α β R r η κ ρ i = Set.univ :=
  CylinderCommonCover.cover_univ _ _ _ (OriginalFirstHalfAnnularJoinCover.cover_univ α β κ hκ)
    (OriginalFirstHalfJoinTimeCover.cover_univ α β R r η ρ hη hκR hρr)

def toCoarse : small (ambient α β) (cover α β R r η κ ρ) ⟶
    small (ambient α β) (OriginalFirstHalfAnnularJoinCover.cover α β κ) :=
  CylinderCommonCover.toSource _ _ _

def toSequential : small (ambient α β) (cover α β R r η κ ρ) ⟶
    small (ambient α β) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) :=
  SmallRefinementComparison.refinement (cover α β R r η κ ρ)
    (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) Prod.snd (fun _ _ hz => hz.2)

theorem toCoarse_inclusion : toCoarse α β R r η κ ρ ≫
    inclusion (ambient α β) (OriginalFirstHalfAnnularJoinCover.cover α β κ) =
      inclusion (ambient α β) (cover α β R r η κ ρ) :=
  CylinderCommonCover.toSource_inclusion _ _ _

theorem toSequential_inclusion : toSequential α β R r η κ ρ ≫
    inclusion (ambient α β) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) =
      inclusion (ambient α β) (cover α β R r η κ ρ) :=
  SmallRefinementComparison.refinement_inclusion (cover α β R r η κ ρ)
    (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) Prod.snd (fun _ _ hz => hz.2)

theorem first_cap_source (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (q : ℕ) :
    (toCoarse α β R r η κ ρ).f ((m + 1) + q) ≫
      (OriginalFirstHalfAnnularJoinCap.native α β R hκ hκR).component q =
    (toSequential α β R r η κ ρ).f ((m + 1) + q) ≫
      (OriginalFirstHalfLocalizedJoinCap.operation α β R r η ρ hκ).component q ≫
        (inclusion (OriginalFirstHalfZeroCover.space α β R) (OriginalFirstHalfZeroCover.cover α β R r η ρ)).f q := by
  haveI := OriginalFirstHalfAnnularJoinCover.nearSource_mono α β R q
  apply (cancel_mono ((push (nearSource α β R)).f q)).mp
  simp only [Category.assoc]
  rw [OriginalFirstHalfAnnularJoinCap.source,
    OriginalFirstHalfLocalizedJoinCap.component_source α β R r η ρ hκ q]
  simp only [← Category.assoc, ← HomologicalComplex.comp_f, toCoarse_inclusion]
  rw [toSequential_inclusion α β R r η κ ρ]

end
end Finsler.OriginalFirstHalfAnnularCommonCover
