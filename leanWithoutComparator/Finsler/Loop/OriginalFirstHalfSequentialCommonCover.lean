module

public import Finsler.Loop.OriginalFirstHalfJoinTimeCover
public import Finsler.Loop.CylinderCommonCover

/-! Actual common original cylinder cover for the sequential
localized join/gamma cap and the already constructed cup-order cap. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfSequentialCommonCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η κ ρ : ℝ)

def cover := CylinderCommonCover.cover (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ)
  (OriginalFirstHalfJointCover.cover α β R r η κ ρ) (𝟙 (ambient α β))

theorem cover_open (i) : IsOpen (cover α β R r η κ ρ i) :=
  CylinderCommonCover.cover_open _ _ _ (OriginalFirstHalfJoinTimeCover.cover_open α β R r η ρ κ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ) i

theorem cover_univ (hη : 0 < η) (hκR : κ < R) (hρr : ρ < r) :
    ⋃ i, cover α β R r η κ ρ i = Set.univ :=
  CylinderCommonCover.cover_univ _ _ _
    (OriginalFirstHalfJoinTimeCover.cover_univ α β R r η ρ hη hκR hρr)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)

def toJoin : small (ambient α β) (cover α β R r η κ ρ) ⟶
    small (ambient α β) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) :=
  CylinderCommonCover.toSource _ _ _

def toCup : small (ambient α β) (cover α β R r η κ ρ) ⟶
    small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ) :=
  SmallRefinementComparison.refinement (cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ) Prod.snd (fun _ _ hz => hz.2)

theorem toJoin_inclusion : toJoin α β R r η κ ρ ≫
    inclusion (ambient α β) (OriginalFirstHalfJoinTimeCover.cover α β R r η ρ κ) =
      inclusion (ambient α β) (cover α β R r η κ ρ) :=
  CylinderCommonCover.toSource_inclusion _ _ _

theorem toCup_inclusion : toCup α β R r η κ ρ ≫
    inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ) =
      inclusion (ambient α β) (cover α β R r η κ ρ) :=
  SmallRefinementComparison.refinement_inclusion (cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ) Prod.snd (fun _ _ hz => hz.2)

end
end Finsler.OriginalFirstHalfSequentialCommonCover
