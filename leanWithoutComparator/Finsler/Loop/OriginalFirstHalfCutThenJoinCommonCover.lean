module

public import Finsler.Loop.OriginalFirstHalfCutGammaJoinCover
public import Finsler.Loop.CylinderCommonCover

/-! Actual common cylinder refinement for the genuine cut-then-join
sequential cap and the established original cut-first cup cap. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutThenJoinCommonCover

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η κ ρ : ℝ) (hr : r < 1)

def cover := CylinderCommonCover.cover (OriginalFirstHalfCutGammaJoinCover.cover α β r hr κ ρ)
  (OriginalFirstHalfJointCover.cover α β R r η κ ρ) (𝟙 (ambient α β))

theorem cover_open (i) : IsOpen (cover α β R r η κ ρ hr i) :=
  CylinderCommonCover.cover_open _ _ _ (OriginalFirstHalfCutGammaJoinCover.cover_open α β r hr κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ) i

theorem cover_univ (hη : 0 < η) (hκ : 0 < κ) (hκR : κ < R) (hρr : ρ < r) :
    ⋃ i, cover α β R r η κ ρ hr i = Set.univ :=
  CylinderCommonCover.cover_univ _ _ _ (OriginalFirstHalfCutGammaJoinCover.cover_univ α β r hr κ hκ hρr)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)

def toCut : small (ambient α β) (cover α β R r η κ ρ hr) ⟶
    small (ambient α β) (OriginalFirstHalfCutGammaJoinCover.cover α β r hr κ ρ) :=
  CylinderCommonCover.toSource _ _ _

def toCup : small (ambient α β) (cover α β R r η κ ρ hr) ⟶
    small (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ) :=
  SmallRefinementComparison.refinement (cover α β R r η κ ρ hr)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ) Prod.snd (fun _ _ hz => hz.2)

theorem toCut_inclusion : toCut α β R r η κ ρ hr ≫
    inclusion (ambient α β) (OriginalFirstHalfCutGammaJoinCover.cover α β r hr κ ρ) =
      inclusion (ambient α β) (cover α β R r η κ ρ hr) := CylinderCommonCover.toSource_inclusion _ _ _

theorem toCup_inclusion : toCup α β R r η κ ρ hr ≫
    inclusion (ambient α β) (OriginalFirstHalfJointCover.cover α β R r η κ ρ) =
      inclusion (ambient α β) (cover α β R r η κ ρ hr) :=
  SmallRefinementComparison.refinement_inclusion (cover α β R r η κ ρ hr)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ) Prod.snd (fun _ _ hz => hz.2)

end
end Finsler.OriginalFirstHalfCutThenJoinCommonCover
