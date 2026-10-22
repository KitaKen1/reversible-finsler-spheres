module

public import Finsler.Topology.SmallRefinementComparison
public import Finsler.Topology.SmallRetractionComparison

/-! One genuine source cover refines a given source cover and the
pullback of a second cover. Both small-chain maps and their exact
inclusion squares are constructed before any cochain is chosen. -/

@[expose] public section
namespace Finsler.CylinderCommonCover

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y) (f : X ⟶ Y)

def cover : ι × κ → Set X := fun i => U i.1 ∩ f ⁻¹' V i.2

theorem cover_open (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j)) (i : ι × κ) :
    IsOpen (cover U V f i) :=
  (hU i.1).inter ((hV i.2).preimage f.hom.continuous)

theorem cover_univ (hU : ⋃ i, U i = Set.univ) (hV : ⋃ j, V j = Set.univ) :
    ⋃ i, cover U V f i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.symm ▸ Set.mem_univ x)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hV.symm ▸ Set.mem_univ (f x))
  exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

def toSource : small X (cover U V f) ⟶ small X U :=
  SmallRefinementComparison.refinement (X := X) (cover U V f) U Prod.fst (fun _ _ hz => hz.1)

theorem toSource_inclusion : toSource U V f ≫ inclusion X U = inclusion X (cover U V f) :=
  SmallRefinementComparison.refinement_inclusion (X := X) (cover U V f) U Prod.fst (fun _ _ hz => hz.1)

def toTarget : small X (cover U V f) ⟶ small Y V :=
  SmallRetractionComparison.map (X := X) (Y := Y) (cover U V f) V f Prod.snd (fun _ _ hz => hz.2)

theorem toTarget_inclusion : toTarget U V f ≫ inclusion Y V = inclusion X (cover U V f) ≫ push f :=
  SmallRetractionComparison.map_inclusion (X := X) (Y := Y) (cover U V f) V f Prod.snd (fun _ _ hz => hz.2)

end
end Finsler.CylinderCommonCover
