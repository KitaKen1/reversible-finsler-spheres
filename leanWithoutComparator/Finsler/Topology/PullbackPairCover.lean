module

public import Finsler.Topology.SmallRetractionComparison

/-! Pairwise intersections of genuine pullback covers give one open
source refinement for two maps, independently of every cochain degree. -/

@[expose] public section
namespace Finsler.PullbackPairCover

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : TopCat.{0}} {ι κ : Type*} (U : ι → Set Y) (V : κ → Set Z)
  (f : X ⟶ Y) (g : X ⟶ Z)

def cover : ι × κ → Set X := fun ij => f ⁻¹' U ij.1 ∩ g ⁻¹' V ij.2

theorem isOpen (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j)) (ij : ι × κ) :
    IsOpen (cover U V f g ij) :=
  ((hU ij.1).preimage f.hom.continuous).inter ((hV ij.2).preimage g.hom.continuous)

theorem covers (hU : ⋃ i, U i = Set.univ) (hV : ⋃ j, V j = Set.univ) :
    ⋃ ij, cover U V f g ij = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU.symm ▸ Set.mem_univ (f x))
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hV.symm ▸ Set.mem_univ (g x))
  exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

theorem maps_left (ij : ι × κ) : Set.MapsTo f (cover U V f g ij) (U ij.1) :=
  fun _ hz => hz.1

theorem maps_right (ij : ι × κ) : Set.MapsTo g (cover U V f g ij) (V ij.2) :=
  fun _ hz => hz.2

def leftMap : small X (cover U V f g) ⟶ small Y U :=
  SmallRetractionComparison.map (cover U V f g) U f Prod.fst (maps_left U V f g)

def rightMap : small X (cover U V f g) ⟶ small Z V :=
  SmallRetractionComparison.map (cover U V f g) V g Prod.snd (maps_right U V f g)

theorem leftMap_inclusion : leftMap U V f g ≫ inclusion Y U = inclusion X (cover U V f g) ≫ push f :=
  SmallRetractionComparison.map_inclusion (cover U V f g) U f Prod.fst (maps_left U V f g)

theorem rightMap_inclusion : rightMap U V f g ≫ inclusion Z V = inclusion X (cover U V f g) ≫ push g :=
  SmallRetractionComparison.map_inclusion (cover U V f g) V g Prod.snd (maps_right U V f g)

end
end Finsler.PullbackPairCover
