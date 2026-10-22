module

public import Finsler.Topology.SmallRetractionComparison

/-! A finite family of actual maps has one genuine open full pullback
cover, and actual small-chain maps to every target cover. -/

@[expose] public section
namespace Finsler.FinitePullbackCover

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : TopCat.{0}} {α ι : Type*} [Finite α]
  (U : ι → Set Y) (f : α → (X ⟶ Y))

def cover : (α → ι) → Set X := fun c => ⋂ a, f a ⁻¹' U (c a)

theorem isOpen (hU : ∀ i, IsOpen (U i)) (c : α → ι) :
    IsOpen (cover U f c) :=
  isOpen_iInter_of_finite (fun a => (hU (c a)).preimage (f a).hom.continuous)

theorem covers (hU : ⋃ i, U i = Set.univ) :
    ⋃ c, cover U f c = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  have hx : ∀ a, ∃ i, f a x ∈ U i := fun a =>
    Set.mem_iUnion.mp (hU.symm ▸ Set.mem_univ (f a x))
  choose c hc using hx
  exact Set.mem_iUnion.mpr ⟨c, Set.mem_iInter.mpr hc⟩

theorem maps (a : α) (c : α → ι) :
    Set.MapsTo (f a) (cover U f c) (U (c a)) :=
  fun _ hx => Set.mem_iInter.mp hx a

def map (a : α) : small X (cover U f) ⟶ small Y U :=
  SmallRetractionComparison.map (X := X) (Y := Y) (cover U f) U (f a) (fun c => c a) (maps U f a)

theorem map_inclusion (a : α) :
    map U f a ≫ inclusion Y U = inclusion X (cover U f) ≫ push (f a) :=
  SmallRetractionComparison.map_inclusion (X := X) (Y := Y) (cover U f) U (f a) (fun c => c a) (maps U f a)

end
end Finsler.FinitePullbackCover
