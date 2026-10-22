module

public import Finsler.Topology.AnnularTimeTrim

/-! The actual cylinder map and literal input naturality of its genuine
singular time prism, before any Thom or tested cochain is chosen. -/

@[expose] public section
namespace Finsler.CylinderPrismNaturality
open CategoryTheory AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

def map {X Y : TopCat.{0}} (e : X ⟶ Y) : TopCat.of (ClosedInterval × X) ⟶ TopCat.of (ClosedInterval × Y) :=
  TopCat.ofHom ⟨fun z => (z.1, e z.2), continuous_fst.prodMk (e.hom.continuous.comp continuous_snd)⟩

theorem slice_square {X Y : TopCat.{0}} (e : X ⟶ Y) (t : ClosedInterval) :
    AnnularTimeTrim.slice X t ≫ map e = e ≫ AnnularTimeTrim.slice Y t := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

theorem prism {X Y : TopCat.{0}} (e : X ⟶ Y) (q : ℕ) :
    (push e).f q ≫ AnnularTimeTrim.prism Y q =
      AnnularTimeTrim.prism X q ≫ (push (map e)).f (q + 1) := by
  rw [AnnularTimeTrim.prism, AnnularTimeTrim.prism,
    TimePrismNaturality.prism_pre, TimePrismNaturality.prism_post]
  apply TimePrismNaturality.prism_congr
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

end
end Finsler.CylinderPrismNaturality
