module

public import Finsler.Topology.JoinedEndpointMaps

/-! The actual shuffle time interval and the actual topological time
prism agree after the genuine cylinder-coordinate flip, on all chains. -/

@[expose] public section
namespace Finsler.TimeIntervalPrismIdentification

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.JoinedEndpointMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem cylinder_flip (X : TopCat.{0}) :
    (AnnularTimeTrim.cylinder X).h ≫ cylinderFlip X = 𝟙 (X ⊗ TopCat.I) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

theorem interval_prism (X Y : TopCat.{0}) (f : X ⊗ TopCat.I ⟶ Y) (j : ℕ) :
    TimeTriangleSplit.interval X j ≫ (push f).f (j + 1) =
      AnnularTimeTrim.prism X j ≫ (push (cylinderFlip X ≫ f)).f (j + 1) := by
  change _ = ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).hom j (j + 1) ≫ _
  rw [← TimeShuffleComparison.rectangle_eq_prism]
  change _ = (TimeTriangleSplit.interval X j ≫
    (push (AnnularTimeTrim.cylinder X).h).f (j + 1)) ≫ _
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← push_comp]
  rw [← Category.assoc, cylinder_flip, Category.id_comp]

theorem component_prism {X Y Z : TopCat.{0}} (f : X ⊗ TopCat.I ⟶ Y) (d : ℕ)
    (u : ∀ q, (chains Y).X (d + q + 1) ⟶ (chains Z).X q) (q : ℕ) :
    CappedTimeSplit.component f d u q =
      AnnularTimeTrim.prism X (d + q) ≫ (push (cylinderFlip X ≫ f)).f (d + q + 1) ≫ u q := by
  unfold CappedTimeSplit.component
  rw [← Category.assoc, interval_prism, Category.assoc]

end
end Finsler.TimeIntervalPrismIdentification
