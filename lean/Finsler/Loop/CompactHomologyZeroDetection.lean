module

public import Finsler.Loop.CompactHomologyLift
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! Vanishing of an actual compact singular homology class in the
full space is already witnessed in one larger actual compact subspace.
Use genuine filtered-colimit equality detection, with no new lift data. -/

@[expose] public section
namespace Finsler.CompactHomologyZeroDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology TopologicalSpace Topology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

theorem exists_larger (X : TopCat.{0}) (q : ℕ) (K : Compacts X)
    (z : (chains (TopCat.of (K : Set X))).homology q)
    (hz : (HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap X (K : Set X))) q).hom z = 0) :
    ∃ L : Compacts X, ∃ f : K ⟶ L,
      (HomologicalComplex.homologyMap (push ((CompactHomologyLift.diagram X).map f)) q).hom z = 0 := by
  have : PreservesFilteredColimitsOfSize.{0,0} (forget (ModuleCat.{0} (ZMod 2))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let C := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).mapCocone
    (CompactHomologyLift.cocone X)
  have he : C.ι.app K z = C.ι.app K 0 := by
    change (HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap X (K : Set X))) q).hom z =
      (HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap X (K : Set X))) q).hom 0
    rw [map_zero]
    exact hz
  obtain ⟨L, f, hf⟩ := ((CompactHomologyLift.homologyColimit X q).eq_iff' z 0).mp he
  refine ⟨L, f, ?_⟩
  change (HomologicalComplex.homologyMap (push ((CompactHomologyLift.diagram X).map f)) q).hom z =
    (HomologicalComplex.homologyMap (push ((CompactHomologyLift.diagram X).map f)) q).hom 0 at hf
  rw [map_zero] at hf
  exact hf

end
end Finsler.CompactHomologyZeroDetection
