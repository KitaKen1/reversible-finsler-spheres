module

public import Finsler.Loop.DirectedCompactHomology
public import Finsler.Topology.SupportedCapNaturality
public import Mathlib.Topology.Sets.Compacts

/-! Every actual singular homology class comes from an actual compact
subspace, by the genuine compact-subspace directed diagram. This uses
Tau Ceti's compact-support colimit construction, not an extra lift input. -/

@[expose] public section
namespace Finsler.CompactHomologyLift
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Topology TopologicalSpace
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000

variable (X : TopCat.{0})

def diagram : Compacts X ⥤ TopCat.{0} where
  obj K := TopCat.of (K : Set X)
  map f := TopCat.ofHom (ContinuousMap.inclusion f.le)
  map_id _ := by ext x : 1; rfl
  map_comp _ _ := by ext x : 1; rfl

def cocone : Cocone (diagram X) where
  pt := X
  ι := { app K := SupportedCap.subspaceMap X (K : Set X)
         naturality := by intro K L f; ext x : 1; rfl }


theorem leg_embedding (K : Compacts X) : IsEmbedding ((cocone X).ι.app K) :=
  IsEmbedding.subtypeVal


theorem absorbs_compact (S : Set X) (hS : IsCompact S) :
    ∃ K : Compacts X, S ⊆ Set.range ((cocone X).ι.app K) := by
  refine ⟨⟨S, hS⟩, ?_⟩
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩


def homologyColimit (q : ℕ) :
    IsColimit (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).mapCocone (cocone X)) :=
  DirectedCompactHomology.homology coeff q (cocone X) (leg_embedding X) (absorbs_compact X)


theorem exists_lift (q : ℕ) (x : (chains X).homology q) :
    ∃ K : Compacts X, ∃ y : (chains (TopCat.of (K : Set X))).homology q,
      (HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap X (K : Set X))) q).hom y = x := by
  have : PreservesFilteredColimitsOfSize.{0,0} (forget (ModuleCat.{0} (ZMod 2))) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  obtain ⟨K, y, hy⟩ := Concrete.isColimit_exists_rep _ (homologyColimit X q) x
  exact ⟨K, y, hy⟩

end
end Finsler.CompactHomologyLift
