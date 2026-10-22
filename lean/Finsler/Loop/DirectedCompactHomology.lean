/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
Adapted here from TauCeti/AlgebraicTopology/Singular/DirectedUnion.lean:
the two compact-support colimit constructions, preserving their proofs.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Coproduct
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import TauCeti.Topology.Category.TopCat.Subspace

/-! Reuse Tau Ceti's actual compact-support filtered-colimit argument.
The library source is present at the fixed project pin but this module
was not in the shared compiled cache; all required dependencies are.
Only this local source is compiled. -/

@[expose] public section
namespace Finsler.DirectedCompactHomology

noncomputable section
open CategoryTheory Limits AlgebraicTopology Topology TopCat
universe w v u

section SSet
variable {J : Type*} [Category J] {F : J ⥤ TopCat.{w}} (c : Cocone F)

def toSSet [IsFiltered J] (hc : ∀ j, IsEmbedding (c.ι.app j))
    (hK : ∀ K : Set c.pt, IsCompact K → ∃ j, K ⊆ Set.range (c.ι.app j)) :
    IsColimit (TopCat.toSSet.mapCocone c) :=
  evaluationJointlyReflectsColimits _ fun n ↦ by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun σ ↦ ?_) (fun j x y hxy ↦ ?_)
    · obtain ⟨j, hj⟩ := hK _ (isCompact_range (c.pt.toSSetObjEquiv n σ).continuous)
      obtain ⟨τ, hτ⟩ := ((hc j).isInducing.mem_range_toSSet_map_app_iff n σ).2 hj
      exact ⟨j, τ, hτ.symm⟩
    · refine ⟨j, 𝟙 j, ?_⟩
      have : Mono (c.ι.app j) := (TopCat.mono_iff_injective _).2 (hc j).injective
      have : Mono ((((evaluation _ _).obj n).mapCocone (TopCat.toSSet.mapCocone c)).ι.app j) :=
        inferInstanceAs (Mono ((TopCat.toSSet.map (c.ι.app j)).app n))
      rw [(CategoryTheory.mono_iff_injective _).1 this hxy]
end SSet

section Homology
variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)
  {J : Type*} [Category J] [IsFiltered J] [HasColimitsOfShape J (Type w)]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] {F : J ⥤ TopCat.{w}} (c : Cocone F)

def homology (hc : ∀ j, IsEmbedding (c.ι.app j))
    (hK : ∀ K : Set c.pt, IsCompact K → ∃ j, K ⊆ Set.range (c.ι.app j)) :
    IsColimit (((singularHomologyFunctor C n).obj R).mapCocone c) :=
  isColimitOfPreserves
    ((SSet.chainComplexFunctor C).obj R ⋙ HomologicalComplex.homologyFunctor C _ n)
    (toSSet c hc hK)
end Homology

end
end Finsler.DirectedCompactHomology
