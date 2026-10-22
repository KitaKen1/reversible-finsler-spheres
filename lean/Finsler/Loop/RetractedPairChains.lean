module

public import Finsler.Topology.SupportedCapNaturality

/-! For a genuine topological pair with an actual retraction, the
relative singular chain quotient has a genuine chain-map section.
Its composite with the quotient is the actual id-i*r projection.
No homology rank, degree restriction or chosen cycle lift is assumed. -/

@[expose] public section
namespace Finsler.RetractedPairChains
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem push_id (X : TopCat.{0}) : push (𝟙 X) = 𝟙 (chains X) := by
  change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
    (TopCat.toSSet.map (𝟙 X)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]

variable (P : TopPair.{0}) (r : P.fst ⟶ P.snd) (hr : P.map ≫ r = 𝟙 P.snd)

def projection : chains P.fst ⟶ chains P.fst :=
  𝟙 _ - push r ≫ push P.map

include hr in
theorem inclusion_projection : push P.map ≫ projection P r = 0 := by
  rw [projection, Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    ← push_comp, hr, push_id, Category.id_comp, sub_self]

theorem projection_quotient : projection P r ≫ P.singularChainComplexπ coeff =
    P.singularChainComplexπ coeff := by
  rw [projection, Preadditive.sub_comp, Category.id_comp, Category.assoc]
  have hz : push P.map ≫ P.singularChainComplexπ coeff = 0 :=
    (P.singularChainComplexShortComplex coeff).zero
  rw [hz, comp_zero, sub_zero]

def sectionMap : P.singularChainComplex coeff ⟶ chains P.fst := by
  let S := P.singularChainComplexShortComplex coeff
  have hS := P.shortExact_singularChainComplexShortComplex coeff
  let : Epi S.g := hS.epi_g
  exact hS.exact.desc (projection P r) (inclusion_projection P r hr)

theorem quotient_section : P.singularChainComplexπ coeff ≫ sectionMap P r hr = projection P r := by
  exact (P.shortExact_singularChainComplexShortComplex coeff).exact.g_desc _ _

theorem section_quotient : sectionMap P r hr ≫ P.singularChainComplexπ coeff = 𝟙 _ := by
  let S := P.singularChainComplexShortComplex coeff
  let : Epi S.g := (P.shortExact_singularChainComplexShortComplex coeff).epi_g
  apply (cancel_epi (P.singularChainComplexπ coeff)).mp
  rw [← Category.assoc, quotient_section, projection_quotient, Category.comp_id]

theorem homology_section (q : ℕ) :
    HomologicalComplex.homologyMap (sectionMap P r hr) q ≫
      HomologicalComplex.homologyMap (P.singularChainComplexπ coeff) q = 𝟙 _ := by
  rw [← HomologicalComplex.homologyMap_comp, section_quotient, HomologicalComplex.homologyMap_id]

theorem homology_projection (q : ℕ) :
    HomologicalComplex.homologyMap (P.singularChainComplexπ coeff) q ≫
      HomologicalComplex.homologyMap (sectionMap P r hr) q =
        HomologicalComplex.homologyMap (projection P r) q := by
  rw [← HomologicalComplex.homologyMap_comp, quotient_section]

include r hr in
theorem quotient_homology_surjective (q : ℕ) : Function.Surjective
    (HomologicalComplex.homologyMap (P.singularChainComplexπ coeff) q).hom := by
  intro z
  refine ⟨(HomologicalComplex.homologyMap (sectionMap P r hr) q).hom z, ?_⟩
  exact ConcreteCategory.congr_hom (homology_section P r hr q) z

end
end Finsler.RetractedPairChains
