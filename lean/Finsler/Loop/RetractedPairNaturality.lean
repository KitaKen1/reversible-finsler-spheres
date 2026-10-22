module

public import Finsler.Loop.RetractedPairChains

/-! The ACTUAL chain sections are natural for actual pair maps that
commute with the given retractions. This is strict chain naturality,
not just equality of selected homology lifts. -/

@[expose] public section
namespace Finsler.RetractedPairNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {P Q : TopPair.{0}} (f : P ⟶ Q) (rP : P.fst ⟶ P.snd) (rQ : Q.fst ⟶ Q.snd)
  (hP : P.map ≫ rP = 𝟙 P.snd) (hQ : Q.map ≫ rQ = 𝟙 Q.snd)
  (hf : TopPair.Hom.fst f ≫ rQ = rP ≫ TopPair.Hom.snd f)

include hf in
theorem projection : push (TopPair.Hom.fst f) ≫ RetractedPairChains.projection Q rQ =
    RetractedPairChains.projection P rP ≫ push (TopPair.Hom.fst f) := by
  have he : (TopPair.Hom.fst f ≫ rQ) ≫ Q.map =
      rP ≫ (P.map ≫ TopPair.Hom.fst f) := by
    rw [hf, Category.assoc, TopPair.Hom.w]
  rw [RetractedPairChains.projection, RetractedPairChains.projection,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp]
  congr 1
  rw [← Category.assoc, ← push_comp, ← push_comp, ← push_comp, ← push_comp]
  exact congrArg push he

include hf in
theorem sectionMap : TopPair.singularChainComplexMap f coeff ≫
    RetractedPairChains.sectionMap Q rQ hQ =
      RetractedPairChains.sectionMap P rP hP ≫ push (TopPair.Hom.fst f) := by
  let : Epi (P.singularChainComplexπ coeff) :=
    (P.shortExact_singularChainComplexShortComplex coeff).epi_g
  apply (cancel_epi (P.singularChainComplexπ coeff)).mp
  rw [← Category.assoc, ← TopPair.singularChainComplexπ_pair_naturality,
    Category.assoc, RetractedPairChains.quotient_section,
    ← Category.assoc, RetractedPairChains.quotient_section]
  exact projection f rP rQ hf

include hf in
theorem homology (q : ℕ) :
    HomologicalComplex.homologyMap (TopPair.singularChainComplexMap f coeff) q ≫
      HomologicalComplex.homologyMap (RetractedPairChains.sectionMap Q rQ hQ) q =
    HomologicalComplex.homologyMap (RetractedPairChains.sectionMap P rP hP) q ≫
      HomologicalComplex.homologyMap (push (TopPair.Hom.fst f)) q := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    sectionMap f rP rQ hP hQ hf]

end
end Finsler.RetractedPairNaturality
