module

public import Finsler.Topology.CyclesBoundaryHomology
public import Finsler.Topology.SmallRetractionComparison
public import Finsler.Topology.DegreeLoweringAdd

/-! The actual inclusion of an open full small-chain complex is split
surjective on homology. A filtered equality proved on genuine common
small cycles therefore descends to all input homology classes, without
an injectivity assumption on the filtered target. -/

@[expose] public section
namespace Finsler.SmallInclusionHomologyCancellation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology TauCeti
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set X)
  (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ)

include hU hc

theorem homology_section (q : ℕ) :
    HomologicalComplex.homologyMap (smallSingularRetraction (X := X) coeff U hU hc) q ≫
      HomologicalComplex.homologyMap (inclusion X U) q = 𝟙 ((chains X).homology q) := by
  rw [← HomologicalComplex.homologyMap_comp]
  have hi : smallSingularRetraction (X := X) coeff U hU hc ≫ inclusion X U =
      singularSmallApprox (X := X) coeff U := smallSingularRetraction_comp_ι (X := X) coeff U hU hc
  rw [hi]
  have hh := (singularSmallApproxHomotopy (X := X) coeff U).homologyMap_eq q
  simpa only [HomologicalComplex.homologyMap_id] using hh.symm

theorem eq_of_pre_inclusion (q : ℕ) (M : ModuleCat.{0} (ZMod 2))
    (a b : (chains X).homology q ⟶ M)
    (he : HomologicalComplex.homologyMap (inclusion X U) q ≫ a =
      HomologicalComplex.homologyMap (inclusion X U) q ≫ b) : a = b := by
  have hh := congrArg (fun f => HomologicalComplex.homologyMap
    (smallSingularRetraction (X := X) coeff U hU hc) q ≫ f) he
  simpa only [← Category.assoc, homology_section X U hU hc q, Category.id_comp] using hh

theorem homology_eq (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ)
    (f g : DegreeLoweringHomology.Map (chains X) E p) (q : ℕ)
    (he : (f.pre (inclusion X U)).homology q = (g.pre (inclusion X U)).homology q) :
    f.homology q = g.homology q := by
  apply eq_of_pre_inclusion X U hU hc (p + q) (E.homology q)
  simpa only [DegreeLoweringHomology.Map.pre_homology] using he

theorem eq_of_small_boundary (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ)
    (f g : DegreeLoweringHomology.Map (chains X) E p) (q : ℕ)
    (W : (small X U).cycles (p + q) ⟶ E.X (q + 1))
    (he : (small X U).iCycles (p + q) ≫ (inclusion X U).f (p + q) ≫
        (f.component q - g.component q) = W ≫ E.d (q + 1) q) :
    f.homology q = g.homology q := by
  apply homology_eq X U hU hc E p f g q
  apply CyclesBoundaryHomology.homology_eq (f.pre (inclusion X U)) (g.pre (inclusion X U)) q W
  simpa only [DegreeLoweringHomology.Map.pre, Preadditive.comp_sub, Category.assoc] using he

theorem split_of_small_boundary (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (p : ℕ)
    (f g h : DegreeLoweringHomology.Map (chains X) E p) (q : ℕ)
    (W : (small X U).cycles (p + q) ⟶ E.X (q + 1))
    (he : (small X U).iCycles (p + q) ≫ (inclusion X U).f (p + q) ≫ f.component q =
      (small X U).iCycles (p + q) ≫ (inclusion X U).f (p + q) ≫ g.component q +
      (small X U).iCycles (p + q) ≫ (inclusion X U).f (p + q) ≫ h.component q + W ≫ E.d (q + 1) q) :
    f.homology q = g.homology q + h.homology q := by
  rw [← DegreeLoweringAdd.sum_homology]
  apply eq_of_small_boundary X U hU hc E p f (DegreeLoweringAdd.sum g h) q W
  simp only [DegreeLoweringAdd.sum, Preadditive.comp_sub, Preadditive.comp_add, Category.assoc]
  rw [he]
  abel

end
end Finsler.SmallInclusionHomologyCancellation
