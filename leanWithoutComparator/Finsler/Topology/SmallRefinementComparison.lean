module

public import Finsler.Topology.SmallRetractionHomology
import all TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-! Actual chain homotopy under cover refinement, with every independent
carrier preserved after inclusion. This does not assert chain naturality
of the simplex-dependent small-chain retraction. -/

@[expose] public section
namespace Finsler.SmallRefinementComparison

open CategoryTheory AlgebraicTopology HomologicalComplex Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X : TopCat.{0}} {ι κ : Type*}
  (U : ι → Set X) (V : κ → Set X) (r : ι → κ)
  (href : ∀ i, U i ⊆ V (r i))

def refinement : small X U ⟶ small X V :=
  SSet.chainComplexMap (X.smallSingularSubcomplexMap U V (𝟙 X) r href) coeff

theorem refinement_inclusion :
    refinement U V r href ≫ inclusion X V = inclusion X U := by
  have he : refinement U V r href ≫ inclusion X V =
      inclusion X U ≫ SSet.chainComplexMap (TopCat.toSSet.map (𝟙 X)) coeff := by
    simpa only [refinement, inclusion, Functor.map_comp] using
      congrArg (fun g => SSet.chainComplexMap g coeff)
        (TopCat.smallSingularSubcomplexMap_ι U V (𝟙 X) r href)
  have hid : SSet.chainComplexMap (TopCat.toSSet.map (𝟙 X)) coeff = 𝟙 (chains X) := by
    change ((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 X)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simpa only [hid, Category.comp_id] using he

variable (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)

theorem retraction_factor :
    smallSingularRetraction coeff U hU hcoverU ≫ refinement U V r href =
      singularSmallApprox coeff U ≫ smallSingularRetraction coeff V hV hcoverV := by
  calc
    _ = (smallSingularRetraction coeff U hU hcoverU ≫ refinement U V r href) ≫
        (inclusion X V ≫ smallSingularRetraction coeff V hV hcoverV) := by
      rw [ι_comp_smallSingularRetraction, Category.comp_id]
    _ = (smallSingularRetraction coeff U hU hcoverU ≫ inclusion X U) ≫
        smallSingularRetraction coeff V hV hcoverV := by
      rw [Category.assoc, ← Category.assoc (refinement U V r href), refinement_inclusion,
        ← Category.assoc]
    _ = _ := by rw [smallSingularRetraction_comp_ι]

def comparison : Homotopy (smallSingularRetraction coeff V hV hcoverV)
    (smallSingularRetraction coeff U hU hcoverU ≫ refinement U V r href) :=
  (Homotopy.ofEq (Category.id_comp (smallSingularRetraction coeff V hV hcoverV)).symm).trans
    (((singularSmallApproxHomotopy coeff U).compRight
      (smallSingularRetraction coeff V hV hcoverV)).trans
      (Homotopy.ofEq (retraction_factor U V r href hU hcoverU hV hcoverV).symm))

theorem comparison_inclusion (n : ℕ) :
    (comparison U V r href hU hcoverU hV hcoverV).hom n (n + 1) ≫
        (inclusion X V).f (n + 1) =
      singularSmallApproxHom coeff U n (n + 1) ≫ (singularSmallApprox coeff V).f (n + 1) := by
  change (0 + (singularSmallApproxHom coeff U n (n + 1) ≫
    (smallSingularRetraction coeff V hV hcoverV).f (n + 1) + 0)) ≫ _ = _
  rw [zero_add, add_zero, Category.assoc, ← HomologicalComplex.comp_f,
    smallSingularRetraction_comp_ι]

theorem comparison_preserves {γ : Type*} (W : γ → Set X) {n : ℕ}
    {c : coeff ⟶ (chains X).X n} (hc : c ∈ supported X W n) :
    c ≫ (comparison U V r href hU hcoverU hV hcoverV).hom n (n + 1) ≫
      (inclusion X V).f (n + 1) ∈ supported X W (n + 1) := by
  rw [comparison_inclusion, ← Category.assoc]
  exact approximation_preserves V W (approximationPrism_preserves U W hc)

theorem comparison_parent {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫
      (comparison U V r href hU hcoverU hV hcoverV).hom n (n + 1) ≫
      (inclusion X V).f (n + 1) ∈ supported X (parentFamily σ) (n + 1) :=
  comparison_preserves U V r href hU hcoverU hV hcoverV (parentFamily σ) (simplex_parent σ)

theorem homology_refinement (n : ℕ) :
    homologyMap (smallSingularRetraction coeff V hV hcoverV) n =
      homologyMap (smallSingularRetraction coeff U hU hcoverU) n ≫
        homologyMap (refinement U V r href) n := by
  rw [← homologyMap_comp]
  exact (comparison U V r href hU hcoverU hV hcoverV).homologyMap_eq n

end
end Finsler.SmallRefinementComparison
