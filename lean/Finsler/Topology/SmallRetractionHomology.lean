module

public import Finsler.Topology.SmallChainCarrier

/-! The actual small-chain homotopy inverse is natural on homology.
No chain-level naturality of the simplex-dependent retraction is claimed. -/

@[expose] public section

namespace Finsler.SmallRetractionHomology

open CategoryTheory AlgebraicTopology HomologicalComplex Finsler.CochainComparison
open Finsler.SmallChainCarrier TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem homology_inverse {X : TopCat.{0}} {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (k : ℕ) :
    homologyMap (smallSingularRetraction coeff U hU hcover) k =
      (smallSingularHomologyIso coeff U hU hcover k).inv := by
  apply (cancel_epi (smallSingularHomologyIso coeff U hU hcover k).hom).mp
  rw [Iso.hom_inv_id, smallSingularHomologyIso_hom, ← homologyMap_comp,
    ι_comp_smallSingularRetraction, homologyMap_id]

theorem homology_naturality {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
    (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)
    (f : X ⟶ Y) (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) (k : ℕ) :
    homologyMap (smallSingularRetraction coeff U hU hcoverU) k ≫
        homologyMap (SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) coeff) k =
      homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f) coeff) k ≫
        homologyMap (smallSingularRetraction coeff V hV hcoverV) k := by
  let a := smallSingularHomologyIso coeff U hU hcoverU k
  let b := smallSingularHomologyIso coeff V hV hcoverV k
  have he := smallSingularHomologyIso_naturality coeff U hU hcoverU V f r hf hV hcoverV k
  rw [homology_inverse, homology_inverse]
  change a.inv ≫ _ = _ ≫ b.inv
  calc
    _ = a.inv ≫
        (homologyMap (SSet.chainComplexMap (X.smallSingularSubcomplexMap U V f r hf) coeff) k ≫
          b.hom) ≫ b.inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = a.inv ≫ (a.hom ≫ homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f) coeff) k) ≫
        b.inv := congrArg (fun m => a.inv ≫ m ≫ b.inv) he.symm
    _ = _ := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end
end Finsler.SmallRetractionHomology
