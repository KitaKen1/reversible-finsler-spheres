module

public import Finsler.Topology.BidegreeOperationFilling
public import Finsler.Topology.FactorwiseSubdivisionComparison

/-! Transfer the actual fixed-bidegree normalized-zero result from
factorwise small chains to cross-then-subdivide on ordinary homology.
The comparison is inside the actual small product complex before the
closed bounded operation, so the target space is unchanged. -/

@[expose] public section
namespace Finsler.FactorwiseBidegreeHomology

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SmallRectangleShuffle Finsler.SmallRectangleCross TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem zero {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ k, IsOpen (V k)) (hcV : ⋃ k, V k = Set.univ)
    (Z : TopCat.{0}) {m : ℕ}
    (u : DegreeLoweringHomology.Map (small (X ⊗ Y) (rectangles U V)) (chains Z) m)
    (j k q : ℕ) (htotal : j + k = m + q)
    (hnorm : ιTensorObj (small X U) (small Y V) j k (m + q) htotal ≫
      (cross U V).f (m + q) ≫ u.component q ≫ (SingularNormalization.projector Z).f q = 0) :
    HomologicalComplex.homologyCross (chains X) (chains Y) j k (m + q) htotal ≫
      HomologicalComplex.homologyMap
        (ambient X Y ≫ FactorwiseSubdivisionComparison.productRetraction U V hU hcU hV hcV)
        (m + q) ≫ u.homology q = 0 := by
  let rx := smallSingularRetraction (X := X) coeff U hU hcU
  let ry := smallSingularRetraction (X := Y) coeff V hV hcV
  have hz := BidegreeOperationFilling.homology_zero Z (cross U V) u j k q htotal hnorm
  have hn : (HomologicalComplex.homologyMap rx j ⊗ₘ HomologicalComplex.homologyMap ry k) ≫
      HomologicalComplex.homologyCross (small X U) (small Y V) j k (m + q) htotal =
      HomologicalComplex.homologyCross (chains X) (chains Y) j k (m + q) htotal ≫
        HomologicalComplex.homologyMap (rx ⊗ₘ ry) (m + q) :=
    HomologicalComplex.homologyCross_naturality rx ry j k (m + q) htotal
  rw [FactorwiseSubdivisionComparison.homology_comparison U V hU hcU hV hcV,
    FactorwiseSubdivisionComparison.factorwise, HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyCross (chains X) (chains Y) j k (m + q) htotal ≫
    (HomologicalComplex.homologyMap (rx ⊗ₘ ry) (m + q) ≫
      HomologicalComplex.homologyMap (cross U V) (m + q)) ≫ u.homology q = 0
  simp only [← Category.assoc]
  rw [← hn]
  simpa only [Category.assoc, hz, comp_zero]

end
end Finsler.FactorwiseBidegreeHomology
