module

public import Finsler.Topology.RelativeFactorwiseComparison
public import Finsler.Topology.CommonPrismRefinement

/-! The genuine time prism in the first input, with the tensor order
unchanged. Both endpoints factor through the actual common small cover.
The explicit relative subdivision boundary stays in the capped target. -/

@[expose] public section
namespace Finsler.FirstFactorTensorTimePrismComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.TensorApproximationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {X Y : TopCat.{0}} {ι κ : Type*}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)

def prism : Homotopy
    ((inclusion X (CommonPrismRefinement.endpointCover X U) ≫
      push (AnnularTimeTrim.slice X 0)) ⊗ₘ inclusion Y V)
    ((inclusion X (CommonPrismRefinement.endpointCover X U) ≫
      push (AnnularTimeTrim.slice X 1)) ⊗ₘ inclusion Y V) :=
  tensorHomotopy (CommonPrismRefinement.prism X U) (Homotopy.refl (inclusion Y V))

theorem on_summand (j k : ℕ) :
    ιTensorObj (small X (CommonPrismRefinement.endpointCover X U)) (small Y V)
      j k (j + k) rfl ≫ (prism U V).hom (j + k) (j + k + 1) =
    ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j + 1, k) •
      (((CommonPrismRefinement.prism X U).hom j (j + 1) ⊗ₘ (inclusion Y V).f k) ≫
        ιTensorObj (chains (TopCat.of (ClosedInterval × X))) (chains Y)
          (j + 1) k (j + k + 1) (by omega)) := by
  rw [prism, Finsler.TensorPrismSummands.on_summand]
  simp only [Homotopy.refl, Homotopy.ofEq_hom, Pi.zero_apply,
    MonoidalPreadditive.tensor_zero, zero_comp, smul_zero, add_zero]

theorem boundary {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)
    (d : ℕ) (u : ∀ q, (small (TopCat.of (ClosedInterval × X) ⊗ Y)
      (SmallRectangleShuffle.rectangles U V)).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V)).d
        (d + q + 2) (d + q + 1) ≫ u q) (q : ℕ) :
    ((small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V).iCycles (d + q) ≫
      (prism U V).hom (d + q) (d + q + 1)) ≫
      (((SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫
        FactorwiseSubdivisionComparison.productRetraction U V hU hcU hV hcV).f (d + q + 1) -
        (FactorwiseSubdivisionComparison.factorwise U V hU hcU hV hcV).f (d + q + 1)) ≫ u q) =
    ((small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V).iCycles (d + q) ≫
      (prism U V).hom (d + q) (d + q + 1) ≫
      (FactorwiseSubdivisionComparison.comparison U V hU hcU hV hcV).hom (d + q + 1) (d + q + 2) ≫
        u (q + 1)) ≫ E.d (q + 1) q := by
  let e₀ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U :=
    PullbackPairCover.leftMap (X := X) (Y := TopCat.of (ClosedInterval × X))
      (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  let e₁ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U :=
    PullbackPairCover.rightMap (X := X) (Y := TopCat.of (ClosedInterval × X))
      (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  apply RelativeFactorwiseComparison.prism_boundary
    (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hcU hV hcV (prism U V)
    (e₀ ⊗ₘ 𝟙 (small Y V)) (e₁ ⊗ₘ 𝟙 (small Y V)) _ _ d u hu q
  · rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => f ⊗ₘ inclusion Y V)
      (PullbackPairCover.leftMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X))
        (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm
  · rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => f ⊗ₘ inclusion Y V)
      (PullbackPairCover.rightMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X))
        (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm

end
end Finsler.FirstFactorTensorTimePrismComparison

