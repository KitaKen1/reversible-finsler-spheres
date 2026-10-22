module

public import Finsler.Topology.RelativeFactorwiseComparison
public import Finsler.Topology.CommonPrismRefinement

/-! Instantiate the relative factorwise comparison with the genuine
time prism in the second input. The common endpoint cover gives its
actual endpoint factorizations. On each summand the prism preserves the
first degree and raises only the second degree. -/

@[expose] public section
namespace Finsler.TensorTimePrismComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.TensorApproximationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set (ClosedInterval × Y))

def prism : Homotopy
    (inclusion X U ⊗ₘ (inclusion Y (CommonPrismRefinement.endpointCover Y V) ≫
      push (AnnularTimeTrim.slice Y 0)))
    (inclusion X U ⊗ₘ (inclusion Y (CommonPrismRefinement.endpointCover Y V) ≫
      push (AnnularTimeTrim.slice Y 1))) :=
  tensorHomotopy (Homotopy.refl (inclusion X U)) (CommonPrismRefinement.prism Y V)

theorem on_summand (j k : ℕ) :
    ιTensorObj (small X U) (small Y (CommonPrismRefinement.endpointCover Y V))
      j k (j + k) rfl ≫ (prism U V).hom (j + k) (j + k + 1) =
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, k + 1) •
      (((inclusion X U).f j ⊗ₘ (CommonPrismRefinement.prism Y V).hom k (k + 1)) ≫
        ιTensorObj (chains X) (chains (TopCat.of (ClosedInterval × Y))) j (k + 1) (j + k + 1) (by omega)) := by
  rw [prism, Finsler.TensorPrismSummands.on_summand]
  simp only [Homotopy.refl, Homotopy.ofEq_hom, Pi.zero_apply,
    MonoidalPreadditive.zero_tensor, zero_comp, smul_zero, zero_add]

theorem boundary {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)
    (d : ℕ) (u : ∀ q, (small (X ⊗ TopCat.of (ClosedInterval × Y))
      (SmallRectangleShuffle.rectangles U V)).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small (X ⊗ TopCat.of (ClosedInterval × Y)) (SmallRectangleShuffle.rectangles U V)).d
        (d + q + 2) (d + q + 1) ≫ u q) (q : ℕ) :
    ((small X U ⊗ small Y (CommonPrismRefinement.endpointCover Y V)).iCycles (d + q) ≫
      (prism U V).hom (d + q) (d + q + 1)) ≫
      (((SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y)) ≫
        FactorwiseSubdivisionComparison.productRetraction U V hU hcU hV hcV).f (d + q + 1) -
        (FactorwiseSubdivisionComparison.factorwise U V hU hcU hV hcV).f (d + q + 1)) ≫ u q) =
    ((small X U ⊗ small Y (CommonPrismRefinement.endpointCover Y V)).iCycles (d + q) ≫
      (prism U V).hom (d + q) (d + q + 1) ≫
      (FactorwiseSubdivisionComparison.comparison U V hU hcU hV hcV).hom (d + q + 1) (d + q + 2) ≫
        u (q + 1)) ≫ E.d (q + 1) q := by
  let e₀ : small Y (CommonPrismRefinement.endpointCover Y V) ⟶
      small (TopCat.of (ClosedInterval × Y)) V :=
    PullbackPairCover.leftMap (X := Y) (Y := TopCat.of (ClosedInterval × Y))
      (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)
  let e₁ : small Y (CommonPrismRefinement.endpointCover Y V) ⟶
      small (TopCat.of (ClosedInterval × Y)) V :=
    PullbackPairCover.rightMap (X := Y) (Y := TopCat.of (ClosedInterval × Y))
      (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)
  apply RelativeFactorwiseComparison.prism_boundary
    (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V hU hcU hV hcV (prism U V)
    (𝟙 (small X U) ⊗ₘ e₀) (𝟙 (small X U) ⊗ₘ e₁) _ _ d u hu q
  · rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => inclusion X U ⊗ₘ f)
      (PullbackPairCover.leftMap_inclusion (X := Y) (Y := TopCat.of (ClosedInterval × Y))
        (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)).symm
  · rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => inclusion X U ⊗ₘ f)
      (PullbackPairCover.rightMap_inclusion (X := Y) (Y := TopCat.of (ClosedInterval × Y))
        (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)).symm

end
end Finsler.TensorTimePrismComparison
