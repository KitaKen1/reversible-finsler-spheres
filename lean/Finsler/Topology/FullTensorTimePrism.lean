module

public import Finsler.Topology.TensorTimePrismComparison

/-! The genuine tensor-time prism on all input chains, and its literal
restriction to the actual common small input complexes. No shuffle
associativity or comparison with the full product-time prism is assumed. -/

@[expose] public section
namespace Finsler.FullTensorTimePrism

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.TensorApproximationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

def prism (X Y : TopCat.{0}) : Homotopy
    (𝟙 (chains X) ⊗ₘ push (AnnularTimeTrim.slice Y 0))
    (𝟙 (chains X) ⊗ₘ push (AnnularTimeTrim.slice Y 1)) :=
  tensorHomotopy (Homotopy.refl (𝟙 (chains X)))
    ((AnnularTimeTrim.cylinder Y).toSSet.chainComplexMap coeff)

theorem on_summand (X Y : TopCat.{0}) (j k : ℕ) :
    ιTensorObj (chains X) (chains Y) j k (j + k) rfl ≫
      (prism X Y).hom (j + k) (j + k + 1) =
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j, k + 1) •
      ((𝟙 ((chains X).X j) ⊗ₘ AnnularTimeTrim.prism Y k) ≫
        ιTensorObj (chains X) (chains (TopCat.of (ClosedInterval × Y)))
          j (k + 1) (j + k + 1) (by omega)) := by
  rw [prism, TensorPrismSummands.on_summand]
  simp only [Homotopy.refl, Homotopy.ofEq_hom, Pi.zero_apply,
    MonoidalPreadditive.zero_tensor, zero_comp, smul_zero, zero_add, HomologicalComplex.id_f]
  rfl

theorem small_restriction {X Y : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set (ClosedInterval × Y)) (N : ℕ) :
    (inclusion X U ⊗ₘ inclusion Y (CommonPrismRefinement.endpointCover Y V)).f N ≫
      (prism X Y).hom N (N + 1) =
    (TensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom N (N + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro j k htotal
  subst N
  change ιTensorObj (small X U) (small Y (CommonPrismRefinement.endpointCover Y V))
    j k (j + k) rfl ≫
    ((inclusion X U ⊗ₘ inclusion Y (CommonPrismRefinement.endpointCover Y V)).f (j + k) ≫
      (prism X Y).hom (j + k) (j + k + 1)) =
    ιTensorObj (small X U) (small Y (CommonPrismRefinement.endpointCover Y V))
      j k (j + k) rfl ≫
      (TensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (j + k) (j + k + 1)
  have hi : ιTensorObj (small X U) (small Y (CommonPrismRefinement.endpointCover Y V))
      j k (j + k) rfl ≫
      (inclusion X U ⊗ₘ inclusion Y (CommonPrismRefinement.endpointCover Y V)).f (j + k) =
      ((inclusion X U).f j ⊗ₘ (inclusion Y (CommonPrismRefinement.endpointCover Y V)).f k) ≫
        ιTensorObj (chains X) (chains Y) j k (j + k) rfl :=
    HomologicalComplex.ι_tensorHom (inclusion X U)
      (inclusion Y (CommonPrismRefinement.endpointCover Y V)) j k (j + k) rfl
  rw [← Category.assoc, hi, Category.assoc, on_summand,
    TensorTimePrismComparison.on_summand (X := X) (Y := Y) U V]
  simp only [Linear.comp_units_smul, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, CommonPrismRefinement.prism_hom]

end
end Finsler.FullTensorTimePrism
