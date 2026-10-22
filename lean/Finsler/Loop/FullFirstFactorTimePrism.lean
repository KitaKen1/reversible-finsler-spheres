module

public import Finsler.Loop.FirstFactorTensorTimePrismComparison
public import Finsler.Loop.FirstFactorTensorPrismNaturality

/-! The actual time prism on the first factor of all input chains,
and its strict restriction to the common small input complexes. -/

@[expose] public section
namespace Finsler.FullFirstFactorTimePrism

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.TensorApproximationHomotopy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

def prism (X Y : TopCat.{0}) : Homotopy
    (push (AnnularTimeTrim.slice X 0) ⊗ₘ 𝟙 (chains Y))
    (push (AnnularTimeTrim.slice X 1) ⊗ₘ 𝟙 (chains Y)) :=
  FirstFactorTensorPrismNaturality.prism
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) (chains Y)

theorem on_summand (X Y : TopCat.{0}) (j k : ℕ) :
    ιTensorObj (chains X) (chains Y) j k (j + k) rfl ≫
      (prism X Y).hom (j + k) (j + k + 1) =
    ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (j + 1, k) •
      ((AnnularTimeTrim.prism X j ⊗ₘ 𝟙 ((chains Y).X k)) ≫
        ιTensorObj (chains (TopCat.of (ClosedInterval × X))) (chains Y)
          (j + 1) k (j + k + 1) (by omega)) :=
  FirstFactorTensorPrismNaturality.on_summand
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) (chains Y) j k

theorem small_restriction {X Y : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y) (N : ℕ) :
    (inclusion X (CommonPrismRefinement.endpointCover X U) ⊗ₘ inclusion Y V).f N ≫
      (prism X Y).hom N (N + 1) =
    (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom N (N + 1) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro j k htotal
  subst N
  change ιTensorObj (small X (CommonPrismRefinement.endpointCover X U)) (small Y V)
    j k (j + k) rfl ≫
    ((inclusion X (CommonPrismRefinement.endpointCover X U) ⊗ₘ inclusion Y V).f (j + k) ≫
      (prism X Y).hom (j + k) (j + k + 1)) =
    ιTensorObj (small X (CommonPrismRefinement.endpointCover X U)) (small Y V)
      j k (j + k) rfl ≫
      (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (j + k) (j + k + 1)
  have hi : ιTensorObj (small X (CommonPrismRefinement.endpointCover X U)) (small Y V)
      j k (j + k) rfl ≫
      (inclusion X (CommonPrismRefinement.endpointCover X U) ⊗ₘ inclusion Y V).f (j + k) =
      ((inclusion X (CommonPrismRefinement.endpointCover X U)).f j ⊗ₘ (inclusion Y V).f k) ≫
        ιTensorObj (chains X) (chains Y) j k (j + k) rfl :=
    HomologicalComplex.ι_tensorHom (inclusion X (CommonPrismRefinement.endpointCover X U))
      (inclusion Y V) j k (j + k) rfl
  rw [← Category.assoc, hi, Category.assoc, on_summand,
    FirstFactorTensorTimePrismComparison.on_summand (X := X) (Y := Y) U V]
  simp only [Linear.comp_units_smul, tensorHom_comp_tensorHom_assoc,
    Category.comp_id, CommonPrismRefinement.prism_hom]

end
end Finsler.FullFirstFactorTimePrism

