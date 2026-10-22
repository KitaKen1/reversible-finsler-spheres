module

public import Finsler.Loop.FirstFactorTensorTimePrismComparison
public import Finsler.Topology.SmallRetractionComparison

/-! Compute the actual sectioned first-input prism followed by the
two cylinder subdivisions. The second small inclusion/retraction is
strictly the identity. The genuine first-factor tensor sign is one. -/

@[expose] public section
namespace Finsler.FirstFactorSectionedPrismSummand

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {X Y : TopCat.{0}} {ι κ : Type*}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)

def inputRetraction :=
  smallSingularRetraction (X := X) coeff (CommonPrismRefinement.endpointCover X U)
    (CommonPrismRefinement.endpointCover_open X U hU) (CommonPrismRefinement.endpointCover_univ X U hcU) ⊗ₘ
  smallSingularRetraction (X := Y) coeff V hV hcV

def cylinderRetraction :=
  smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU ⊗ₘ
    smallSingularRetraction (X := Y) coeff V hV hcV

def firstPrefix (j : ℕ) :=
  (smallSingularRetraction (X := X) coeff (CommonPrismRefinement.endpointCover X U)
    (CommonPrismRefinement.endpointCover_open X U hU) (CommonPrismRefinement.endpointCover_univ X U hcU)).f j ≫
  (CommonPrismRefinement.prism X U).hom j (j + 1) ≫
  (smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU).f (j + 1)

theorem on_summand (j k : ℕ) :
    ιTensorObj (chains X) (chains Y) j k (j + k) rfl ≫
      (inputRetraction (X := X) (Y := Y) U V hU hcU hV hcV).f (j + k) ≫
      (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (j + k) (j + k + 1) ≫
      (cylinderRetraction (X := X) (Y := Y) U V hU hcU hV hcV).f (j + k + 1) =
    (firstPrefix U hU hcU j ⊗ₘ (smallSingularRetraction (X := Y) coeff V hV hcV).f k) ≫
      ιTensorObj (small (TopCat.of (ClosedInterval × X)) U) (small Y V) (j + 1) k (j + k + 1) (by omega) := by
  let rx := smallSingularRetraction (X := X) coeff (CommonPrismRefinement.endpointCover X U)
    (CommonPrismRefinement.endpointCover_open X U hU) (CommonPrismRefinement.endpointCover_univ X U hcU)
  let ry := smallSingularRetraction (X := Y) coeff V hV hcV
  let rt := smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU
  have hi : ιTensorObj (chains X) (chains Y) j k (j + k) rfl ≫ (rx ⊗ₘ ry).f (j + k) =
      (rx.f j ⊗ₘ ry.f k) ≫
        ιTensorObj (small X (CommonPrismRefinement.endpointCover X U)) (small Y V) j k (j + k) rfl := by
    rw [HomologicalComplex.tensorHom_eq_mapBifunctorMap]
    exact HomologicalComplex.ι_tensorHom rx ry j k (j + k) rfl
  have ho : ιTensorObj (chains (TopCat.of (ClosedInterval × X))) (chains Y) (j + 1) k (j + k + 1) (by omega) ≫
      (rt ⊗ₘ ry).f (j + k + 1) =
    (rt.f (j + 1) ⊗ₘ ry.f k) ≫
      ιTensorObj (small (TopCat.of (ClosedInterval × X)) U) (small Y V) (j + 1) k (j + k + 1) (by omega) := by
    rw [HomologicalComplex.tensorHom_eq_mapBifunctorMap]
    exact HomologicalComplex.ι_tensorHom rt ry (j + 1) k (j + k + 1) (by omega)
  have hyr : (inclusion Y V).f k ≫ ry.f k = 𝟙 ((small Y V).X k) := by
    have hh := congrArg (fun f => f.f k) (ι_comp_smallSingularRetraction (X := Y) coeff V hV hcV)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using hh
  change ιTensorObj (chains X) (chains Y) j k (j + k) rfl ≫ (rx ⊗ₘ ry).f (j + k) ≫
    (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (j + k) (j + k + 1) ≫
    (rt ⊗ₘ ry).f (j + k + 1) = _
  rw [← Category.assoc, hi, Category.assoc,
    ← Category.assoc
      (ιTensorObj (small X (CommonPrismRefinement.endpointCover X U)) (small Y V) j k (j + k) rfl),
    FirstFactorTensorTimePrismComparison.on_summand (X := X) (Y := Y) U V]
  simp only [ComplexShape.ε₁_def, one_smul, Category.assoc]
  rw [ho]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, hyr, Category.comp_id]
  rfl

end
end Finsler.FirstFactorSectionedPrismSummand
