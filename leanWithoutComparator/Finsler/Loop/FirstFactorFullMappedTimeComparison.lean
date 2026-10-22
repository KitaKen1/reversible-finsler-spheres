module

public import Finsler.Loop.FirstFactorMappedTimeComparison
public import Finsler.Loop.FullFirstFactorTimePrism
public import Finsler.Loop.TensorSmallInputCancellation

/-! Remove both actual small input restrictions from the mapped
first-time comparison using a section on the entire tensor homology.
The resulting operation uses factorwise cylinder subdivisions. -/

@[expose] public section
namespace Finsler.FirstFactorFullMappedTimeComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.FirstFactorMappedRectangles

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1700000

variable {X Y Z : TopCat.{0}} {ι κ μ : Type*}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)
  (W : μ → Set Z) (hW : ∀ i, IsOpen (W i)) (hcW : ⋃ i, W i = Set.univ)
  (f : TopCat.of (ClosedInterval × X) ⊗ Y ⟶ Z)
  (r : ι × κ → μ)
  (hf : ∀ c, Set.MapsTo f (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V c) (W (r c)))
  {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)
  (u : ∀ q, (small Z W).X (d + q + 1) ⟶ E.X q)
  (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q = (small Z W).d (d + q + 2) (d + q + 1) ≫ u q)
  (h₀ : ∀ q, (push (AnnularTimeTrim.slice X 0) ⊗ₘ 𝟙 (chains Y)).f (d + q + 1) ≫
    (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q = 0)
  (h₁ : ∀ q, (push (AnnularTimeTrim.slice X 1) ⊗ₘ 𝟙 (chains Y)).f (d + q + 1) ≫
    (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q = 0)

theorem endpoint_restriction (t : ClosedInterval) :
    (inclusion X (CommonPrismRefinement.endpointCover X U) ⊗ₘ inclusion Y V) ≫
      (push (AnnularTimeTrim.slice X t) ⊗ₘ 𝟙 (chains Y)) =
    CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V t := by
  rw [tensorHom_comp_tensorHom, Category.comp_id]
  rfl

theorem small_endpoint_zero (t : ClosedInterval)
    (ht : ∀ q, (push (AnnularTimeTrim.slice X t) ⊗ₘ 𝟙 (chains Y)).f (d + q + 1) ≫
      (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q = 0) (q : ℕ) :
    (CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V t).f (d + q + 1) ≫
      (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q = 0 := by
  rw [← endpoint_restriction (X := X) (Y := Y) U V t, HomologicalComplex.comp_f, Category.assoc, ht, comp_zero]

def coarseOperation : DegreeLoweringHomology.Map (chains X ⊗ chains Y) E d :=
  TimePrismDescent.operation (FullFirstFactorTimePrism.prism X Y) d
    (FirstFactorMappedTimeComparison.coarseCap (X := X) (Y := Y) W hW hcW f d u)
    (FirstFactorMappedTimeComparison.coarseCap_comm (X := X) (Y := Y) W hW hcW f d u hu) h₀ h₁

def operation : DegreeLoweringHomology.Map (chains X ⊗ chains Y) E d :=
  (FirstFactorMappedTimeComparison.afterOperation (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu
    (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 0 h₀)
    (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 1 h₁)).pre
      (smallSingularRetraction (X := X) coeff (CommonPrismRefinement.endpointCover X U)
        (CommonPrismRefinement.endpointCover_open X U hU)
        (CommonPrismRefinement.endpointCover_univ X U hcU) ⊗ₘ
      smallSingularRetraction (X := Y) coeff V hV hcV)

theorem coarse_small_restriction (q : ℕ) :
    ((coarseOperation (X := X) (Y := Y) W hW hcW f d u hu h₀ h₁).pre
      (inclusion X (CommonPrismRefinement.endpointCover X U) ⊗ₘ inclusion Y V)).homology q =
    (FirstFactorMappedTimeComparison.coarseOperation (X := X) (Y := Y) U V W hW hcW f d u hu
      (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 0 h₀)
      (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 1 h₁)).homology q := by
  apply DegreeLoweringHomology.Map.homology_eq_of_components
  intro q'
  dsimp only [coarseOperation, FirstFactorMappedTimeComparison.coarseOperation,
    DegreeLoweringHomology.Map.pre, TimePrismDescent.operation, TimePrismDescent.component]
  rw [← Category.assoc, FullFirstFactorTimePrism.small_restriction (X := X) (Y := Y) U V]

theorem operation_small_restriction (q : ℕ) :
    ((operation (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu h₀ h₁).pre
      (inclusion X (CommonPrismRefinement.endpointCover X U) ⊗ₘ inclusion Y V)).homology q =
    (FirstFactorMappedTimeComparison.afterOperation (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu
      (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 0 h₀)
      (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 1 h₁)).homology q := by
  dsimp only [operation]
  rw [DegreeLoweringHomology.Map.pre_homology, DegreeLoweringHomology.Map.pre_homology,
    ← Category.assoc, ← homologyMap_comp,
    TensorSmallInputCancellation.small_section (CommonPrismRefinement.endpointCover X U) V
      (CommonPrismRefinement.endpointCover_open X U hU)
      (CommonPrismRefinement.endpointCover_univ X U hcU) hV hcV,
    homologyMap_id, Category.id_comp]

theorem homology_eq (q : ℕ) :
    (coarseOperation (X := X) (Y := Y) W hW hcW f d u hu h₀ h₁).homology q =
      (operation (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu h₀ h₁).homology q := by
  apply TensorSmallInputCancellation.homology_eq (CommonPrismRefinement.endpointCover X U) V
    (CommonPrismRefinement.endpointCover_open X U hU)
    (CommonPrismRefinement.endpointCover_univ X U hcU) hV hcV d _ _ q
  rw [coarse_small_restriction (X := X) (Y := Y) U V W hW hcW f d u hu h₀ h₁,
    operation_small_restriction (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu h₀ h₁]
  exact FirstFactorMappedTimeComparison.coarse_after_homology (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu
    (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 0 h₀)
    (small_endpoint_zero (X := X) (Y := Y) U V W hW hcW f d u 1 h₁) q

end
end Finsler.FirstFactorFullMappedTimeComparison
