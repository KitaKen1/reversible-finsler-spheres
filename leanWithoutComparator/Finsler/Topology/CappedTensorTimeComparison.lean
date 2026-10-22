module

public import Finsler.Topology.SmallTensorCrossRetraction
public import Finsler.Topology.TimePrismDescent
public import Finsler.Topology.DegreeLoweringExact

/-! Construct both genuine capped tensor-time operations. The actual
common endpoint cover makes both subdivision orders identical on each
endpoint. Their difference on cycles is an explicit boundary in the
same target complex, and hence their homology maps agree. -/

@[expose] public section
namespace Finsler.CappedTensorTimeComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {X Y : TopCat.{0}} {ι κ : Type*}
  (U : ι → Set X) (V : κ → Set (ClosedInterval × Y))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)

def before := SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y)) ≫
  FactorwiseSubdivisionComparison.productRetraction
    (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V hU hcU hV hcV

def after := FactorwiseSubdivisionComparison.factorwise
  (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V hU hcU hV hcV

def endpoint (t : ClosedInterval) := inclusion X U ⊗ₘ
  (inclusion Y (CommonPrismRefinement.endpointCover Y V) ≫ push (AnnularTimeTrim.slice Y t))

theorem endpoints :
    endpoint U V 0 ≫ before U V hU hcU hV hcV = endpoint U V 0 ≫ after U V hU hcU hV hcV ∧
    endpoint U V 1 ≫ before U V hU hcU hV hcV = endpoint U V 1 ≫ after U V hU hcU hV hcV := by
  let e₀ : small Y (CommonPrismRefinement.endpointCover Y V) ⟶
      small (TopCat.of (ClosedInterval × Y)) V :=
    PullbackPairCover.leftMap (X := Y) (Y := TopCat.of (ClosedInterval × Y))
      (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)
  let e₁ : small Y (CommonPrismRefinement.endpointCover Y V) ⟶
      small (TopCat.of (ClosedInterval × Y)) V :=
    PullbackPairCover.rightMap (X := Y) (Y := TopCat.of (ClosedInterval × Y))
      (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)
  have hs : (inclusion X U ⊗ₘ inclusion (TopCat.of (ClosedInterval × Y)) V) ≫
      before U V hU hcU hV hcV =
      (inclusion X U ⊗ₘ inclusion (TopCat.of (ClosedInterval × Y)) V) ≫
        after U V hU hcU hV hcV :=
    (SmallTensorCrossRetraction.cross_then_retract (X := X) (Y := TopCat.of (ClosedInterval × Y))
      U V hU hcU hV hcV).trans
      (SmallTensorCrossRetraction.factorwise (X := X) (Y := TopCat.of (ClosedInterval × Y))
        U V hU hcU hV hcV).symm
  have he₀ : endpoint U V 0 =
      (𝟙 (small X U) ⊗ₘ e₀) ≫ (inclusion X U ⊗ₘ inclusion (TopCat.of (ClosedInterval × Y)) V) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => inclusion X U ⊗ₘ f)
      (PullbackPairCover.leftMap_inclusion (X := Y) (Y := TopCat.of (ClosedInterval × Y))
        (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)).symm
  have he₁ : endpoint U V 1 =
      (𝟙 (small X U) ⊗ₘ e₁) ≫ (inclusion X U ⊗ₘ inclusion (TopCat.of (ClosedInterval × Y)) V) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => inclusion X U ⊗ₘ f)
      (PullbackPairCover.rightMap_inclusion (X := Y) (Y := TopCat.of (ClosedInterval × Y))
        (Z := TopCat.of (ClosedInterval × Y)) V V (AnnularTimeTrim.slice Y 0) (AnnularTimeTrim.slice Y 1)).symm
  constructor
  · rw [he₀, Category.assoc, Category.assoc, hs]
  · rw [he₁, Category.assoc, Category.assoc, hs]

variable {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)
  (u : ∀ q, (small (X ⊗ TopCat.of (ClosedInterval × Y))
    (SmallRectangleShuffle.rectangles U V)).X (d + q + 1) ⟶ E.X q)
  (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
    (small (X ⊗ TopCat.of (ClosedInterval × Y)) (SmallRectangleShuffle.rectangles U V)).d
      (d + q + 2) (d + q + 1) ≫ u q)
  (h₀ : ∀ q, (endpoint U V 0).f (d + q + 1) ≫
    (before U V hU hcU hV hcV).f (d + q + 1) ≫ u q = 0)
  (h₁ : ∀ q, (endpoint U V 1).f (d + q + 1) ≫
    (before U V hU hcU hV hcV).f (d + q + 1) ≫ u q = 0)

def cap (f : chains X ⊗ chains (TopCat.of (ClosedInterval × Y)) ⟶
    small (X ⊗ TopCat.of (ClosedInterval × Y)) (SmallRectangleShuffle.rectangles U V))
    (q : ℕ) := f.f (d + q + 1) ≫ u q

include hu in
theorem cap_comm (f : chains X ⊗ chains (TopCat.of (ClosedInterval × Y)) ⟶
    small (X ⊗ TopCat.of (ClosedInterval × Y)) (SmallRectangleShuffle.rectangles U V)) (q : ℕ) :
    cap U V d u f (q + 1) ≫ E.d (q + 1) q =
    (chains X ⊗ chains (TopCat.of (ClosedInterval × Y))).d (d + q + 2) (d + q + 1) ≫
      cap U V d u f q := by
  dsimp only [cap]
  rw [Category.assoc, hu, ← Category.assoc]
  change (f.f (d + q + 2) ≫ _ ) ≫ _ = _
  rw [f.comm, Category.assoc]

theorem after_endpoint_zero (t : ClosedInterval)
    (he : endpoint U V t ≫ before U V hU hcU hV hcV =
      endpoint U V t ≫ after U V hU hcU hV hcV)
    (hz : ∀ q, (endpoint U V t).f (d + q + 1) ≫
      (before U V hU hcU hV hcV).f (d + q + 1) ≫ u q = 0) (q : ℕ) :
    (endpoint U V t).f (d + q + 1) ≫ cap U V d u (after U V hU hcU hV hcV) q = 0 := by
  dsimp only [cap]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, ← he, HomologicalComplex.comp_f,
    Category.assoc, hz]

def beforeOperation : DegreeLoweringHomology.Map
    (small X U ⊗ small Y (CommonPrismRefinement.endpointCover Y V)) E d :=
  TimePrismDescent.operation (TensorTimePrismComparison.prism (X := X) (Y := Y) U V) d
    (cap U V d u (before U V hU hcU hV hcV))
    (cap_comm U V d u hu (before U V hU hcU hV hcV)) h₀ h₁

def afterOperation : DegreeLoweringHomology.Map
    (small X U ⊗ small Y (CommonPrismRefinement.endpointCover Y V)) E d :=
  TimePrismDescent.operation (TensorTimePrismComparison.prism (X := X) (Y := Y) U V) d
    (cap U V d u (after U V hU hcU hV hcV))
    (cap_comm U V d u hu (after U V hU hcU hV hcV))
    (after_endpoint_zero U V hU hcU hV hcV d u 0 (endpoints U V hU hcU hV hcV).1 h₀)
    (after_endpoint_zero U V hU hcU hV hcV d u 1 (endpoints U V hU hcU hV hcV).2 h₁)

theorem cycle_boundary (q : ℕ) :
    (small X U ⊗ small Y (CommonPrismRefinement.endpointCover Y V)).iCycles (d + q) ≫
      ((beforeOperation U V hU hcU hV hcV d u hu h₀ h₁).component q -
        (afterOperation U V hU hcU hV hcV d u hu h₀ h₁).component q) =
    ((small X U ⊗ small Y (CommonPrismRefinement.endpointCover Y V)).iCycles (d + q) ≫
      (TensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (d + q) (d + q + 1) ≫
      (FactorwiseSubdivisionComparison.comparison (X := X) (Y := TopCat.of (ClosedInterval × Y))
        U V hU hcU hV hcV).hom (d + q + 1) (d + q + 2) ≫ u (q + 1)) ≫ E.d (q + 1) q := by
  simpa only [beforeOperation, afterOperation, TimePrismDescent.operation,
    TimePrismDescent.component, cap, before, after, Category.assoc,
    Preadditive.comp_sub, Preadditive.sub_comp] using
    TensorTimePrismComparison.boundary (X := X) (Y := Y) U V hU hcU hV hcV d u hu q

theorem homology_eq (q : ℕ) :
    (beforeOperation U V hU hcU hV hcV d u hu h₀ h₁).homology q =
      (afterOperation U V hU hcU hV hcV d u hu h₀ h₁).homology q := by
  exact DegreeLoweringExact.homology_eq_of_cycle_boundary
    (beforeOperation U V hU hcU hV hcV d u hu h₀ h₁)
    (afterOperation U V hU hcU hV hcV d u hu h₀ h₁) q
    ((TensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (d + q) (d + q + 1) ≫
      (FactorwiseSubdivisionComparison.comparison (X := X) (Y := TopCat.of (ClosedInterval × Y))
        U V hU hcU hV hcV).hom (d + q + 1) (d + q + 2) ≫ u (q + 1))
    (cycle_boundary U V hU hcU hV hcV d u hu h₀ h₁ q)

end
end Finsler.CappedTensorTimeComparison
