module

public import Finsler.Topology.SmallTensorCrossRetraction
public import Finsler.Loop.FirstFactorTensorTimePrismComparison
public import Finsler.Topology.TimePrismDescent
public import Finsler.Topology.DegreeLoweringExact

/-! Construct both genuine capped first-input tensor-time operations. The actual
common endpoint cover makes both subdivision orders identical on each
endpoint. Their difference on cycles is an explicit boundary in the
same target complex, and hence their homology maps agree. -/

@[expose] public section
namespace Finsler.CappedFirstFactorTensorTimeComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {X Y : TopCat.{0}} {ι κ : Type*}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)

def before := SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫
  FactorwiseSubdivisionComparison.productRetraction
    (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hcU hV hcV

def after := FactorwiseSubdivisionComparison.factorwise
  (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hcU hV hcV

def endpoint (t : ClosedInterval) :=
  (inclusion X (CommonPrismRefinement.endpointCover X U) ≫ push (AnnularTimeTrim.slice X t)) ⊗ₘ
    inclusion Y V

theorem endpoints :
    endpoint U V 0 ≫ before U V hU hcU hV hcV = endpoint U V 0 ≫ after U V hU hcU hV hcV ∧
    endpoint U V 1 ≫ before U V hU hcU hV hcV = endpoint U V 1 ≫ after U V hU hcU hV hcV := by
  let e₀ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U :=
    PullbackPairCover.leftMap (X := X) (Y := TopCat.of (ClosedInterval × X))
      (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  let e₁ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U :=
    PullbackPairCover.rightMap (X := X) (Y := TopCat.of (ClosedInterval × X))
      (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  have hs : (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) ≫
      before U V hU hcU hV hcV =
      (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) ≫
        after U V hU hcU hV hcV :=
    (SmallTensorCrossRetraction.cross_then_retract (X := TopCat.of (ClosedInterval × X)) (Y := Y)
      U V hU hcU hV hcV).trans
      (SmallTensorCrossRetraction.factorwise (X := TopCat.of (ClosedInterval × X)) (Y := Y)
        U V hU hcU hV hcV).symm
  have he₀ : endpoint U V 0 =
      (e₀ ⊗ₘ 𝟙 (small Y V)) ≫ (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => f ⊗ₘ inclusion Y V)
      (PullbackPairCover.leftMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X))
        (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm
  have he₁ : endpoint U V 1 =
      (e₁ ⊗ₘ 𝟙 (small Y V)) ≫ (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun f => f ⊗ₘ inclusion Y V)
      (PullbackPairCover.rightMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X))
        (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm
  constructor
  · rw [he₀, Category.assoc, Category.assoc, hs]
  · rw [he₁, Category.assoc, Category.assoc, hs]

variable {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)
  (u : ∀ q, (small (TopCat.of (ClosedInterval × X) ⊗ Y)
    (SmallRectangleShuffle.rectangles U V)).X (d + q + 1) ⟶ E.X q)
  (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
    (small (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V)).d
      (d + q + 2) (d + q + 1) ≫ u q)
  (h₀ : ∀ q, (endpoint U V 0).f (d + q + 1) ≫
    (before U V hU hcU hV hcV).f (d + q + 1) ≫ u q = 0)
  (h₁ : ∀ q, (endpoint U V 1).f (d + q + 1) ≫
    (before U V hU hcU hV hcV).f (d + q + 1) ≫ u q = 0)

def cap (f : chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y ⟶
    small (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V))
    (q : ℕ) := f.f (d + q + 1) ≫ u q

include hu in
theorem cap_comm (f : chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y ⟶
    small (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V)) (q : ℕ) :
    cap U V d u f (q + 1) ≫ E.d (q + 1) q =
    (chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y).d (d + q + 2) (d + q + 1) ≫
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
    (small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V) E d :=
  TimePrismDescent.operation (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V) d
    (cap U V d u (before U V hU hcU hV hcV))
    (cap_comm U V d u hu (before U V hU hcU hV hcV)) h₀ h₁

def afterOperation : DegreeLoweringHomology.Map
    (small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V) E d :=
  TimePrismDescent.operation (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V) d
    (cap U V d u (after U V hU hcU hV hcV))
    (cap_comm U V d u hu (after U V hU hcU hV hcV))
    (after_endpoint_zero U V hU hcU hV hcV d u 0 (endpoints U V hU hcU hV hcV).1 h₀)
    (after_endpoint_zero U V hU hcU hV hcV d u 1 (endpoints U V hU hcU hV hcV).2 h₁)

theorem cycle_boundary (q : ℕ) :
    (small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V).iCycles (d + q) ≫
      ((beforeOperation U V hU hcU hV hcV d u hu h₀ h₁).component q -
        (afterOperation U V hU hcU hV hcV d u hu h₀ h₁).component q) =
    ((small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V).iCycles (d + q) ≫
      (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (d + q) (d + q + 1) ≫
      (FactorwiseSubdivisionComparison.comparison (X := TopCat.of (ClosedInterval × X)) (Y := Y)
        U V hU hcU hV hcV).hom (d + q + 1) (d + q + 2) ≫ u (q + 1)) ≫ E.d (q + 1) q := by
  simpa only [beforeOperation, afterOperation, TimePrismDescent.operation,
    TimePrismDescent.component, cap, before, after, Category.assoc,
    Preadditive.comp_sub, Preadditive.sub_comp] using
    FirstFactorTensorTimePrismComparison.boundary (X := X) (Y := Y) U V hU hcU hV hcV d u hu q

theorem homology_eq (q : ℕ) :
    (beforeOperation U V hU hcU hV hcV d u hu h₀ h₁).homology q =
      (afterOperation U V hU hcU hV hcV d u hu h₀ h₁).homology q := by
  exact DegreeLoweringExact.homology_eq_of_cycle_boundary
    (beforeOperation U V hU hcU hV hcV d u hu h₀ h₁)
    (afterOperation U V hU hcU hV hcV d u hu h₀ h₁) q
    ((FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (d + q) (d + q + 1) ≫
      (FactorwiseSubdivisionComparison.comparison (X := TopCat.of (ClosedInterval × X)) (Y := Y)
        U V hU hcU hV hcV).hom (d + q + 1) (d + q + 2) ≫ u (q + 1))
    (cycle_boundary U V hU hcU hV hcV d u hu h₀ h₁ q)

end
end Finsler.CappedFirstFactorTensorTimeComparison

