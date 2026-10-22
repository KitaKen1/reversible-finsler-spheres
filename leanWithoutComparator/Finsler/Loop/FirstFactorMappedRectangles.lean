module

public import Finsler.Loop.CappedFirstFactorTensorTimeComparison
public import Finsler.Topology.SmallRetractionComparison
public import Finsler.Topology.RelativeSmallRetraction

/-! Actual rectangular source covers mapped into a specified target
cover. On the common small time endpoints, target-after-map and both
factorwise subdivision orders agree as chain maps in that target. -/

@[expose] public section
namespace Finsler.FirstFactorMappedRectangles

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {X Y Z : TopCat.{0}} {ι κ μ : Type*}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)
  (W : μ → Set Z) (hW : ∀ i, IsOpen (W i)) (hcW : ⋃ i, W i = Set.univ)
  (f : TopCat.of (ClosedInterval × X) ⊗ Y ⟶ Z)
  (r : ι × κ → μ)
  (hf : ∀ c, Set.MapsTo f (SmallRectangleShuffle.rectangles U V c) (W (r c)))

def targetMap : small (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V) ⟶
    small Z W :=
  SmallRetractionComparison.map (SmallRectangleShuffle.rectangles U V) W f r hf

def coarse : chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y ⟶ small Z W :=
  SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫
    push f ≫ smallSingularRetraction (X := Z) coeff W hW hcW

def before : chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y ⟶ small Z W :=
  CappedFirstFactorTensorTimeComparison.before (X := X) (Y := Y) U V hU hcU hV hcV ≫ targetMap (X := X) (Y := Y) U V W f r hf

def after : chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y ⟶ small Z W :=
  CappedFirstFactorTensorTimeComparison.after (X := X) (Y := Y) U V hU hcU hV hcV ≫ targetMap (X := X) (Y := Y) U V W f r hf

theorem targetMap_small :
    inclusion (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V) ≫
      push f ≫ smallSingularRetraction (X := Z) coeff W hW hcW = targetMap (X := X) (Y := Y) U V W f r hf := by
  rw [← Category.assoc, ← SmallRetractionComparison.map_inclusion
    (SmallRectangleShuffle.rectangles U V) W f r hf, Category.assoc,
    ι_comp_smallSingularRetraction, Category.comp_id]
  rfl

theorem small_coarse :
    (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) ≫ coarse (X := X) (Y := Y) W hW hcW f =
      SmallRectangleCross.cross (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V ≫ targetMap (X := X) (Y := Y) U V W f r hf := by
  rw [coarse, ← Category.assoc, ← SmallRectangleCross.cross_inclusion, Category.assoc,
    targetMap_small (X := X) (Y := Y) U V W hW hcW f r hf]

theorem small_before :
    (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) ≫ before (X := X) (Y := Y) U V hU hcU hV hcV W f r hf =
      SmallRectangleCross.cross (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V ≫ targetMap (X := X) (Y := Y) U V W f r hf := by
  dsimp only [before, CappedFirstFactorTensorTimeComparison.before]
  rw [← Category.assoc, SmallTensorCrossRetraction.cross_then_retract (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hcU hV hcV]

theorem endpoint_equal :
    CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 0 ≫ coarse (X := X) (Y := Y) W hW hcW f =
      CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 0 ≫ before (X := X) (Y := Y) U V hU hcU hV hcV W f r hf ∧
    CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 1 ≫ coarse (X := X) (Y := Y) W hW hcW f =
      CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 1 ≫ before (X := X) (Y := Y) U V hU hcU hV hcV W f r hf := by
  let e₀ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U := PullbackPairCover.leftMap (X := X) (Y := TopCat.of (ClosedInterval × X))
    (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  let e₁ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U := PullbackPairCover.rightMap (X := X) (Y := TopCat.of (ClosedInterval × X))
    (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  have he₀ : CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 0 =
      (e₀ ⊗ₘ 𝟙 (small Y V)) ≫ (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => z ⊗ₘ inclusion Y V)
      (PullbackPairCover.leftMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X))
        (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm
  have he₁ : CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 1 =
      (e₁ ⊗ₘ 𝟙 (small Y V)) ≫ (inclusion (TopCat.of (ClosedInterval × X)) U ⊗ₘ inclusion Y V) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun z => z ⊗ₘ inclusion Y V)
      (PullbackPairCover.rightMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X))
        (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm
  constructor
  · rw [he₀, Category.assoc, Category.assoc, small_coarse, small_before]
  · rw [he₁, Category.assoc, Category.assoc, small_coarse, small_before]

theorem exists_endpoint_lifts :
    ∃ e₀ e₁ : (small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V) ⟶
      small (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V),
      CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 0 ≫
        SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y = e₀ ≫
          inclusion (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V) ∧
      CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 1 ≫
        SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y = e₁ ≫
          inclusion (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles U V) := by
  let e₀ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U := PullbackPairCover.leftMap (X := X) (Y := TopCat.of (ClosedInterval × X))
    (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  let e₁ : small X (CommonPrismRefinement.endpointCover X U) ⟶
      small (TopCat.of (ClosedInterval × X)) U := PullbackPairCover.rightMap (X := X) (Y := TopCat.of (ClosedInterval × X))
    (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  refine ⟨(e₀ ⊗ₘ 𝟙 (small Y V)) ≫ SmallRectangleCross.cross (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V,
    (e₁ ⊗ₘ 𝟙 (small Y V)) ≫ SmallRectangleCross.cross (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V, ?_, ?_⟩
  · rw [Category.assoc, SmallRectangleCross.cross_inclusion, ← Category.assoc,
      tensorHom_comp_tensorHom, Category.id_comp]
    rw [PullbackPairCover.leftMap_inclusion]
    rfl
  · rw [Category.assoc, SmallRectangleCross.cross_inclusion, ← Category.assoc,
      tensorHom_comp_tensorHom, Category.id_comp]
    rw [PullbackPairCover.rightMap_inclusion]
    rfl

end
end Finsler.FirstFactorMappedRectangles
