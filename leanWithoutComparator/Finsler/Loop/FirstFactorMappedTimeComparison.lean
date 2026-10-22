module

public import Finsler.Loop.FirstFactorMappedRectangles
public import Finsler.Topology.DegreeLoweringExact

/-! Postcompose both real refinement comparisons with one closed cap
in the fixed target. The original target retraction and the factorwise
source retractions give equal small-input time homology operations. -/

@[expose] public section
namespace Finsler.FirstFactorMappedTimeComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.FirstFactorMappedRectangles

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

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
  (h₀ : ∀ q, (CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 0).f (d + q + 1) ≫
    (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q = 0)
  (h₁ : ∀ q, (CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V 1).f (d + q + 1) ≫
    (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q = 0)

def mappedCap (q : ℕ) := (targetMap (X := X) (Y := Y) U V W f r hf).f (d + q + 1) ≫ u q

include hu in
theorem mappedCap_comm (q : ℕ) :
    mappedCap (X := X) (Y := Y) U V W f r hf d u (q + 1) ≫ E.d (q + 1) q =
    (small (TopCat.of (ClosedInterval × X) ⊗ Y) (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V)).d
      (d + q + 2) (d + q + 1) ≫ mappedCap (X := X) (Y := Y) U V W f r hf d u q := by
  dsimp only [mappedCap]
  rw [Category.assoc, hu, ← Category.assoc]
  change ((targetMap (X := X) (Y := Y) U V W f r hf).f (d + q + 2) ≫ _) ≫ _ = _
  rw [(targetMap (X := X) (Y := Y) U V W f r hf).comm, Category.assoc]

def coarseCap (q : ℕ) := (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q

include hu in
theorem coarseCap_comm (q : ℕ) :
    coarseCap (X := X) (Y := Y) W hW hcW f d u (q + 1) ≫ E.d (q + 1) q =
    (chains (TopCat.of (ClosedInterval × X)) ⊗ chains Y).d
      (d + q + 2) (d + q + 1) ≫ coarseCap (X := X) (Y := Y) W hW hcW f d u q := by
  dsimp only [coarseCap]
  rw [Category.assoc, hu, ← Category.assoc]
  change ((coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 2) ≫ _) ≫ _ = _
  rw [(coarse (X := X) (Y := Y) W hW hcW f).comm, Category.assoc]

theorem before_endpoint_zero (t : ClosedInterval)
    (he : CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V t ≫ coarse (X := X) (Y := Y) W hW hcW f =
      CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V t ≫ before (X := X) (Y := Y) U V hU hcU hV hcV W f r hf)
    (hz : ∀ q, (CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V t).f (d + q + 1) ≫
      (coarse (X := X) (Y := Y) W hW hcW f).f (d + q + 1) ≫ u q = 0) (q : ℕ) :
    (CappedFirstFactorTensorTimeComparison.endpoint (X := X) (Y := Y) U V t).f (d + q + 1) ≫
      (CappedFirstFactorTensorTimeComparison.before (X := X) (Y := Y) U V hU hcU hV hcV).f (d + q + 1) ≫
        mappedCap (X := X) (Y := Y) U V W f r hf d u q = 0 := by
  have hh := congrArg (fun k => k.f (d + q + 1) ≫ u q) he
  simpa only [HomologicalComplex.comp_f, before, mappedCap, Category.assoc, hz q] using hh.symm

def coarseOperation : DegreeLoweringHomology.Map
    (small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V) E d :=
  TimePrismDescent.operation (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V) d
    (coarseCap (X := X) (Y := Y) W hW hcW f d u) (coarseCap_comm (X := X) (Y := Y) W hW hcW f d u hu) h₀ h₁

def beforeOperation : DegreeLoweringHomology.Map
    (small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V) E d :=
  CappedFirstFactorTensorTimeComparison.beforeOperation (X := X) (Y := Y) U V hU hcU hV hcV d
    (mappedCap (X := X) (Y := Y) U V W f r hf d u) (mappedCap_comm (X := X) (Y := Y) U V W f r hf d u hu)
    (before_endpoint_zero (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u 0
      (endpoint_equal (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf).1 h₀)
    (before_endpoint_zero (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u 1
      (endpoint_equal (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf).2 h₁)

def afterOperation : DegreeLoweringHomology.Map
    (small X (CommonPrismRefinement.endpointCover X U) ⊗ small Y V) E d :=
  CappedFirstFactorTensorTimeComparison.afterOperation (X := X) (Y := Y) U V hU hcU hV hcV d
    (mappedCap (X := X) (Y := Y) U V W f r hf d u) (mappedCap_comm (X := X) (Y := Y) U V W f r hf d u hu)
    (before_endpoint_zero (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u 0
      (endpoint_equal (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf).1 h₀)
    (before_endpoint_zero (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u 1
      (endpoint_equal (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf).2 h₁)

theorem coarse_before_homology (q : ℕ) :
    (coarseOperation (X := X) (Y := Y) U V W hW hcW f d u hu h₀ h₁).homology q =
      (beforeOperation (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu h₀ h₁).homology q := by
  let H := (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).compRight
    (SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y)
  obtain ⟨e₀, e₁, he₀, he₁⟩ := exists_endpoint_lifts (X := X) (Y := Y) U V
  let J := SmallRetractionComparison.comparison (X := TopCat.of (ClosedInterval × X) ⊗ Y) (Y := Z) (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V) W
    (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hV)
    (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hcU hcV) hW hcW f r hf
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary _ _ q
    (H.hom (d + q) (d + q + 1) ≫ J.hom (d + q + 1) (d + q + 2) ≫ u (q + 1))
  have hh := RelativeSmallRetraction.prism_boundary (X := TopCat.of (ClosedInterval × X) ⊗ Y) (Y := Z) (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V) W
    (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hV)
    (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hcU hcV) hW hcW f r hf
    H e₀ e₁ he₀ he₁ d u hu q
  simpa only [coarseOperation, beforeOperation, TimePrismDescent.operation, TimePrismDescent.component,
    CappedFirstFactorTensorTimeComparison.beforeOperation, CappedFirstFactorTensorTimeComparison.cap,
    CappedFirstFactorTensorTimeComparison.before, coarseCap, coarse, mappedCap, targetMap,
    HomologicalComplex.comp_f, Homotopy.compRight_hom, FactorwiseSubdivisionComparison.productRetraction,
    H, J, Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp] using hh

theorem coarse_after_homology (q : ℕ) :
    (coarseOperation (X := X) (Y := Y) U V W hW hcW f d u hu h₀ h₁).homology q =
      (afterOperation (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu h₀ h₁).homology q := by
  exact (coarse_before_homology (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u hu h₀ h₁ q).trans
    (CappedFirstFactorTensorTimeComparison.homology_eq (X := X) (Y := Y) U V hU hcU hV hcV d
      (mappedCap (X := X) (Y := Y) U V W f r hf d u) (mappedCap_comm (X := X) (Y := Y) U V W f r hf d u hu)
      (before_endpoint_zero (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u 0
        (endpoint_equal (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf).1 h₀)
      (before_endpoint_zero (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf d u 1
        (endpoint_equal (X := X) (Y := Y) U V hU hcU hV hcV W hW hcW f r hf).2 h₁) q)

end
end Finsler.FirstFactorMappedTimeComparison
