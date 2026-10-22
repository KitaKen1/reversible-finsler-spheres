module

public import Finsler.Topology.OriginalSecondHalfFullTensorOperation
import all Finsler.Topology.OriginalSecondHalfFullTensorOperation
import all Finsler.Topology.OriginalSecondHalfTensorTimeOperation
public import Finsler.Topology.OriginalSecondHalfTensorHomology
import all Finsler.Topology.OriginalSecondHalfTensorHomology
import all Finsler.Topology.OriginalSecondHalfTimeOperation
public import Finsler.Topology.SuccAlignmentNaturality
public import Finsler.Topology.SmallTensorHomologyCancellation

/-! Remove the common small input refinements from the actual original
second-input tensor-time homology theorem. First identify the two literal
cap degree conventions. Then use the actual small-chain homology sections
in both factors, keeping the retained-length sublevel unchanged. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfFullTensorHomology

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000


variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]

variable {s : ℕ} (α : C(P, SphereLoop (s + 1))) (β : C(Q, SphereLoop (s + 1)))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (s + 1)) (B : ℝ)
  {ι κ : Type*} (U : ι → Set P) (V : κ → Set (ClosedInterval × Q))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (a p : ℕ)
  (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (s + 1))) p)
  (u : DegreeLoweringHomology.Map (small (TopCat.of (P × (ClosedInterval × Q))) (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V))
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + (s + 1) + p))
  (hu : ∀ q, u.component q ≫ (push (source α β K hK r hr F B)).f q =
    (inclusion (TopCat.of (P × (ClosedInterval × Q))) (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V)).f (a + (s + 1) + p + q) ≫
      threeCap (TopCat.of (P × (ClosedInterval × Q))) a (s + 1) p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit (s + 1)
          (AnnularSelfCut.cocycle (s + 1) (by omega) h))
        (SelfCutParameterFamily.testedExtension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
          (fun _ => r) (fun _ => hr) PUnit.unit p T))




def unrefined : DegreeLoweringHomology.Map
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q))
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1)))))
    (a + s + p) :=
  OriginalSecondHalfFullTensorOperation.output α β K hK r hr F B (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV) (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV) h a p J T u hu

theorem cap_normal (q : ℕ) :
    OriginalSecondHalfTensorTimeOperation.cap α β K hK r hr F B (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV) (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV) a p u q ≫
      (push (retained α β K hK r hr F B)).f q =
    (CappedTensorTimeComparison.before (X := TopCat.of P) (Y := TopCat.of Q) U V hU hcU hV hcV).f
      ((a + s + p) + q + 1) ≫ OriginalSecondHalfTensorHomology.outputCap α β K hK r hr F B U V a p u q := by
  have hc : ClosedCapDegreeTransport.align (a + s) p
      (OriginalSecondHalfTimeOperation.nested α β K hK r hr F B (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV) (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV) a p u) q =
      (FactorwiseSubdivisionComparison.productRetraction
        (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hcU hV hcV).f
        ((a + s + p) + q + 1) ≫ DegreeLoweringSuccAlignment.align (a + s + p) u (by omega) q :=
    SuccAlignmentNaturality.nested_pre
      (FactorwiseSubdivisionComparison.productRetraction
        (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hcU hV hcV) a s p u q
  simp only [OriginalSecondHalfTensorTimeOperation.cap, hc,
    CappedTensorTimeComparison.before, HomologicalComplex.comp_f,
    OriginalSecondHalfTensorHomology.outputCap, SuccAlignmentNaturality.post, Category.assoc]

theorem small_component (q : ℕ) :
    (OriginalSecondHalfTensorHomology.original α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).component q =
      (OriginalSecondHalfTensorTimeOperation.output α β K hK r hr F B (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV) (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV) h a p J T u hu U V).component q := by
  change (TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q) U V).hom
      ((a + s + p) + q) ((a + s + p) + q + 1) ≫
      ((CappedTensorTimeComparison.before (X := TopCat.of P) (Y := TopCat.of Q) U V hU hcU hV hcV).f
        ((a + s + p) + q + 1) ≫ OriginalSecondHalfTensorHomology.outputCap α β K hK r hr F B U V a p u q) =
    ((TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q) U V).hom
      ((a + s + p) + q) ((a + s + p) + q + 1) ≫
      OriginalSecondHalfTensorTimeOperation.cap α β K hK r hr F B (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV) (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV) a p u q) ≫
      (push (retained α β K hK r hr F B)).f q
  simpa only [Category.assoc] using congrArg
    (fun f => (TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q) U V).hom
      ((a + s + p) + q) ((a + s + p) + q + 1) ≫ f) (cap_normal α β K hK r hr F B U V hU hcU hV hcV a p u q).symm

theorem small_homology (q : ℕ) :
    (OriginalSecondHalfTensorHomology.original α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).homology q =
    homologyMap (inclusion (TopCat.of P) U ⊗ₘ
      inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
      ((a + s + p) + q) ≫ (unrefined α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).homology q := by
  exact (DegreeLoweringHomology.Map.homology_eq_of_components
    (OriginalSecondHalfTensorHomology.original α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu)
    (OriginalSecondHalfTensorTimeOperation.output α β K hK r hr F B (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV) (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV) h a p J T u hu U V)
    (small_component α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu) q).trans
    (OriginalSecondHalfFullTensorOperation.small_homology α β K hK r hr F B (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV) (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV) h a p J T u hu U V q)

theorem homology_zero (j k q : ℕ) (htotal : j + k = (a + s + p) + q)
    (hsmall : homologyCross (small (TopCat.of P) U)
      (small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
      j k ((a + s + p) + q) htotal ≫
        (OriginalSecondHalfTensorHomology.original α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).homology q = 0) :
    homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q))
      j k ((a + s + p) + q) htotal ≫ (unrefined α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).homology q = 0 := by
  exact SmallTensorHomologyCancellation.zero_of_small (X := TopCat.of P) (Y := TopCat.of Q)
    U (CommonPrismRefinement.endpointCover (TopCat.of Q) V) hU hcU
    (CommonPrismRefinement.endpointCover_open (TopCat.of Q) V hV)
    (CommonPrismRefinement.endpointCover_univ (TopCat.of Q) V hcV)
    (a + s + p) (unrefined α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu)
    (OriginalSecondHalfTensorHomology.original α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu)
    j k q htotal (small_homology α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu q) hsmall

end
end Finsler.OriginalSecondHalfFullTensorHomology
