module

public import Finsler.Topology.FullTensorTimePrism
public import Finsler.Topology.OriginalSecondHalfTensorTimeOperation
import all Finsler.Topology.OriginalSecondHalfTensorTimeOperation
import all Finsler.Topology.OriginalSecondHalfTimeOperation

/-! Construct the actual original second-input tensor-time operation
on all input chains. Its restriction to any common small input cover is
literally the previously constructed operation, in the same bounded
cut domain and the same retained-length sublevel. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfFullTensorOperation

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
  {ι : Type*} (W : ι → Set (P × (ClosedInterval × Q)))
  (hW : ∀ v, IsOpen (W v)) (hcW : ⋃ v, W v = Set.univ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (a p : ℕ)
  (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (s + 1))) p)
  (u : DegreeLoweringHomology.Map (small (TopCat.of (P × (ClosedInterval × Q))) W)
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + (s + 1) + p))
  (hu : ∀ q, u.component q ≫ (push (source α β K hK r hr F B)).f q =
    (inclusion (TopCat.of (P × (ClosedInterval × Q))) W).f (a + (s + 1) + p + q) ≫
      threeCap (TopCat.of (P × (ClosedInterval × Q))) a (s + 1) p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit (s + 1)
          (AnnularSelfCut.cocycle (s + 1) (by omega) h))
        (SelfCutParameterFamily.testedExtension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
          (fun _ => r) (fun _ => hr) PUnit.unit p T))



include hu in
theorem endpoint_zero (t : ClosedInterval)
    (ht : cochainPullback (SelfCutThomCocycle.atTime (s + 1) t) (s + 1)
      (AnnularSelfCut.cocycle (s + 1) (by omega) h) = 0) (q : ℕ) :
    (𝟙 (chains (TopCat.of P)) ⊗ₘ push (AnnularTimeTrim.slice (TopCat.of Q) t)).f
      ((a + s + p) + q + 1) ≫
      OriginalSecondHalfTensorTimeOperation.cap α β K hK r hr F B W hW hcW a p u q = 0 := by
  dsimp only [OriginalSecondHalfTensorTimeOperation.cap]
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    OriginalSecondHalfTensorTimeOperation.slice_cross, HomologicalComplex.comp_f, Category.assoc]
  rw [OriginalSecondHalfTimeOperation.endpoint_zero α β K hK r hr F B W hW hcW h a p J T u hu t ht q, comp_zero]

def operation : DegreeLoweringHomology.Map
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q))
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + s + p) :=
  TimePrismDescent.operation (FullTensorTimePrism.prism (TopCat.of P) (TopCat.of Q))
    (a + s + p) (OriginalSecondHalfTensorTimeOperation.cap α β K hK r hr F B W hW hcW a p u)
    (OriginalSecondHalfTensorTimeOperation.cap_comm α β K hK r hr F B W hW hcW a p u)
    (endpoint_zero α β K hK r hr F B W hW hcW h a p J T u hu 0 (AnnularSupportedCut.time_zero (s + 1) (by omega) h))
    (endpoint_zero α β K hK r hr F B W hW hcW h a p J T u hu 1 (AnnularSupportedCut.time_one (s + 1) (by omega) h))

def output : DegreeLoweringHomology.Map
    (chains (TopCat.of P) ⊗ chains (TopCat.of Q))
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1)))))
    (a + s + p) :=
  (operation α β K hK r hr F B W hW hcW h a p J T u hu).post (push (retained α β K hK r hr F B))

theorem small_component {ι' κ' : Type*} (U : ι' → Set P) (V : κ' → Set (ClosedInterval × Q)) (q : ℕ) :
    (OriginalSecondHalfTensorTimeOperation.output α β K hK r hr F B W hW hcW h a p J T u hu U V).component q =
    (inclusion (TopCat.of P) U ⊗ₘ
      inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)).f
      ((a + s + p) + q) ≫ (output α β K hK r hr F B W hW hcW h a p J T u hu).component q := by
  change (TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q) U V).hom
      ((a + s + p) + q) ((a + s + p) + q + 1) ≫
      OriginalSecondHalfTensorTimeOperation.cap α β K hK r hr F B W hW hcW a p u q ≫ _ =
    (inclusion (TopCat.of P) U ⊗ₘ
      inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)).f
      ((a + s + p) + q) ≫
    ((FullTensorTimePrism.prism (TopCat.of P) (TopCat.of Q)).hom
      ((a + s + p) + q) ((a + s + p) + q + 1) ≫
      OriginalSecondHalfTensorTimeOperation.cap α β K hK r hr F B W hW hcW a p u q) ≫ _
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ OriginalSecondHalfTensorTimeOperation.cap
      α β K hK r hr F B W hW hcW a p u q ≫
      (push (retained α β K hK r hr F B)).f q)
    (FullTensorTimePrism.small_restriction (X := TopCat.of P) (Y := TopCat.of Q)
      U V ((a + s + p) + q)).symm

theorem small_homology {ι' κ' : Type*} (U : ι' → Set P) (V : κ' → Set (ClosedInterval × Q)) (q : ℕ) :
    (OriginalSecondHalfTensorTimeOperation.output α β K hK r hr F B W hW hcW h a p J T u hu U V).homology q =
    HomologicalComplex.homologyMap (inclusion (TopCat.of P) U ⊗ₘ
      inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
      ((a + s + p) + q) ≫ (output α β K hK r hr F B W hW hcW h a p J T u hu).homology q := by
  rw [← DegreeLoweringHomology.Map.pre_homology]
  exact DegreeLoweringHomology.Map.homology_eq_of_components
    (OriginalSecondHalfTensorTimeOperation.output α β K hK r hr F B W hW hcW h a p J T u hu U V)
    ((output α β K hK r hr F B W hW hcW h a p J T u hu).pre (inclusion (TopCat.of P) U ⊗ₘ
      inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)))
    (small_component α β K hK r hr F B W hW hcW h a p J T u hu U V) q

end
end Finsler.OriginalSecondHalfFullTensorOperation
