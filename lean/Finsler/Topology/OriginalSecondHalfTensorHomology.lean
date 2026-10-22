module

public import Finsler.Topology.CappedTensorTimeComparison
public import Finsler.Topology.DegreeLoweringSuccAlignment
public import Finsler.Topology.OriginalSecondHalfTensorTimeOperation
public import Finsler.Topology.BidegreeOperationFilling

/-! Close both actual tensor-time caps for the original supported
second-half operation. Exact endpoint diagrams supply the hypotheses,
and their homology maps agree inside the retained-length sublevel.
The proved fixed-bidegree normalized zero then kills the actual input
homology cross product, including output degree zero. Comparison with
the original full-time prism remains a separate obligation. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfTensorHomology

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


private theorem summand_reindex
    {K L D C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f₀ f₁ : K ⊗ L ⟶ D} (H : Homotopy f₀ f₁) (F : D ⟶ C)
    (j k N Ncap : ℕ) (ht : j + k = N) (hc : N + 1 = Ncap)
    {M : ModuleCat.{0} (ZMod 2)} (g : C.X Ncap ⟶ M)
    (hz : ιTensorObj K L j k (j + k) rfl ≫ H.hom (j + k) (j + k + 1) ≫
      F.f (j + k + 1) ≫ eqToHom (congrArg C.X (show j + k + 1 = Ncap by omega)) ≫ g = 0) :
    ιTensorObj K L j k N ht ≫ H.hom N (N + 1) ≫ F.f (N + 1) ≫
      eqToHom (congrArg C.X hc) ≫ g = 0 := by
  subst N
  exact hz

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



def outputCap (q : ℕ) :
    (small (TopCat.of (P × (ClosedInterval × Q)))
      (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V)).X
      ((a + s + p) + q + 1) ⟶
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))).X q :=
  DegreeLoweringSuccAlignment.align (a + s + p)
    (u.post (push (retained α β K hK r hr F B))) (by omega) q

theorem outputCap_comm (q : ℕ) :
    outputCap α β K hK r hr F B U V a p u (q + 1) ≫
      (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))).d (q + 1) q =
    (small (TopCat.of (P × (ClosedInterval × Q)))
      (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V)).d
      ((a + s + p) + q + 2) ((a + s + p) + q + 1) ≫ outputCap α β K hK r hr F B U V a p u q :=
  DegreeLoweringSuccAlignment.comm (a + s + p)
    (u.post (push (retained α β K hK r hr F B))) (by omega) q

include hu in
theorem endpoint_zero (t : ClosedInterval)
    (ht : cochainPullback (SelfCutThomCocycle.atTime (s + 1) t) (s + 1)
      (AnnularSelfCut.cocycle (s + 1) (by omega) h) = 0) (q : ℕ) :
    (CappedTensorTimeComparison.endpoint (X := TopCat.of P) (Y := TopCat.of Q) U V t).f ((a + s + p) + q + 1) ≫
      (CappedTensorTimeComparison.before (X := TopCat.of P) (Y := TopCat.of Q) U V hU hcU hV hcV).f ((a + s + p) + q + 1) ≫
        outputCap α β K hK r hr F B U V a p u q = 0 := by
  let W := SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V
  let f := push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t) ≫
    FactorwiseSubdivisionComparison.productRetraction (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
      U V hU hcU hV hcV
  haveI := OriginalSecondHalfCapUniqueness.source_mono α β K hK r hr F B q
  have hz := ThreeCapRetractionZero.after_retraction
    (X := TopCat.of (P × (ClosedInterval × Q))) W
    (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hU hV)
    (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V hcU hcV)
    (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) t)
    (OriginalSecondHalfEndpointZero.region (P := P) (Q := Q) t)
    (OriginalSecondHalfEndpointZero.face_region t) a (s + 1) p q J
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit (s + 1)
      (AnnularSelfCut.cocycle (s + 1) (by omega) h))
    (SelfCutParameterFamily.testedExtension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
      (fun _ => r) (fun _ => hr) PUnit.unit p T)
    (OriginalSecondHalfEndpointZero.thom_region α β K hK (by omega) h t ht)
    u (push (source α β K hK r hr F B)) (hu q)
  have hpost : f.f (a + (s + 1) + p + q) ≫
      (u.post (push (retained α β K hK r hr F B))).component q = 0 := by
    change f.f (a + (s + 1) + p + q) ≫ u.component q ≫ _ = 0
    have hz' : f.f (a + (s + 1) + p + q) ≫ u.component q = 0 := hz
    rw [← Category.assoc, hz', zero_comp]
  have hzero := DegreeLoweringSuccAlignment.pre_zero (a + s + p)
    (u.post (push (retained α β K hK r hr F B))) (by omega) f q hpost
  have hi : (inclusion (TopCat.of P) U ⊗ₘ
      inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)) ≫
      (𝟙 (chains (TopCat.of P)) ⊗ₘ push (AnnularTimeTrim.slice (TopCat.of Q) t)) =
      CappedTensorTimeComparison.endpoint (X := TopCat.of P) (Y := TopCat.of Q) U V t := by
    rw [tensorHom_comp_tensorHom, Category.comp_id]
    rfl
  have hf : CappedTensorTimeComparison.endpoint (X := TopCat.of P) (Y := TopCat.of Q) U V t ≫
      CappedTensorTimeComparison.before (X := TopCat.of P) (Y := TopCat.of Q) U V hU hcU hV hcV =
      (inclusion (TopCat.of P) U ⊗ₘ
        inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)) ≫
      SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q) ≫ f := by
    dsimp only [CappedTensorTimeComparison.before]
    rw [← hi]
    simpa only [f, Category.assoc] using congrArg
      (fun g => (inclusion (TopCat.of P) U ⊗ₘ
        inclusion (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)) ≫ g ≫
        FactorwiseSubdivisionComparison.productRetraction (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          U V hU hcU hV hcV)
      (OriginalSecondHalfTensorTimeOperation.slice_cross (P := P) (Q := Q) t)
  rw [← Category.assoc, ← HomologicalComplex.comp_f, hf]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  change _ ≫ _ ≫ (f.f ((a + s + p) + q + 1) ≫
    DegreeLoweringSuccAlignment.align (a + s + p)
      (u.post (push (retained α β K hK r hr F B))) (by omega) q) = 0
  rw [hzero, comp_zero, comp_zero]

def original : DegreeLoweringHomology.Map
    (small (TopCat.of P) U ⊗
      small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1)))))
    (a + s + p) :=
  CappedTensorTimeComparison.beforeOperation (X := TopCat.of P) (Y := TopCat.of Q) U V hU hcU hV hcV (a + s + p)
    (outputCap α β K hK r hr F B U V a p u) (outputCap_comm α β K hK r hr F B U V a p u)
    (endpoint_zero α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu 0 (AnnularSupportedCut.time_zero (s + 1) (by omega) h))
    (endpoint_zero α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu 1 (AnnularSupportedCut.time_one (s + 1) (by omega) h))

def factorwiseOperation : DegreeLoweringHomology.Map
    (small (TopCat.of P) U ⊗
      small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
    (chains (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1)))))
    (a + s + p) :=
  CappedTensorTimeComparison.afterOperation (X := TopCat.of P) (Y := TopCat.of Q) U V hU hcU hV hcV (a + s + p)
    (outputCap α β K hK r hr F B U V a p u) (outputCap_comm α β K hK r hr F B U V a p u)
    (endpoint_zero α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu 0 (AnnularSupportedCut.time_zero (s + 1) (by omega) h))
    (endpoint_zero α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu 1 (AnnularSupportedCut.time_one (s + 1) (by omega) h))

theorem homology_eq (q : ℕ) :
    (original α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).homology q = (factorwiseOperation α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).homology q :=
  CappedTensorTimeComparison.homology_eq (X := TopCat.of P) (Y := TopCat.of Q) U V hU hcU hV hcV (a + s + p)
    (outputCap α β K hK r hr F B U V a p u) (outputCap_comm α β K hK r hr F B U V a p u)
    (endpoint_zero α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu 0 (AnnularSupportedCut.time_zero (s + 1) (by omega) h))
    (endpoint_zero α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu 1 (AnnularSupportedCut.time_one (s + 1) (by omega) h)) q

variable (hvan : ∀ (j k q : ℕ) (htotal : j + k + 1 = a + (s + 1) + p + q), a + p < j →
  ιTensorObj (small (TopCat.of P) U)
    (small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)) j k (j + k) rfl ≫
    (TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q) U V).hom (j + k) (j + k + 1) ≫
    (FactorwiseSubdivisionComparison.factorwise (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
      U V hU hcU hV hcV).f (j + k + 1) ≫
    eqToHom (congrArg (small (TopCat.of (P × (ClosedInterval × Q)))
      (SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V)).X htotal) ≫
    u.component q ≫ (push (retained α β K hK r hr F B)).f q ≫
      (SingularNormalization.projector
        (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))).f q = 0)

include hvan in
theorem factorwise_normalized_zero (j k q : ℕ) (htotal : j + k = (a + s + p) + q) (hdegree : a + p < j) :
    ιTensorObj (small (TopCat.of P) U)
      (small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
      j k ((a + s + p) + q) htotal ≫
    (factorwiseOperation α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).component q ≫
      (SingularNormalization.projector
        (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))).f q = 0 := by
  have hz := summand_reindex
    (TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q) U V)
    (FactorwiseSubdivisionComparison.factorwise (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
      U V hU hcU hV hcV) j k ((a + s + p) + q) (a + (s + 1) + p + q) htotal (by omega)
    (u.component q ≫ (push (retained α β K hK r hr F B)).f q ≫
      (SingularNormalization.projector
        (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))).f q)
    (hvan j k q (by omega) hdegree)
  simpa only [factorwiseOperation, CappedTensorTimeComparison.afterOperation,
    TimePrismDescent.operation, TimePrismDescent.component, CappedTensorTimeComparison.cap,
    CappedTensorTimeComparison.after, outputCap, DegreeLoweringSuccAlignment.align,
    DegreeLoweringHomology.Map.post, Category.assoc] using hz

include hvan in
theorem homology_zero (j k q : ℕ) (htotal : j + k = (a + s + p) + q) (hdegree : a + p < j) :
    HomologicalComplex.homologyCross (small (TopCat.of P) U)
      (small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V))
      j k ((a + s + p) + q) htotal ≫ (original α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu).homology q = 0 := by
  rw [homology_eq α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu]
  have hz := BidegreeOperationFilling.homology_zero
    (TopCat.of ({γ | SobolevLength.length F γ < B} : Set (SphereLoop (s + 1))))
    (𝟙 (small (TopCat.of P) U ⊗
      small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q) V)))
    (factorwiseOperation α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu) j k q htotal
    (by
      erw [HomologicalComplex.id_f, Category.id_comp]
      exact factorwise_normalized_zero α β K hK r hr F B U V hU hcU hV hcV h a p J T u hu hvan j k q htotal hdegree)
  erw [HomologicalComplex.homologyMap_id, Category.id_comp] at hz
  exact hz

end
end Finsler.OriginalSecondHalfTensorHomology
