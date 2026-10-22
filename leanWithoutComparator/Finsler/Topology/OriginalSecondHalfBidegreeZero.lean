module

public import Finsler.Topology.OriginalSecondHalfGlobalOperation
public import Finsler.Topology.SmallRectangleCrossSimplex

/-! Uniform normalized vanishing on the complete fixed-bidegree summand
of the actual factorwise-small cross product. The operation is a genuine
global closed bounded lift, rather than a separately postulated lift on
each product simplex. Identification with the original time retractions
is still a distinct requirement. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfBidegreeZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open HomologicalComplex
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors Finsler.SmallRectangleShuffle
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1)

theorem exists_scale (F : ReversibleMetric n) (hcompact : IsCompact K) (hn : 1 ≤ n)
    {δ ρ ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
    ∀ {ι κ : Type*} (U : ι → Set P) (V : κ → Set (ClosedInterval × Q))
      (cx : ι → P) (cy : κ → ClosedInterval × Q),
      (∀ i, U i ⊆ PairDistanceCover.cover id η (cx i)) →
      (∀ v, V v ⊆ PairDistanceCover.cover id η (cy v)) →
    ∀ (ρJ : ℝ),
      (∀ i, U i ⊆ PairDistanceCover.cover (fun x => basepoint (α x)) (ρJ / 4) (cx i)) →
      (∀ v, V v ⊆ PairDistanceCover.cover
        (fun y : ClosedInterval × Q => basepoint (β y.2)) (ρJ / 4) (cy v)) →
      (∀ z : P × (ClosedInterval × Q),
        dist (basepoint (α z.1)) (basepoint (β z.2.2)) < 2 * ρJ → z ∈ K) →
    ∀ (a p : ℕ) (L A : ℝ)
      (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
        (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) ρJ)) a J = 0 →
    ∀ (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : K, SobolevLength.length F (OriginalSecondHalfFamily.family α β K hK z).2 < A) →
    ∀ (C : DegreeLoweringHomology.Map
      (small (TopCat.of (P × (ClosedInterval × Q)))
        (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V))
      (chains (TopCat.of (bounded α β K hK r hr F (A - L + 3 * ε)))) (a + n + p)),
      (∀ q, C.component q ≫ (push (source α β K hK r hr F (A - L + 3 * ε))).f q =
        (inclusion (TopCat.of (P × (ClosedInterval × Q)))
          (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V)).f (a + n + p + q) ≫
        threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
          (SupportedSelfCutAdequacy.extension K
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
            (AnnularSelfCut.cocycle n hn h))
          (SelfCutParameterFamily.testedExtension K
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
            (fun _ => r) (fun _ => hr) PUnit.unit p T)) →
    ∀ (j k q : ℕ) (htotal : j + k = a + n + p + q), a + p < j →
      ιTensorObj (small (TopCat.of P) U) (small (TopCat.of (ClosedInterval × Q)) V)
        j k (a + n + p + q) htotal ≫
        (SmallRectangleCross.cross (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V).f
          (a + n + p + q) ≫ C.component q ≫
        (push (retained α β K hK r hr F (A - L + 3 * ε))).f q ≫
        (SingularNormalization.projector
          (TopCat.of ({γ | SobolevLength.length F γ < A - L + 3 * ε} : Set (SphereLoop n)))).f q = 0 := by
  obtain ⟨η, hη, hηb, hall⟩ := OriginalSecondHalfUniformVanishing.exists_scale
    α β K hK r hr F hcompact hn h hρr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro ι κ U V cx cy hU hV ρJ hUJ hVJ hTube a p L A J hJ T hT hA C hC j k q htotal hdegree
  apply SmallRectangleCrossSimplex.zero_of_models
    (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V (a + n + p + q) htotal
  intro σ τ
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff (TopCat.of P) U σ.val).mp σ.property
  obtain ⟨v, hv⟩ := (TopCat.mem_smallSingularSubcomplex_iff
    (TopCat.of (ClosedInterval × Q)) V τ.val).mp τ.property
  let G := SmallRectangleCrossSimplex.model (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V σ τ
  let W := (SSet.chainComplexMap G coeff).f (a + n + p + q) ≫ C.component q
  have hmap : SSet.chainComplexMap G coeff ≫
      inclusion (TopCat.of (P × (ClosedInterval × Q)))
        (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V) =
      SSet.chainComplexMap
        (ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ.val τ.val) coeff := by
    change SSet.chainComplexMap G coeff ≫
      SSet.chainComplexMap
        (((TopCat.of P) ⊗ (TopCat.of (ClosedInterval × Q))).smallSingularSubcomplex
          (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V)).ι coeff = _
    rw [← Functor.map_comp]
    exact congrArg (fun f => SSet.chainComplexMap f coeff)
      (SmallRectangleCrossSimplex.model_inclusion
        (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V σ τ)
  have hsource : W ≫ (push (source α β K hK r hr F (A - L + 3 * ε))).f q =
      OriginalSecondHalfUniformVanishing.rawComponent α β K hK r hr j k σ.val τ.val a p q hn h J T := by
    dsimp only [W, OriginalSecondHalfUniformVanishing.rawComponent]
    rw [Category.assoc, hC q, ← Category.assoc, ← HomologicalComplex.comp_f, hmap]
  have hz := hall j k σ.val τ.val (cx i) (cy v) (hi.trans (hU i)) (hv.trans (hV v))
    ρJ (hi.trans (hUJ i)) (hv.trans (hVJ v)) hTube a p q L A htotal hdegree J hJ T hT
    (fun z _ => hA z) W hsource
  simpa only [W, G, Category.assoc] using hz

end
end Finsler.OriginalSecondHalfBidegreeZero
