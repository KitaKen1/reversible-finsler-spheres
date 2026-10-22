module

public import Finsler.Topology.OriginalSecondHalfCapUniqueness
public import Finsler.Topology.ThreeCapBoundedProductDomain
public import Finsler.Topology.ThreeCapJoinTube

/-! The actual original second-half supported three-cap has zero
normalized retained output on factorwise-small product simplices under
the original degree bound. No bounded product map is assumed: if the
raw component is nonzero, a genuine nonzero simplex supplies the whole
join tube and bounded cut-domain map. The zero case uses chain monicity.
Comparison with the original global source retractions remains separate. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfUniformVanishing

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1)

def rawComponent (j k : ℕ)
    (σ : TopCat.toSSet.obj (TopCat.of P) _⦋j⦌)
    (τ : TopCat.toSSet.obj (TopCat.of (ClosedInterval × Q)) _⦋k⦌)
    (a p q : ℕ) (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    (((Δ[j] : SSet.{0}) ⊗ Δ[k]).chainComplex coeff).X (a + n + p + q) ⟶
      (chains (TopCat.of (P × (ClosedInterval × Q)))).X q :=
  (SSet.chainComplexMap
    (ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ) coeff).f
    (a + n + p + q) ≫ threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
    (SupportedSelfCutAdequacy.extension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
      (AnnularSelfCut.cocycle n hn h))
    (SelfCutParameterFamily.testedExtension K
      (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
      (fun _ => r) (fun _ => hr) PUnit.unit p T)

theorem exists_scale (F : ReversibleMetric n) (hcompact : IsCompact K) (hn : 1 ≤ n)
    {δ ρ ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
    ∀ (j k : ℕ) (σ : TopCat.toSSet.obj (TopCat.of P) _⦋j⦌)
      (τ : TopCat.toSSet.obj (TopCat.of (ClosedInterval × Q)) _⦋k⦌) (cx : P) (cy : ClosedInterval × Q),
      Set.range ((TopCat.of P).toSSetObjEquiv _ σ) ⊆ PairDistanceCover.cover id η cx →
      Set.range ((TopCat.of (ClosedInterval × Q)).toSSetObjEquiv _ τ) ⊆ PairDistanceCover.cover id η cy →
    ∀ (ρJ : ℝ),
      Set.range ((TopCat.of P).toSSetObjEquiv _ σ) ⊆
        PairDistanceCover.cover (fun x => basepoint (α x)) (ρJ / 4) cx →
      Set.range ((TopCat.of (ClosedInterval × Q)).toSSetObjEquiv _ τ) ⊆
        PairDistanceCover.cover (fun y : ClosedInterval × Q => basepoint (β y.2)) (ρJ / 4) cy →
      (∀ z : P × (ClosedInterval × Q),
        dist (basepoint (α z.1)) (basepoint (β z.2.2)) < 2 * ρJ → z ∈ K) →
    ∀ (a p q : ℕ) (L A : ℝ), j + k = a + n + p + q → a + p < j →
    ∀ (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
        (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (fun x => basepoint (α x))
          (fun y : ClosedInterval × Q => basepoint (β y.2)) ρJ)) a J = 0 →
    ∀ (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : K, z.val ∈ ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ →
        SobolevLength.length F (OriginalSecondHalfFamily.family α β K hK z).2 < A) →
    ∀ (W : (((Δ[j] : SSet.{0}) ⊗ Δ[k]).chainComplex coeff).X (a + n + p + q) ⟶
      (chains (TopCat.of (bounded α β K hK r hr F (A - L + 3 * ε)))).X q),
      W ≫ (push (source α β K hK r hr F (A - L + 3 * ε))).f q =
        rawComponent α β K hK r hr j k σ τ a p q hn h J T →
      W ≫ (push (OriginalSecondHalfBoundedFactors.retained α β K hK r hr F (A - L + 3 * ε))).f q ≫
        (SingularNormalization.projector
          (TopCat.of ({γ | SobolevLength.length F γ < A - L + 3 * ε} : Set (SphereLoop n)))).f q = 0 := by
  obtain ⟨η, hη, hηb, hall⟩ := ThreeCapBoundedProductDomain.exists_uniform_lifts F K hcompact
    (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
    (fun _ => r) (fun _ => ρ) (fun _ => hr) (fun _ => h.1.trans h.2.2) (fun _ => hρr)
    hε hb (fun _ => hradius)
  refine ⟨η, hη, hηb, ?_⟩
  intro j k σ τ cx cy hσ hτ ρJ hσJ hτJ hTube a p q L A htotal hdegree J hJ T hT hA W hW
  let R := rawComponent α β K hK r hr j k σ τ a p q hn h J T
  change W ≫ (push (source α β K hK r hr F (A - L + 3 * ε))).f q = R at hW
  by_cases hR : R = 0
  · haveI := OriginalSecondHalfCapUniqueness.source_mono α β K hK r hr F (A - L + 3 * ε) q
    have hW0 : W = 0 := by
      apply (cancel_mono ((push (source α β K hK r hr F (A - L + 3 * ε))).f q)).mp
      rw [hW, hR, zero_comp]
    rw [hW0, zero_comp]
  · have hex : ∃ z : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) _⦋a + n + p + q⦌,
        ((Δ[j] : SSet.{0}) ⊗ Δ[k]).ιChainComplex (R := coeff) z ≫ R ≠ 0 := by
      classical
      by_contra hz
      push Not at hz
      apply hR
      apply SSet.chainComplex_hom_ext (X := ((Δ[j] : SSet.{0}) ⊗ Δ[k])) (R := coeff)
      intro z
      simpa only [comp_zero] using hz z
    obtain ⟨z, hz⟩ := hex
    dsimp only [R, rawComponent] at hz
    rw [SSet.ι_chainComplexMap_f_assoc] at hz
    have hrectJ : ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ ⊆
        PairDistanceCover.cover (fun x => basepoint (α x)) (ρJ / 4) cx ×ˢ
          PairDistanceCover.cover (fun y : ClosedInterval × Q => basepoint (β y.2)) (ρJ / 4) cy :=
      Set.prod_mono hσJ hτJ
    have hSK : ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ ⊆ K :=
      ThreeCapJoinTube.rectangle_in_tube (P := TopCat.of P) (Q := TopCat.of (ClosedInterval × Q))
      (E := Ambient n)
      (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2))
      ρJ cx cy (ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ) K
      hrectJ hTube a n p q J hJ _ _
      ((ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ).app _ z)
      (ProductSimplexCarrier.model_parent (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ _ z) hz
    obtain ⟨hgood, G, hsource, hout⟩ := hall j k σ τ cx cy hσ hτ hSK PUnit.unit a n p q L A J
      (AnnularSelfCut.cocycle n hn h) (AnnularSupportedCut.cocycle_supported n hn h) T hT hA z hz
    have hG : G ≫ TopCat.toSSet.map (source α β K hK r hr F (A - L + 3 * ε)) =
        ProductSimplexCarrier.model (TopCat.of P) (TopCat.of (ClosedInterval × Q)) σ τ := by
      simpa only [OriginalSecondHalfBoundedFactors.source, domainProjection, bounded, retainedCut,
        OriginalSecondHalfFamily.domain, OriginalSecondHalfFamily.cutMap,
        SelfCutParameterFamily.retainedMap, Functor.map_comp, Category.assoc] using hsource
    apply OriginalSecondHalfCapUniqueness.normalized_output_zero α β K hK r hr F (A - L + 3 * ε)
      j k σ τ G hG a p q htotal hdegree hn h J T W
    simpa only [R, rawComponent] using hW

end
end Finsler.OriginalSecondHalfUniformVanishing
