module

public import Finsler.Topology.ThreeCapWholeRectangle
public import Finsler.Topology.BoundedProductSimplexLift

/-! Use actual nonzero supported three-cap witnesses to construct a
genuine bounded product-simplex cut-domain map. The common factor scale
is chosen before the two input degrees, the three cap degrees, all
cochains and length thresholds. No product-domain map is postulated. -/

@[expose] public section
namespace Finsler.ThreeCapBoundedProductDomain

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SobolevLength
open Finsler.SelfCutParameterFamily Finsler.ThreeCapBlockVanishing
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {ι : Type*} [Fintype ι]
  {n : ℕ} (F : ReversibleMetric n) (K : Set (P × Q)) (hK : IsCompact K)
  (e : ι → (TopCat.of K ⟶ parameters n)) (r ρ : ι → ℝ)
  (hr : ∀ i, r i ≤ 1) (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, 4 * ρ i < r i)
  {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b)
  (hradius : ∀ i, r i ≤ SelfCutLengthControl.radius F hε)

include hK hρ hρr hε hb hradius

theorem exists_uniform_lifts : ∃ η > 0, η ≤ b ∧
    ∀ (u v : ℕ) (σ : TopCat.toSSet.obj (TopCat.of P) _⦋u⦌)
      (τ : TopCat.toSSet.obj (TopCat.of Q) _⦋v⦌) (cx : P) (cy : Q),
      Set.range ((TopCat.of P).toSSetObjEquiv _ σ) ⊆ PairDistanceCover.cover id η cx →
      Set.range ((TopCat.of Q).toSSetObjEquiv _ τ) ⊆ PairDistanceCover.cover id η cy →
      ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of Q) σ τ ⊆ K →
      ∀ (i : ι) (j k p q : ℕ) (L A : ℝ)
      (J : singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) j)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n (ρ i))) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : K, z.val ∈ ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of Q) σ τ →
        length F (e i z).2 < A) →
      ∀ (z : ((Δ[u] : SSet.{0}) ⊗ Δ[v]) _⦋j + k + p + q⦌),
      (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex
        ((ProductSimplexCarrier.model (TopCat.of P) (TopCat.of Q) σ τ).app _ z) ≫
        threeCap (TopCat.of (P × Q)) j k p q J
          (SupportedSelfCutAdequacy.extension K e i k φ)
          (testedExtension K e r hr i p T) ≠ 0 →
      let D := domain K e r i
      let f := retainedMap K e r hr i
      let B : Set (TopCat.of (SphereLoop n)) := {γ | length F γ < A - L + 3 * ε}
      ∃ hgood : ∀ w ∈ ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of Q) σ τ,
          ∃ hw : w ∈ D, f ⟨w, hw⟩ ∈ B,
      ∃ G : ((Δ[u] : SSet.{0}) ⊗ Δ[v]) ⟶ TopCat.toSSet.obj
        (TopCat.of (PartialDoubleCapDomainFiltered.boundedDomain (TopCat.of (P × Q))
          (TopCat.of (SphereLoop n)) D f B)),
      (G ≫ TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of D)
        (PartialDoubleCapDomainFiltered.boundedDomain (TopCat.of (P × Q))
          (TopCat.of (SphereLoop n)) D f B)) ≫
        TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of (P × Q)) D) =
          ProductSimplexCarrier.model (TopCat.of P) (TopCat.of Q) σ τ) ∧
      (G ≫ TopCat.toSSet.map (PartialDoubleCapDomainFiltered.retained
        (TopCat.of (P × Q)) (TopCat.of (SphereLoop n)) D f B) ≫
        TopCat.toSSet.map (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) B) =
          BoundedProductSimplexLift.domain (TopCat.of P) (TopCat.of Q)
            (TopCat.of (SphereLoop n)) σ τ D f B hgood ≫ TopCat.toSSet.map f) := by
  obtain ⟨η, hη, hηb, had⟩ := ThreeCapWholeRectangle.exists_filtered_scale F K hK e r ρ
    hr hρ hρr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro u v σ τ cx cy hσ hτ hSK i j k p q L A J φ hφ T hT hA z hcap
  have hrect : ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of Q) σ τ ⊆
      PairDistanceCover.cover id η cx ×ˢ PairDistanceCover.cover id η cy := Set.prod_mono hσ hτ
  have hgood := had cx cy (ProductSimplexCarrier.rectangle (TopCat.of P) (TopCat.of Q) σ τ)
    hrect hSK i j k p q L A J φ hφ T hT hA
    ((ProductSimplexCarrier.model (TopCat.of P) (TopCat.of Q) σ τ).app _ z)
    (ProductSimplexCarrier.model_parent (TopCat.of P) (TopCat.of Q) σ τ _ z) hcap
  refine ⟨hgood, BoundedProductSimplexLift.toBounded (TopCat.of P) (TopCat.of Q)
    (TopCat.of (SphereLoop n)) σ τ _ _ _ hgood, ?_, ?_⟩
  · exact BoundedProductSimplexLift.source_inclusion _ _ _ _ _ _ _ _ _
  · exact BoundedProductSimplexLift.retained_inclusion _ _ _ _ _ _ _ _ _

end
end Finsler.ThreeCapBoundedProductDomain
