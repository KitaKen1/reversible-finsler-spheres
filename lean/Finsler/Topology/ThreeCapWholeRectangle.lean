module

public import Finsler.Topology.ThreeCapBlockVanishing
public import Finsler.Topology.SupportedSelfCutAdequacy

/-! A nonzero original three-cap controls a whole source rectangle,
including points outside that particular shuffle simplex. The first
join cap is arbitrary. The actual cut and tested front faces provide
the two existing adequacy witnesses, so the chosen scale precedes all
degrees, cochains and length thresholds. -/

@[expose] public section
namespace Finsler.ThreeCapWholeRectangle

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SobolevLength
open Finsler.SelfCutParameterFamily Finsler.RelativeCapAssociativity
open Finsler.ThreeCapBlockVanishing
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem tail_nonzero (X : TopCat.{0}) (j k p q : ℕ)
    (J : singularCochainGroup (ZMod 2) X j)
    (φ : singularCochainGroup (ZMod 2) X k)
    (ψ : singularCochainGroup (ZMod 2) X p)
    (σ : TopCat.toSSet.obj X _⦋j + k + p + q⦌)
    (hn : (TopCat.toSSet.obj X).ιChainComplex σ ≫ threeCap X j k p q J φ ψ ≠ 0) :
    (((TopCat.toSSet.obj X).ιChainComplex
      (ThreeCapBlockVanishing.segment _ j (k + (p + q)) (by omega) σ) ≫
        absoluteChain X k (p + q) (k + (p + q)) rfl φ) ≫
          absoluteChain X p q (p + q) rfl ψ) ≠ 0 := by
  intro hz
  apply hn
  have he := congrArg (fun f => f ≫
    (absoluteChain X k (p + q) (k + (p + q)) rfl φ ≫
      absoluteChain X p q (p + q) rfl ψ))
    (SmallCapCarrier.cap_simplex X j (k + (p + q)) (j + k + p + q) (by omega) J σ)
  have he' : (TopCat.toSSet.obj X).ιChainComplex σ ≫ threeCap X j k p q J φ ψ =
      SmallCapCarrier.weight X j (k + (p + q)) (j + k + p + q) (by omega) J σ ≫
        (((TopCat.toSSet.obj X).ιChainComplex
          (ThreeCapBlockVanishing.segment _ j (k + (p + q)) (by omega) σ) ≫
            absoluteChain X k (p + q) (k + (p + q)) rfl φ) ≫
              absoluteChain X p q (p + q) rfl ψ) := by
    simpa only [threeCap, ThreeCapBlockVanishing.segment, Category.assoc] using he
  rw [he', hz, comp_zero]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {ι : Type*} [Fintype ι]
  {n : ℕ} (F : ReversibleMetric n) (K : Set (P × Q)) (hK : IsCompact K)
  (e : ι → (TopCat.of K ⟶ parameters n)) (r ρ : ι → ℝ)
  (hr : ∀ i, r i ≤ 1) (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, 4 * ρ i < r i)
  {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b)
  (hradius : ∀ i, r i ≤ SelfCutLengthControl.radius F hε)

include hK hρ hρr hε hb hradius

theorem exists_filtered_scale : ∃ η > 0, η ≤ b ∧
    ∀ (cx : P) (cy : Q) (S : Set (P × Q)),
      S ⊆ PairDistanceCover.cover id η cx ×ˢ PairDistanceCover.cover id η cy → S ⊆ K →
      ∀ (i : ι) (j k p q : ℕ) (L A : ℝ)
      (J : singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) j)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n (ρ i))) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : K, z.val ∈ S → length F (e i z).2 < A) →
      ∀ (σ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋j + k + p + q⦌),
      Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ) ⊆ S →
      (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ ≫
        threeCap (TopCat.of (P × Q)) j k p q J
          (SupportedSelfCutAdequacy.extension K e i k φ)
          (testedExtension K e r hr i p T) ≠ 0 →
      ∀ z ∈ S, ∃ hz : z ∈ domain K e r i,
        length F (retainedMap K e r hr i ⟨z, hz⟩) < A - L + 3 * ε := by
  obtain ⟨η, hη, hηb, had⟩ := SupportedSelfCutAdequacy.exists_filtered_scale F K hK e r ρ
    hr hρ hρr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro cx cy S hrect hSK i j k p q L A J φ hφ T hT hA σ hσS hcap
  let τ := ThreeCapBlockVanishing.segment (TopCat.toSSet.obj (TopCat.of (P × Q)))
    j (k + (p + q)) (by omega) σ
  have ht := tail_nonzero (TopCat.of (P × Q)) j k p q J _ _ σ hcap
  have hw := SequentialCapWitness.sequential_nonzero_faces (TopCat.of (P × Q)) k p q _ _ τ ht
  have hf := SequentialCapWitness.sequential_faces_range (TopCat.of (P × Q)) k p q τ
  have hτS : Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ τ) ⊆ S :=
    (SequentialCapWitness.simplex_map_range (TopCat.of (P × Q)) _ σ).trans hσS
  exact had cx cy S hrect hSK i k p L A φ hφ T hT hA _ _
    (hf.1.trans hτS) (hf.2.trans hτS) hw.1 hw.2

end
end Finsler.ThreeCapWholeRectangle
