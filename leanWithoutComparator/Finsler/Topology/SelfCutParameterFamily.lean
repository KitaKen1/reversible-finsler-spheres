module

public import Finsler.Topology.FiniteGuardedOscillation
public import Finsler.Topology.TubeTestWitness
public import Finsler.Analysis.SelfCutOscillation

/-! Actual self-cut and tested-loop maps on a compact outer parameter
tube. The outer map is only required on that genuine tube. Nonzero
zero-extended Thom/test evaluations supply the two witnesses needed for
the simultaneous whole-parent distance and length estimates. -/

@[expose] public section
namespace Finsler.SelfCutParameterFamily

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SobolevLength
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {ι : Type*} {n : ℕ}

def distanceValue (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (i : ι) : P × Q → ℝ :=
  TubeTestWitness.partialValue (X := TopCat.of (P × Q)) K (e i) (distance n)

def domain (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (r : ι → ℝ) (i : ι) :
    Set (P × Q) := K ∩ {z | distanceValue K e i z < r i}

def toCut (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (r : ι → ℝ) (i : ι) :
    TopCat.of (domain K e r i) ⟶ TopCat.of (neighborhood n (r i)) := by
  refine TopCat.ofHom ⟨fun z => ⟨e i ⟨z.val, z.property.1⟩, ?_⟩, ?_⟩
  · change distance n (e i ⟨z.val, z.property.1⟩) < r i
    have hz : distanceValue K e i z.val < r i := z.property.2
    rw [distanceValue, TubeTestWitness.partialValue, dite_eq_left z.property.1] at hz
    exact hz
  · have hc : Continuous (fun z : domain K e r i => e i ⟨z.val, z.property.1⟩) :=
      (e i).hom.continuous.comp (continuous_subtype_val.subtype_mk _)
    exact hc.subtype_mk _

def testedMap (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (r : ι → ℝ)
    (hr : ∀ i, r i ≤ 1) (i : ι) : TopCat.of (domain K e r i) ⟶ TopCat.of (SphereLoop n) :=
  toCut K e r i ≫ TopCat.ofHom (tested n (hr i))

def retainedMap (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (r : ι → ℝ)
    (hr : ∀ i, r i ≤ 1) (i : ι) : TopCat.of (domain K e r i) ⟶ TopCat.of (SphereLoop n) :=
  toCut K e r i ≫ TopCat.ofHom (retained n (hr i))

def testedValue (F : ReversibleMetric n) (K : Set (P × Q))
    (e : ι → (TopCat.of K ⟶ parameters n)) (r : ι → ℝ) (hr : ∀ i, r i ≤ 1) (i : ι) : P × Q → ℝ :=
  TubeTestWitness.partialValue (X := TopCat.of (P × Q)) (domain K e r i) (testedMap K e r hr i) (length F)

def thomExtension (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n))
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hn : 1 ≤ n) (i : ι) :
    singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) n :=
  TubeCochainExtension.extend (TopCat.of (P × Q)) K n
    (cochainPullback (e i) n (NormalizedSelfCut.cocycle n hn (hρ i)))

def testedExtension (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n))
    (r : ι → ℝ) (hr : ∀ i, r i ≤ 1) (i : ι) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) p :=
  TubeCochainExtension.extend (TopCat.of (P × Q)) (domain K e r i) p
    (cochainPullback (testedMap K e r hr i) p T)

theorem distance_continuousOn (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (i : ι) :
    ContinuousOn (distanceValue K e i) K :=
  TubeTestWitness.continuousOn_partialValue (X := TopCat.of (P × Q)) K (e i) (distance n) (continuous_distance n)

theorem guarded_subset_domain (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n))
    (r ρ : ι → ℝ) (hρr : ∀ i, 4 * ρ i < r i) (i : ι) :
    FiniteGuardedOscillation.guarded K (distanceValue K e i) (2 * ρ i) ⊆ domain K e r i := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hb := hz.2
  have hg := hρr i
  change distanceValue K e i z ≤ 2 * (2 * ρ i) at hb
  change distanceValue K e i z < r i
  linarith

theorem tested_continuousOn_guarded (F : ReversibleMetric n) (K : Set (P × Q))
    (e : ι → (TopCat.of K ⟶ parameters n)) (r ρ : ι → ℝ)
    (hr : ∀ i, r i ≤ 1) (hρr : ∀ i, 4 * ρ i < r i) (i : ι) :
    ContinuousOn (testedValue F K e r hr i)
      (FiniteGuardedOscillation.guarded K (distanceValue K e i) (2 * ρ i)) :=
  (TubeTestWitness.continuousOn_partialValue (X := TopCat.of (P × Q)) (domain K e r i) (testedMap K e r hr i)
    (length F) (SelfCutOscillation.continuous_length F)).mono (guarded_subset_domain K e r ρ hρr i)

theorem thom_witness (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n))
    (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hn : 1 ≤ n) (i : ι)
    (σ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋n⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ ≫
      thomExtension K e ρ hρ hn i ≠ 0) :
    ∃ z ∈ Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ), distanceValue K e i z ≤ ρ i := by
  let A : Set (parameters n) := {z | -distance n z < -(ρ i)}
  have he : A = exterior n (ρ i) := by
    ext z
    change -distance n z < -(ρ i) ↔ ρ i < distance n z
    constructor <;> intro h <;> linarith
  have hzero : cochainPullback (SupportedCap.subspaceMap (parameters n) A) n
      (NormalizedSelfCut.cocycle n hn (hρ i)) = 0 := by
    rw [he]
    exact NormalizedSelfCut.cocycle_supported n hn (hρ i)
  obtain ⟨hK, z, hz, hb⟩ := TubeTestWitness.extension_test_witness (X := TopCat.of (P × Q)) K (e i)
    (fun z => -distance n z) n (-(ρ i)) (NormalizedSelfCut.cocycle n hn (hρ i)) hzero σ hσ
  have hzK := hK hz
  refine ⟨z, hz, ?_⟩
  simp only [TubeTestWitness.partialValue, dite_eq_left hzK] at hb
  rw [distanceValue, TubeTestWitness.partialValue, dite_eq_left hzK]
  linarith

theorem tested_witness (F : ReversibleMetric n) (K : Set (P × Q))
    (e : ι → (TopCat.of K ⟶ parameters n)) (r : ι → ℝ) (hr : ∀ i, r i ≤ 1)
    (i : ι) (p : ℕ) (L : ℝ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0)
    (σ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋p⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ ≫ testedExtension K e r hr i p T ≠ 0) :
    ∃ z ∈ Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ), L ≤ testedValue F K e r hr i z :=
  (TubeTestWitness.extension_test_witness (X := TopCat.of (P × Q)) (domain K e r i) (testedMap K e r hr i)
    (length F) p L T hT σ hσ).2

end
end Finsler.SelfCutParameterFamily
