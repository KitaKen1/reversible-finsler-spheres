module

public import Finsler.Topology.SelfCutParameterFamily

/-! Simultaneous whole-parent self-cut adequacy for an actual finite
continuous family on a compact outer parameter tube. Choose the factor
scale before any cochain degree, threshold or representative. Nonzero
actual arbitrary far-supported and tested faces supply the witnesses, and the actual retained
loops have the additive length bound in every degree. Both cochain degrees and representatives follow the selected scale. Instantiating the
outer family with all original interchange homotopies remains separate. -/

@[expose] public section
namespace Finsler.SupportedSelfCutAdequacy

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SobolevLength
open Finsler.SelfCutParameterFamily Finsler.PairDistanceCover
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000


variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {ι : Type*} {n : ℕ}

def extension (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n)) (i : ι) (k : ℕ)
    (φ : singularCochainGroup (ZMod 2) (parameters n) k) :
    singularCochainGroup (ZMod 2) (TopCat.of (P × Q)) k :=
  TubeCochainExtension.extend (TopCat.of (P × Q)) K k (cochainPullback (e i) k φ)

theorem witness (K : Set (P × Q)) (e : ι → (TopCat.of K ⟶ parameters n))
    (ρ : ℝ) (i : ι) (k : ℕ) (φ : singularCochainGroup (ZMod 2) (parameters n) k)
    (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
    (σ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋k⦌)
    (hσ : (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ ≫ extension K e i k φ ≠ 0) :
    ∃ z ∈ Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ), distanceValue K e i z ≤ ρ := by
  let A : Set (parameters n) := {z | -distance n z < -ρ}
  have he : A = exterior n ρ := by
    ext z
    change -distance n z < -ρ ↔ ρ < distance n z
    constructor <;> intro h <;> linarith
  have hzero : cochainPullback (SupportedCap.subspaceMap (parameters n) A) k φ = 0 := by
    rw [he]
    exact hφ
  obtain ⟨hK, z, hz, hb⟩ := TubeTestWitness.extension_test_witness (X := TopCat.of (P × Q)) K (e i)
    (fun z => -distance n z) k (-ρ) φ hzero σ hσ
  have hzK := hK hz
  refine ⟨z, hz, ?_⟩
  simp only [TubeTestWitness.partialValue, dite_eq_left hzK] at hb
  rw [distanceValue, TubeTestWitness.partialValue, dite_eq_left hzK]
  linarith

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {ι : Type*} [Fintype ι]
  {n : ℕ} (F : ReversibleMetric n) (K : Set (P × Q)) (hK : IsCompact K)
  (e : ι → (TopCat.of K ⟶ parameters n)) (r ρ : ι → ℝ)
  (hr : ∀ i, r i ≤ 1) (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, 4 * ρ i < r i)
  {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)

include hK hρ hρr hε ha

theorem exists_scale : ∃ η > 0, η ≤ a ∧
    ∀ (cx : P) (cy : Q) (S : Set (P × Q)),
      S ⊆ cover id η cx ×ˢ cover id η cy → S ⊆ K →
      ∀ (i : ι) (k p : ℕ) (L : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n (ρ i))) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      ∀ (σ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋k⦌)
        (τ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋p⦌),
      Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ) ⊆ S →
      Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ τ) ⊆ S →
      (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ ≫ extension K e i k φ ≠ 0 →
      (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex τ ≫ testedExtension K e r hr i p T ≠ 0 →
      ∀ z ∈ S, z ∈ domain K e r i ∧ L - ε ≤ testedValue F K e r hr i z := by
  classical
  obtain ⟨η, hη, hηa, had⟩ := FiniteGuardedOscillation.exists_rectangle_adequacy Finset.univ hK
    (distanceValue K e) (testedValue F K e r hr) (fun i => 2 * ρ i)
    (fun i _ => mul_pos (by norm_num) (hρ i))
    (fun i _ => distance_continuousOn K e i)
    (fun i _ => tested_continuousOn_guarded F K e r ρ hr hρr i) hε ha
  refine ⟨η, hη, hηa, ?_⟩
  intro cx cy S hrect hSK i k p L φ hφ T hT σ τ hσS hτS hσ hτ
  obtain ⟨w, hw, hwd⟩ := witness K e (ρ i) i k φ hφ σ hσ
  have hwd' : distanceValue K e i w < 2 * ρ i := by linarith [hρ i]
  obtain ⟨hnear, hlower⟩ := had cx cy S hrect hSK i (Finset.mem_univ i) ⟨w, hσS hw, hwd'⟩
  obtain ⟨v, hv, hLv⟩ := tested_witness F K e r hr i p L T hT τ hτ
  intro z hz
  refine ⟨⟨hSK hz, ?_⟩, hlower L ⟨v, hτS hv, hLv⟩ z hz⟩
  have hd := hnear z hz
  have hg := hρr i
  change distanceValue K e i z < r i
  linarith

theorem exists_filtered_scale (hradius : ∀ i, r i ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ a ∧
    ∀ (cx : P) (cy : Q) (S : Set (P × Q)),
      S ⊆ cover id η cx ×ˢ cover id η cy → S ⊆ K →
      ∀ (i : ι) (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n (ρ i))) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : K, z.val ∈ S → length F (e i z).2 < A) →
      ∀ (σ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋k⦌)
        (τ : TopCat.toSSet.obj (TopCat.of (P × Q)) _⦋p⦌),
      Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ σ) ⊆ S →
      Set.range ((TopCat.of (P × Q)).toSSetObjEquiv _ τ) ⊆ S →
      (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex σ ≫ extension K e i k φ ≠ 0 →
      (TopCat.toSSet.obj (TopCat.of (P × Q))).ιChainComplex τ ≫ testedExtension K e r hr i p T ≠ 0 →
      ∀ z ∈ S, ∃ hz : z ∈ domain K e r i,
        length F (retainedMap K e r hr i ⟨z, hz⟩) < A - L + 3 * ε := by
  obtain ⟨η, hη, hηa, had⟩ := exists_scale F K hK e r ρ hr hρ hρr hε ha
  refine ⟨η, hη, hηa, ?_⟩
  intro cx cy S hrect hSK i k p L A φ hφ T hT hA σ τ hσS hτS hσ hτ z hzS
  obtain ⟨hz, htest⟩ := had cx cy S hrect hSK i k p L φ hφ T hT σ τ hσS hτS hσ hτ z hzS
  refine ⟨hz, ?_⟩
  have ht : L - ε ≤ length F (testedMap K e r hr i ⟨z, hz⟩) := by
    simpa only [testedValue, TubeTestWitness.partialValue, dite_eq_left hz] using htest
  exact SelfCutLengthControl.filtered_retained_lt F hε
    (toTube n (hr i) (toCut K e r i ⟨z, hz⟩))
    ((toCut K e r i ⟨z, hz⟩).property.trans_le (hradius i))
    (hA ⟨z, hz.1⟩ hzS) ht

end
end Finsler.SupportedSelfCutAdequacy
