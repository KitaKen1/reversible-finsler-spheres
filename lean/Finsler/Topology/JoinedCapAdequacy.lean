module

public import Finsler.Topology.SequentialCapWitness
public import Finsler.Topology.JoinedComparisonAdequacy

/-! A nonzero actual successive far/test cap on a small whole parent
forces the actual retained-length bound throughout that parent for the
full joined cylinder and both trim homotopies. The original supported
cut and subdivision comparisons still have to be connected. -/

@[expose] public section
namespace Finsler.JoinedCapAdequacy

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.RelativeCapAssociativity Finsler.JoinedComparisonAdequacy
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}

theorem exists_filtered_scale (F : ReversibleMetric n)
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∀ (cx : ClosedInterval × ClosedInterval) (cy : X) (S : Set (Outer X)),
      S ⊆ PairDistanceCover.cover id η cx ×ˢ PairDistanceCover.cover id η cy →
      ∀ (i : Fin 3) (k p q : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z ∈ S, length F (u z.2).val.1 + length F (u z.2).val.2 < A) →
      ∀ (σ : TopCat.toSSet.obj (TopCat.of (Outer X)) _⦋k + (p + q)⦌),
      Set.range ((TopCat.of (Outer X)).toSSetObjEquiv _ σ) ⊆ S →
      (((TopCat.toSSet.obj (TopCat.of (Outer X))).ιChainComplex σ ≫
        absoluteChain (TopCat.of (Outer X)) k (p + q) (k + (p + q)) rfl
          (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)) ≫
        absoluteChain (TopCat.of (Outer X)) p q (p + q) rfl
          (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T)) ≠ 0 →
      ∀ z ∈ S, ∃ hz : z ∈ domain (tube X) (family u a ha ha1) (fun _ => r) i,
        length F (retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i ⟨z, hz⟩) <
          A - L + 3 * ε := by
  obtain ⟨η, hη, hηb, had⟩ := JoinedComparisonAdequacy.exists_filtered_scale F u a ha ha1
    hρ hρr hr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro cx cy S hrect i k p q L A φ hφ T hT hA σ hσS hcap z hzS
  have hw := SequentialCapWitness.sequential_nonzero_faces (TopCat.of (Outer X)) k p q
    (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
    (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T) σ hcap
  have hfaces := SequentialCapWitness.sequential_faces_range (TopCat.of (Outer X)) k p q σ
  exact had cx cy S hrect i k p L A φ hφ T hT hA
    (SequentialCapWitness.front (TopCat.of (Outer X)) k (p + q) σ)
    (SequentialCapWitness.front (TopCat.of (Outer X)) p q
      (SequentialCapWitness.back (TopCat.of (Outer X)) k (p + q) σ))
    (hfaces.1.trans hσS) (hfaces.2.trans hσS) hw.1 hw.2 z hzS

end
end Finsler.JoinedCapAdequacy
