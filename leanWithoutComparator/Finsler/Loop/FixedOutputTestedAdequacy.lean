module

public import Finsler.Topology.CompactRectangleOscillation
public import Finsler.Topology.TubeTestWitness
public import Finsler.Analysis.SelfCutOscillation

/-! Uniform whole-parent filtering for a genuine tested map and an
independently specified fixed output. Any nonzero tested face in the
parent supplies the lower length bound, including block and skip faces. -/

@[expose] public section
namespace Finsler.FixedOutputTestedAdequacy

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exists_scale {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y] [CompactSpace X] [CompactSpace Y]
    {n : ℕ} (F : ReversibleMetric n) (tested output : C(X × Y, SphereLoop n))
    (budget : X × Y → ℝ) (C : ℝ)
    (hbudget : ∀ z, SobolevLength.length F (tested z) + SobolevLength.length F (output z) < budget z + C)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧ ∀ (cx : X) (cy : Y) (S : Set (X × Y)),
      S ⊆ PairDistanceCover.cover id η cx ×ˢ PairDistanceCover.cover id η cy →
      ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z ∈ S, budget z < A) →
      ∀ (τ : TopCat.toSSet.obj (TopCat.of (X × Y)) _⦋p⦌),
      Set.range ((TopCat.of (X × Y)).toSSetObjEquiv _ τ) ⊆ S →
      (TopCat.toSSet.obj (TopCat.of (X × Y))).ιChainComplex τ ≫ cochainPullback (TopCat.ofHom tested) p T ≠ 0 →
      ∀ z ∈ S, SobolevLength.length F (output z) < A - L + C + ε := by
  obtain ⟨η, hη, hηb, hosc⟩ := CompactRectangleOscillation.exists_rectangle_scale (X := X) (Y := Y) (ι := Unit)
    (Finset.univ : Finset Unit) (K := Set.univ) isCompact_univ
    (fun _ : Unit => fun z : X × Y => SobolevLength.length F (tested z))
    (fun _ _ => ((SelfCutOscillation.continuous_length F).comp tested.continuous).continuousOn) hε hb
  refine ⟨η, hη, hηb, ?_⟩
  intro cx cy S hrect p L A T hshort hA τ hτS hτ
  have hzero : cochainPullback (SupportedCap.subspaceMap (TopCat.of (X × Y))
      {z | SobolevLength.length F (tested z) < L}) p (cochainPullback (TopCat.ofHom tested) p T) = 0 :=
    pullback_support (X := TopCat.of (X × Y)) (Y := TopCat.of (SphereLoop n)) (TopCat.ofHom tested) _ (SelfCutOscillation.short F L) (fun _ hz => hz) p T hshort
  obtain ⟨w, hw, hnot⟩ := TubeTestWitness.nonzero_evaluation_witness (X := TopCat.of (X × Y))
    {z | SobolevLength.length F (tested z) < L} p (cochainPullback (TopCat.ofHom tested) p T) hzero τ hτ
  have hwS := hτS hw
  have hL : L ≤ SobolevLength.length F (tested w) := le_of_not_gt hnot
  intro z hz
  have ho := hosc cx cy () (Finset.mem_univ _) z.1 (hrect hz).1 w.1 (hrect hwS).1
    z.2 (hrect hz).2 w.2 (hrect hwS).2 (Set.mem_univ _) (Set.mem_univ _)
  have hlo := (abs_lt.mp ho).1
  have hB := hbudget z
  have hA' := hA z hz
  linarith

end
end Finsler.FixedOutputTestedAdequacy
