module

public import Finsler.Loop.FirstInputSelfCutCochains
public import Finsler.Loop.OriginalFirstHalfCutOutputJoinData
public import Finsler.Analysis.SelfCutLengthControl
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Compactness supplies one first-input metric scale before all
tested data. A nonzero proper cap then forces the retained length bound
on the whole parent, for any cochain with the actual tested-short support. -/

@[expose] public section
namespace Finsler.CompactSingleCutLengthOscillation

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.H1SelfCutNeighborhood
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P : Type} [PseudoMetricSpace P] {n : ℕ}
  (α : C(P, SphereLoop n)) (r : ℝ) (hr : r < 1) (F : ReversibleMetric n)

theorem cap_witness (L : ℝ) (d q : ℕ)
    (φ : singularCochainGroup (ZMod 2) (TopCat.of (CompactRotatedCutData.source α r)) d)
    (hφ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (CompactRotatedCutData.source α r))
      (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) d φ = 0)
    (σ : TopCat.toSSet.obj (TopCat.of (CompactRotatedCutData.source α r)) _⦋d + q⦌)
    (hnz : (TopCat.toSSet.obj (TopCat.of (CompactRotatedCutData.source α r))).ιChainComplex σ ≫
      absoluteChain (TopCat.of (CompactRotatedCutData.source α r)) d q (d + q) rfl φ ≠ 0) :
    ∃ w ∈ Set.range ((TopCat.of (CompactRotatedCutData.source α r)).toSSetObjEquiv _ σ),
      L ≤ SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr w) := by
  classical
  by_contra h
  push Not at h
  apply hnz
  apply SupportedCap.cap_zero_on_simplex _ _ d q _ rfl φ hφ σ
  intro z hz
  exact h z hz

theorem exists_scale [CompactSpace P] {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧ ∀ (c : ClosedInterval × P) (z w : CompactRotatedCutData.source α r),
      z.val ∈ Metric.ball c η → w.val ∈ Metric.ball c η →
      |SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr z) -
        SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr w)| < ε := by
  letI := CompactRotatedCutData.source_compactSpace α r
  have hc : Continuous (fun z : CompactRotatedCutData.source α r =>
      SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr z)) :=
    (SelfCutOscillation.continuous_length F).comp
      (FirstInputRotationOriginalFactors.originalTester α r hr).hom.continuous
  obtain ⟨δ, hδ, hstep⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  refine ⟨min (δ / 2) b, lt_min (half_pos hδ) hb, min_le_right _ _, ?_⟩
  intro c z w hz hw
  have hd : dist z w < δ := by
    change dist z.val w.val < δ
    have hz' : dist z.val c < min (δ / 2) b := hz
    have hw' : dist c w.val < min (δ / 2) b := by
      have hw₀ : dist w.val c < min (δ / 2) b := hw
      rw [dist_comm] at hw₀
      exact hw₀
    have hh := lt_of_le_of_lt (dist_triangle z.val c w.val) (add_lt_add hz' hw')
    have hm := min_le_left (δ / 2) b
    linarith
  simpa only [Real.dist_eq] using hstep hd

theorem exists_parent_bound [CompactSpace P] {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧ ∀ (a L : ℝ) (d q : ℕ)
      (φ : singularCochainGroup (ZMod 2) (TopCat.of (CompactRotatedCutData.source α r)) d),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (CompactRotatedCutData.source α r))
        (TestedCupOneSupport.short F (FirstInputRotationOriginalFactors.originalTester α r hr) L)) d φ = 0 →
      ∀ (c : ClosedInterval × P)
        (σ : TopCat.toSSet.obj (TopCat.of (CompactRotatedCutData.source α r)) _⦋d + q⦌),
      (∀ z ∈ Set.range ((TopCat.of (CompactRotatedCutData.source α r)).toSSetObjEquiv _ σ), z.val ∈ Metric.ball c η) →
      (TopCat.toSSet.obj (TopCat.of (CompactRotatedCutData.source α r))).ιChainComplex σ ≫
        absoluteChain (TopCat.of (CompactRotatedCutData.source α r)) d q (d + q) rfl φ ≠ 0 →
      (∀ z ∈ Set.range ((TopCat.of (CompactRotatedCutData.source α r)).toSSetObjEquiv _ σ),
        SobolevLength.length F (α z.val.2) < a) →
      ∀ z ∈ Set.range ((TopCat.of (CompactRotatedCutData.source α r)).toSSetObjEquiv _ σ),
        SobolevLength.length F (OriginalFirstHalfCutOutputJoinData.kept α r hr z) < a - L + 3 * ε := by
  obtain ⟨η, hη, hηb, hosc⟩ := exists_scale α r hr F hε hb
  refine ⟨η, hη, hηb, ?_⟩
  intro a L d q φ hφ c σ hfine hnz hA z hz
  obtain ⟨w, hw, hL⟩ := cap_witness α r hr F L d q φ hφ σ hnz
  have htest : L - ε ≤ SobolevLength.length F (FirstInputRotationOriginalFactors.originalTester α r hr z) := by
    have hh := (abs_lt.mp (hosc c z w (hfine z hz) (hfine w hw))).1
    linarith
  apply SelfCutLengthControl.filtered_retained_lt F hε
    (FirstInputRotationOriginalFactors.originalCut α r hr z) _ (hA z hz) htest
  change SupportedSelfCut.distance n (z.val.1, α z.val.2) < SelfCutLengthControl.radius F hε
  exact z.property.trans_lt hradius

end
end Finsler.CompactSingleCutLengthOscillation
