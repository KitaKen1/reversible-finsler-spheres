module

public import Finsler.Loop.EmptySingularChains
public import Finsler.Loop.FirstInputSelfCutBoundedSpace

/-! Nonpositive individual length bounds make the actual bounded kept
carrier empty. Every genuine degree-lowering operation into its small
chains is literally zero, before taking homology and including degree
zero. A nonpositive beta bound likewise forces its parameter space empty. -/

@[expose] public section
namespace Finsler.BoundedCarrierEmpty

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (F : ReversibleMetric (m + 1)) (B : ℝ)

theorem bounded_empty (hB : B ≤ 0) : IsEmpty (FirstInputSelfCutBoundedSpace.bounded α r hr F B) := by
  refine ⟨fun z => ?_⟩
  have hp := (SobolevLength.length_nonneg F (FirstInputSelfCutBoundedSpace.retained α r hr F B z).val).trans_lt
    (FirstInputSelfCutBoundedSpace.retained α r hr F B z).property
  exact (not_lt_of_ge hB hp).elim

theorem small_zero {ι : Type*} (U : ι → Set (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)))
    (hB : B ≤ 0) (q : ℕ) :
    IsZero ((small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) U).X q) := by
  have := bounded_empty α r hr F B hB
  exact EmptySingularChains.small_zero _ U q

theorem component_zero {ι : Type*} (U : ι → Set (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)))
    {C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (op : DegreeLoweringHomology.Map C (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) U) d)
    (hB : B ≤ 0) (q : ℕ) : op.component q = 0 :=
  (small_zero α r hr F B U hB q).eq_of_tgt _ _

theorem homology_zero {ι : Type*} (U : ι → Set (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)))
    {C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (op : DegreeLoweringHomology.Map C (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) U) d)
    (hB : B ≤ 0) (q : ℕ) : op.homology q = 0 := by
  have hc : op.cycles q = 0 := by
    apply (cancel_mono ((small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) U).iCycles q)).mp
    rw [DegreeLoweringHomology.Map.cycles_i, component_zero α r hr F B U op hB q, comp_zero, zero_comp]
  apply (cancel_epi (C.homologyπ (d + q))).mp
  rw [DegreeLoweringHomology.Map.homologyπ_homology, hc, zero_comp, comp_zero]

theorem family_empty {Q : Type} [TopologicalSpace Q] {n : ℕ} (β : C(Q, SphereLoop n)) (F : ReversibleMetric n)
    {b : ℝ} (hβ : ∀ y, SobolevLength.length F (β y) < b) (hb : b ≤ 0) : IsEmpty Q :=
  ⟨fun y => (not_lt_of_ge hb ((SobolevLength.length_nonneg F (β y)).trans_lt (hβ y))).elim⟩

end
end Finsler.BoundedCarrierEmpty
