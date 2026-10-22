module

public import Finsler.Loop.FirstInputRotationOriginalFactors
public import Finsler.Loop.CompactJoinCocycle
public import Finsler.Loop.OriginalFirstHalfCupOneCochains

/-! Actual canonical retained right cuts as a parameter family.
Their basepoints are exactly the original basepoints, so the genuine
normalized join cochain is the literal original join pullback. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfCutOutputJoinData

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CompactH1Alignment Finsler.H1FiberBase
open Finsler.H1SelfCutNeighborhood Finsler.CochainComparison Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (r : ℝ) (hr : r < 1)

def kept : C(CompactRotatedCutData.source α r, SphereLoop n) :=
  ⟨fun z => right (FirstInputRotationOriginalFactors.originalCut α r hr z),
    continuous_right.comp (FirstInputRotationOriginalFactors.originalCut α r hr).continuous⟩

theorem kept_basepoint (z : CompactRotatedCutData.source α r) :
    basepoint (kept α r hr z) = basepoint (α z.val.2) := basepoint_right _

def originalPair : TopCat.of (CompactRotatedCutData.source α r × Q) ⟶ TopCat.of (P × Q) :=
  TopCat.ofHom ⟨fun z => (z.1.val.2, z.2), by fun_prop⟩

def originalTime : TopCat.of (CompactRotatedCutData.source α r × Q) ⟶
    TopCat.of (ClosedInterval × (P × Q)) :=
  TopCat.ofHom ⟨fun z => (z.1.val.1, (z.1.val.2, z.2)), by fun_prop⟩

theorem evaluation_square : CompactJoinCocycle.evaluation (kept α r hr) β =
    originalPair α r (Q := Q) ≫ CompactJoinCocycle.evaluation α β := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  apply Prod.ext
  · apply Subtype.ext
    exact kept_basepoint α r hr z.1
  · rfl

theorem normalized_join_pullback (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) :
    CompactJoinCocycle.cocycle (kept α r hr) β hn hκ =
      cochainPullback (originalPair α r (Q := Q)) n (CompactJoinCocycle.cocycle α β hn hκ) := by
  rw [CompactJoinCocycle.cocycle, CompactJoinCocycle.cocycle, ← pullback_comp, evaluation_square]

theorem pair_gap (z : CompactRotatedCutData.source α r × Q) :
    dist (basepoint (kept α r hr z.1)) (basepoint (β z.2)) =
      dist (basepoint (α z.1.val.2)) (basepoint (β z.2)) := by
  rw [kept_basepoint]

theorem cut_pair_far_zero (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) :
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (CompactRotatedCutData.source α r × Q))
      (NearFarCapComparison.far (X := TopCat.of (CompactRotatedCutData.source α r)) (Y := TopCat.of Q)
        (fun z => basepoint (kept α r hr z)) (fun y => basepoint (β y)) κ)) n
      (CompactJoinCocycle.cocycle (kept α r hr) β hn hκ) = 0 :=
  CompactJoinCocycle.cocycle_far_zero (kept α r hr) β hn hκ

end
end Finsler.OriginalFirstHalfCutOutputJoinData
