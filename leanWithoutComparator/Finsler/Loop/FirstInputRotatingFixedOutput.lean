module

public import Finsler.Loop.FirstInputRotatingCut
public import Finsler.Topology.FirstHalfFixedOutput
public import Finsler.Topology.JoinLengthComparison
public import Finsler.Analysis.SelfCutLengthControl

/-! Keep the corrected first retained loop joined to the original
second input fixed while the tested cut undergoes partial correction.
Compact cut-length continuity gives one uniform whole-point budget,
without an equivariance identity for short arcs. -/

@[expose] public section
namespace Finsler.FirstInputRotatingFixedOutput

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1FiberBase Finsler.H1SelfCutNeighborhood
open Finsler.H1LoopJoin Finsler.H1JoinContinuity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ) (hR : R ≤ 1 / 2) (hr : r < 1)

theorem rotation_one_basepoint (z : FirstInputRotatingCut.source α β R r) :
    basepoint (FirstInputRotatingCut.rotation α β R r hR hr (1, z)).val.2 = basepoint (β z.val.2.val.2) := by
  have hR1 : R < 1 := hR.trans_lt (by norm_num)
  change basepoint (FirstInputRotationFamily.family α β R hR1 (1, z.val.2)) = _
  rw [FirstInputRotationFamily.family_one]
  exact basepoint_align _ _

def endPair : C(FirstInputRotatingCut.source α β R r, H1JoinContinuity.composable n) := by
  let cut : C(FirstInputRotatingCut.source α β R r, H1SelfCutNeighborhood.tube n) :=
    (FirstInputRotatingCut.rotation α β R r hR hr).comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  let v : C(FirstInputRotatingCut.source α β R r, SphereLoop n) :=
    ⟨fun z => β z.val.2.val.2, by fun_prop⟩
  have hm (z : FirstInputRotatingCut.source α β R r) : basepoint (right (cut z)) = basepoint (v z) :=
    (basepoint_right _).trans (rotation_one_basepoint α β R r hR hr z)
  exact ⟨fun z => ⟨(right (cut z), v z), hm z⟩,
    ((continuous_right.comp cut.continuous).prodMk v.continuous).subtype_mk hm⟩

def output : C(FirstInputRotatingCut.source α β R r, SphereLoop n) :=
  (H1JoinContinuity.joinMap (1 / 2) (by norm_num) (by norm_num)).comp (endPair α β R r hR hr)

theorem length_output (F : ReversibleMetric n) (z : FirstInputRotatingCut.source α β R r) :
    SobolevLength.length F (output α β R r hR hr z) =
      SobolevLength.length F (right (FirstInputRotatingCut.rotation α β R r hR hr (1, z))) +
        SobolevLength.length F (β z.val.2.val.2) :=
  JoinLengthComparison.length_join F (1 / 2) (by norm_num) (by norm_num)
    (endPair α β R r hR hr z).val.1 (endPair α β R r hR hr z).val.2 (endPair α β R r hR hr z).property

def interiorInput :
    C({z : FirstInputRotatingCut.source α β R r | (z.val.1 : ℝ) < 1}, FirstHalfRetainedHomotopy.inputs n) := by
  let cut : C({z : FirstInputRotatingCut.source α β R r | (z.val.1 : ℝ) < 1}, H1SelfCutNeighborhood.tube n) :=
    (FirstInputRotatingCut.rotation α β R r hR hr).comp
      ⟨fun z => (1, z.val), continuous_const.prodMk continuous_subtype_val⟩
  let v : C({z : FirstInputRotatingCut.source α β R r | (z.val.1 : ℝ) < 1}, SphereLoop n) :=
    ⟨fun z => β z.val.val.2.val.2, by fun_prop⟩
  have hm (z : {z : FirstInputRotatingCut.source α β R r | (z.val.1 : ℝ) < 1}) :
      (cut z, v z) ∈ FirstHalfRetainedHomotopy.inputs n :=
    ⟨z.property, rotation_one_basepoint α β R r hR hr z.val⟩
  exact ⟨fun z => ⟨(cut z, v z), hm z⟩, (cut.continuous.prodMk v.continuous).subtype_mk hm⟩

theorem output_as_target (z : {z : FirstInputRotatingCut.source α β R r | (z.val.1 : ℝ) < 1}) :
    output α β R r hR hr z.val = FirstHalfRetainedHomotopy.targetMap (interiorInput α β R r hR hr z) := rfl

theorem exists_sum_bound [CompactSpace P] (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ ρ > 0, ρ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < ρ →
      ∀ (s : _root_.unitInterval) (z : FirstInputRotatingCut.source α β R r),
      SobolevLength.length F (left (FirstInputRotatingCut.rotation α β R r hR hr (s, z))) +
        SobolevLength.length F (output α β R r hR hr z) <
          SobolevLength.length F (α z.val.2.val.1) + SobolevLength.length F (β z.val.2.val.2) + 4 * ε := by
  obtain ⟨ρ, hρ, hρ1, hbound⟩ := FirstInputRotatingCut.exists_length_control α β r hr F hε
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro R hR hRρ s z
  have hl := (abs_lt.mp (hbound R hR hRρ s z).1).2
  have ht := (abs_lt.mp (hbound R hR hRρ 1 z).2).2
  have hd : ‖(endpoint (FirstInputRotatingCut.original α β R r hR hr z).val : Ambient n) -
      (point (FirstInputRotatingCut.original α β R r hR hr z).val.2 : Ambient n)‖ < SelfCutLengthControl.radius F hε :=
    z.property.trans_lt hradius
  have hs := (SelfCutLengthControl.radius_spec F hε).2.2 (FirstInputRotatingCut.original α β R r hR hr z) hd
  change SobolevLength.length F (left (FirstInputRotatingCut.original α β R r hR hr z)) +
    SobolevLength.length F (right (FirstInputRotatingCut.original α β R r hR hr z)) <
      SobolevLength.length F (α z.val.2.val.1) + 2 * ε at hs
  rw [length_output]
  linarith

theorem exists_filtered_bound [CompactSpace P] (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ ρ > 0, ρ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < ρ →
      ∀ (A L : ℝ) (s : _root_.unitInterval) (z : FirstInputRotatingCut.source α β R r),
      SobolevLength.length F (α z.val.2.val.1) + SobolevLength.length F (β z.val.2.val.2) < A →
      L - ε ≤ SobolevLength.length F (left (FirstInputRotatingCut.rotation α β R r hR hr (s, z))) →
      SobolevLength.length F (output α β R r hR hr z) < A - L + 5 * ε := by
  obtain ⟨ρ, hρ, hρ1, hbound⟩ := exists_sum_bound α β r hr F hε hradius
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro R hR hRρ A L s z hA htest
  have hb := hbound R hR hRρ s z
  linarith

end
end Finsler.FirstInputRotatingFixedOutput
