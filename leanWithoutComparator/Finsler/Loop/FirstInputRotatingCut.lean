module

public import Finsler.Loop.CompactRotatedCutData
public import Finsler.Loop.FirstInputRotationFamily

/-! The genuine canonical tested and retained cuts during partial
first-input correction. The uniform compact cut-length control holds
on every later smaller join tube, so its radius can be combined with
other constraints before all tested data. -/

@[expose] public section
namespace Finsler.FirstInputRotatingCut

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1FiberBase Finsler.H1SelfCutNeighborhood Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)

def source : Set (ClosedInterval × CompactNearJoinParameters.tube α β R) :=
  {z | distance n (z.1, α z.2.val.1) ≤ r}

def dataMap (hR : R ≤ 1 / 2) :
    C(_root_.unitInterval × source α β R r, CompactRotatedCutData.data α r) := by
  have hcut (z : _root_.unitInterval × source α β R r) :
      (z.2.val.1, z.2.val.2.val.1) ∈ CompactRotatedCutData.source α r := z.2.property
  have hnear (z : _root_.unitInterval × source α β R r) :
      (z.1, (⟨(z.2.val.1, z.2.val.2.val.1), hcut z⟩, point (β z.2.val.2.val.2))) ∈
        CompactRotatedCutData.data α r := by
    change dist (basepoint (β z.2.val.2.val.2)) (basepoint (α z.2.val.2.val.1)) ≤ 1 / 2
    rw [dist_comm]
    exact z.2.val.2.property.trans hR
  refine ⟨fun z => ⟨(z.1, (⟨(z.2.val.1, z.2.val.2.val.1), hcut z⟩, point (β z.2.val.2.val.2))), hnear z⟩, ?_⟩
  have hc : Continuous (fun z : _root_.unitInterval × source α β R r =>
      (⟨(z.2.val.1, z.2.val.2.val.1), hcut z⟩ : CompactRotatedCutData.source α r)) := by fun_prop
  have hb : Continuous (fun z : _root_.unitInterval × source α β R r => point (β z.2.val.2.val.2)) :=
    continuous_point.comp (β.continuous.comp (show Continuous (fun z : _root_.unitInterval × source α β R r => z.2.val.2.val.2) by fun_prop))
  exact (continuous_fst.prodMk (hc.prodMk hb)).subtype_mk hnear

def rotation (hR : R ≤ 1 / 2) (hr : r < 1) :
    C(_root_.unitInterval × source α β R r, H1SelfCutNeighborhood.tube n) :=
  (CompactRotatedCutData.rotatingCut α r hr).comp (dataMap α β R r hR)

def original (hR : R ≤ 1 / 2) (hr : r < 1) : C(source α β R r, H1SelfCutNeighborhood.tube n) :=
  (CompactRotatedCutData.originalCut α r hr).comp
    ((dataMap α β R r hR).comp ⟨fun z => (0, z), continuous_const.prodMk continuous_id⟩)

theorem rotation_parameters (hR : R ≤ 1 / 2) (hr : r < 1) (hR1 : R < 1)
    (s : _root_.unitInterval) (z : source α β R r) :
    (rotation α β R r hR hr (s, z)).val =
      (z.val.1, FirstInputRotationFamily.family α β R hR1 (s, z.val.2)) := rfl

theorem original_parameters (hR : R ≤ 1 / 2) (hr : r < 1) (z : source α β R r) :
    (original α β R r hR hr z).val = (z.val.1, α z.val.2.val.1) := rfl

theorem rotation_zero (hR : R ≤ 1 / 2) (hr : r < 1) (z : source α β R r) :
    rotation α β R r hR hr (0, z) = original α β R r hR hr z := by
  apply Subtype.ext
  rw [rotation_parameters α β R r hR hr (hR.trans_lt (by norm_num)) 0 z, original_parameters,
    FirstInputRotationFamily.family_zero]

theorem exists_length_control [CompactSpace P] (hr : r < 1) (F : ReversibleMetric n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < ρ →
      ∀ (s : _root_.unitInterval) (z : source α β R r),
      |SobolevLength.length F (left (rotation α β R r hR hr (s, z))) -
        SobolevLength.length F (left (original α β R r hR hr z))| < ε ∧
      |SobolevLength.length F (right (rotation α β R r hR hr (s, z))) -
        SobolevLength.length F (right (original α β R r hR hr z))| < ε := by
  obtain ⟨ρ, hρ, hρ1, hbound⟩ := CompactRotatedCutData.exists_cut_length_control α r hr F hε
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro R hR hRρ s z
  have hz : CompactRotatedCutData.gap α r (dataMap α β R r hR (s, z)) < ρ := by
    change dist (basepoint (β z.val.2.val.2)) (basepoint (α z.val.2.val.1)) < ρ
    rw [dist_comm]
    exact z.val.2.property.trans_lt hRρ
  exact hbound (dataMap α β R r hR (s, z)) hz

end
end Finsler.FirstInputRotatingCut
