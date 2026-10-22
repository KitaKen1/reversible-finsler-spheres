module

public import Finsler.Loop.NativeBVFixedShift
public import Finsler.Loop.NativeGHRateConvergence

/-! The SAME original Theta and GH towers have one positive asymptotic
rate. The fixed BV shift also gives the exact-slope ONE-SIDED bound
t_r <= (r+2) beta. A bounded lower deviation at beta is not inferred
from convergence or from the inter-tower gap. -/
@[expose] public section
namespace Finsler.NativeThetaGHCommonRate
open CategoryTheory AlgebraicTopology SphereOddDegree Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def average (r : ℕ) : ℝ :=
  NativeThetaSpectralLength.level m hm F P v₀ r / ((r : ℝ) + 1)

include hm P v₀ in
theorem gh_level_upper (r : ℕ) : NativeGHSpectralSupport.level m F r ≤
    ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F := by
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 1)).mp
    (NativeGHOptimalRate.average_le_rate m hm F P v₀ r)
  simpa only [mul_comm] using h

theorem theta_level_upper (r : ℕ) : NativeThetaSpectralLength.level m hm F P v₀ r ≤
    ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + NativeGHOptimalRate.rate m F := by
  have h := (NativeBVFixedShift.shift_one m hm F P v₀ r).trans
    (gh_level_upper m hm F P v₀ (r + 1))
  push_cast at h
  nlinarith

theorem theta_lift_above_line (r : ℕ) {a : ℝ}
    (ha : ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + NativeGHOptimalRate.rate m F < a) :
    a ∈ NativeThetaSpectralLength.lifts m hm F P v₀ r :=
  NativeThetaSpectralLength.lift_above m hm F P v₀ r
    ((theta_level_upper m hm F P v₀ r).trans_lt ha)

theorem common_level_band {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ,
    ((r : ℝ) + 1) * (NativeGHOptimalRate.rate m F - ε) - C ≤ NativeGHSpectralSupport.level m F r ∧
    NativeGHSpectralSupport.level m F r ≤ NativeThetaSpectralLength.level m hm F P v₀ r ∧
    NativeThetaSpectralLength.level m hm F P v₀ r ≤
      ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + NativeGHOptimalRate.rate m F := by
  obtain ⟨C, hC, h⟩ := NativeGHOptimalRate.exists_level_band m hm F P v₀
    (show NativeGHOptimalRate.rate m F - ε < NativeGHOptimalRate.rate m F by linarith)
  exact ⟨C, hC, fun r => ⟨h r, NativeThetaSpectralLength.gh_le_level m hm F P v₀ r,
    theta_level_upper m hm F P v₀ r⟩⟩

theorem average_eq (r : ℕ) : average m hm F P v₀ r = NativeGHOptimalRate.average m F r +
    NativeThetaGHSpectralGap.gap m hm F P v₀ r / ((r : ℝ) + 1) := by
  unfold average NativeGHOptimalRate.average NativeThetaGHSpectralGap.gap
  rw [← add_div]
  congr 1
  ring

theorem normalized_gap_tendsto_zero :
    Tendsto (fun r : ℕ => NativeThetaGHSpectralGap.gap m hm F P v₀ r / ((r : ℝ) + 1))
      atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall (NativeThetaGHSpectralGap.gap_nonneg m hm F P v₀))
    (Eventually.of_forall (NativeBVFixedShift.uniform_gap m hm F P v₀))
  exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

theorem average_tendsto : Tendsto (average m hm F P v₀) atTop (𝓝 (NativeGHOptimalRate.rate m F)) := by
  have h := (NativeGHRateConvergence.average_tendsto m hm F P v₀).add
    (normalized_gap_tendsto_zero m hm F P v₀)
  simpa only [add_zero, ← average_eq m hm F P v₀] using h

theorem common_positive_rate : 0 < NativeGHOptimalRate.rate m F ∧
    Tendsto (NativeGHOptimalRate.average m F) atTop (𝓝 (NativeGHOptimalRate.rate m F)) ∧
    Tendsto (average m hm F P v₀) atTop (𝓝 (NativeGHOptimalRate.rate m F)) :=
  ⟨NativeGHOptimalRate.rate_positive m hm F P v₀,
    NativeGHRateConvergence.average_tendsto m hm F P v₀, average_tendsto m hm F P v₀⟩

theorem rate_unique {β : ℝ} (h : Tendsto (average m hm F P v₀) atTop (𝓝 β)) :
    β = NativeGHOptimalRate.rate m F :=
  tendsto_nhds_unique h (average_tendsto m hm F P v₀)

theorem slope_le_rate_of_theta_band {σ C : ℝ}
    (h : ∀ᶠ r : ℕ in atTop,
      ((r : ℝ) + 1) * σ - C ≤ NativeThetaSpectralLength.level m hm F P v₀ r) :
    σ ≤ NativeGHOptimalRate.rate m F := by
  apply NativeGHRateConvergence.slope_le_rate_of_level_band m hm F P v₀
    (C := C + NativeThetaSpectralLength.level m hm F P v₀ 0)
  filter_upwards [h] with r hr
  have hg := NativeBVFixedShift.uniform_gap m hm F P v₀ r
  unfold NativeThetaGHSpectralGap.gap at hg
  linarith

end
end Finsler.NativeThetaGHCommonRate
