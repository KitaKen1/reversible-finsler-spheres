module

public import Finsler.Loop.NativeGHOptimalRate
public import Mathlib.Topology.Algebra.Order.Field

/-! Fekete-type convergence for the actual GH support levels. The already
proved finite-block remainder supplies the lower bound, so the full
subadditive machinery and an arbitrary endpoint choice are unnecessary. -/
@[expose] public section
namespace Finsler.NativeGHRateConvergence
open CategoryTheory AlgebraicTopology SphereOddDegree Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.NativeGHSpectralSupport Finsler.NativeGHOptimalRate
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)
include hm P v₀

theorem eventually_average_gt {l : ℝ} (hl : l < rate m F) :
    ∀ᶠ r : ℕ in atTop, l < average m F r := by
  let σ := (l + rate m F) / 2
  have hσ : l < σ := by dsimp [σ]; linarith
  have hσrate : σ < rate m F := by dsimp [σ]; linarith
  obtain ⟨C, hC, hlevel⟩ := exists_level_band m hm F P v₀ hσrate
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (σ - l))
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro r hr
  have hNr : (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hfrac : C / (σ - l) < (r : ℝ) + 1 := by linarith
  have hprod : C < ((r : ℝ) + 1) * (σ - l) :=
    (div_lt_iff₀ (sub_pos.mpr hσ)).mp hfrac
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 1)).2
  have h := hlevel r
  nlinarith

theorem average_tendsto : Tendsto (average m F) atTop (𝓝 (rate m F)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro l hl
    exact eventually_average_gt m hm F P v₀ hl
  · intro u hu
    exact Filter.Eventually.of_forall (fun r => (average_le_rate m hm F P v₀ r).trans_lt hu)

/-- No larger eventual linear support slope exists, regardless of the
fixed additive margin. This is optimality for GH powers, not full HR. -/
theorem slope_le_rate_of_level_band {σ C : ℝ}
    (h : ∀ᶠ r : ℕ in atTop, ((r : ℝ) + 1) * σ - C ≤ level m F r) :
    σ ≤ rate m F := by
  by_contra hbad
  have hpos : 0 < σ - rate m F := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (C / (σ - rate m F))
  obtain ⟨M, hM⟩ := eventually_atTop.1 h
  let r := max N M
  have hNr : (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast (le_max_left N M)
  have hR := hM r (le_max_right N M)
  have hupper := (div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ) + 1)).mp
    (average_le_rate m hm F P v₀ r)
  have hp : C < ((r : ℝ) + 1) * (σ - rate m F) :=
    (div_lt_iff₀ hpos).mp (by linarith)
  nlinarith

end
end Finsler.NativeGHRateConvergence
