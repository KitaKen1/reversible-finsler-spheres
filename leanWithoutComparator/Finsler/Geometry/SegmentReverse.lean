module

public import Finsler.Geometry.SegmentContinuity

/-! Reversal of coordinate segments. The spray is even in the velocity, so the time reversal of a
coordinate geodesic is a coordinate geodesic; by uniqueness for the jet ODE it is the exp-data
geodesic with initial velocity −γ'(1), and when this velocity is inside the exp-data ball the
uniqueness of the local inverse identifies it with the segment from z to y. -/

@[expose] public section

namespace Finsler.SegmentReverse

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.EikonalChart
open Finsler.ExpInverseRegularity Finsler.ChartTransfer
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- The reversed segment from y to z is the segment from z to y. -/
theorem geo_reverse {y z : Coordinates n} (hy : y ∈ closedBall y₀ r) (hz : z ∈ closedBall y₀ r)
    (hyz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) (hsmall : ‖deriv (geo F D y z) 1‖ < D.ρ) :
    ∀ s ∈ Icc (0 : ℝ) 1, geo F D z y s = geo F D y z (1 - s) := by
  have hV := expInv_ne_zero D hy hyz.le hne
  have hVρ : ‖expInv D y z‖ < D.ρ := by
    have := norm_expInv_le D hy hyz.le
    linarith
  obtain ⟨hC, hT, hD, hA, -, -⟩ := geodesic_facts D hy hV hVρ
  have hC' : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (geo F D y z) t := hC
  have hT' : ∀ t ∈ Icc (0 : ℝ) 1, geo F D y z t ∈ (extChartAt (𝓡 n) p).target := hT
  have hD' : ∀ t ∈ Icc (0 : ℝ) 1, deriv (geo F D y z) t ≠ 0 := hD
  have hA' : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv (geo F D y z)) t =
      spray (coordinateLagrangian F p) (curveJet (geo F D y z) t) := hA
  have hend : geo F D y z 1 = z := geodesic_endpoint D hy hyz.le hne
  have hstart : geo F D y z 0 = y := by
    unfold geo scaledGeodesic
    rw [mul_zero, D.init]
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, 1 - s ∈ Icc (0 : ℝ) 1 :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  set x : ℝ → Coordinates n := fun s => geo F D y z (1 - s) with hxdef
  have hdx : deriv x = fun s => -deriv (geo F D y z) (1 - s) := by
    funext s
    rw [hxdef]
    exact deriv_comp_const_sub (f := geo F D y z) (a := (1 : ℝ)) (x := s)
  have hddx : ∀ s, deriv (deriv x) s = deriv (deriv (geo F D y z)) (1 - s) := by
    intro s
    rw [hdx]
    have hneg : (fun s => -deriv (geo F D y z) (1 - s)) =
        -(fun s => deriv (geo F D y z) (1 - s)) := rfl
    rw [hneg, deriv.neg, deriv_comp_const_sub (f := deriv (geo F D y z)) (a := (1 : ℝ)) (x := s),
      neg_neg]
  have hxC : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 x s := fun s hs =>
    (hC' (1 - s) (hmem s hs)).comp s (contDiffAt_const.sub contDiffAt_id)
  have hxT : ∀ s ∈ Icc (0 : ℝ) 1, x s ∈ (extChartAt (𝓡 n) p).target :=
    fun s hs => hT' _ (hmem s hs)
  have hxV : ∀ s ∈ Icc (0 : ℝ) 1, deriv x s ≠ 0 := by
    intro s hs
    rw [hdx, neg_ne_zero]
    exact hD' _ (hmem s hs)
  have hxA : ∀ s ∈ Icc (0 : ℝ) 1,
      deriv (deriv x) s = spray (coordinateLagrangian F p) (curveJet x s) := by
    intro s hs
    rw [hddx, hA' _ (hmem s hs)]
    have hj : curveJet x s = (geo F D y z (1 - s), (-1 : ℝ) • deriv (geo F D y z) (1 - s)) := by
      simp only [curveJet, hdx, neg_one_smul]
      rfl
    rw [hj, coordinate_spray_smul F p (hT' _ (hmem s hs)) (hD' _ (hmem s hs))
      (by norm_num : (-1 : ℝ) ≠ 0)]
    simp [curveJet]
  set v := deriv x 0 with hvdef
  have hv : v = -deriv (geo F D y z) 1 := by
    rw [hvdef, hdx]
    simp
  have hv0 : v ≠ 0 := hxV 0 (left_mem_Icc.mpr zero_le_one)
  have hvρ : ‖v‖ < D.ρ := by
    rw [hv, norm_neg]
    exact hsmall
  have hx0 : x 0 = z := by
    simp only [hxdef, sub_zero]
    exact hend
  have heq := eq_scaledGeodesic F D hz hv0 hvρ hxC hxT hxV hxA hx0 rfl
  -- the endpoint identifies v with the exp inverse from z to y
  have hzy : ‖y - z‖ ≤ D.ρ / 2 := by
    rw [norm_sub_rev]
    exact hyz.le
  have hexp : z + v + Finsler.RadialRemainder.rad D.R z v = y := by
    rw [← expMap_eq D hz]
    have h1 := heq 1 (right_mem_Icc.mpr zero_le_one)
    have hx1 : x 1 = y := by
      simp only [hxdef, sub_self]
      exact hstart
    rw [hx1] at h1
    rw [h1]
    simp only [scaledGeodesic, mul_one, expMap]
  obtain ⟨hVmem, hVspec⟩ := expInv_spec D hz hzy
  have hvmem : v ∈ closedBall (0 : Coordinates n) D.ρ := by
    rw [mem_closedBall, dist_zero_right]
    exact hvρ.le
  have hvV : v = expInv D z y := eq_of_exp_eq D hz hvmem hVmem (hexp.trans hVspec.symm)
  intro s hs
  have h := heq s hs
  rw [hvV] at h
  exact h.symm

end

end Finsler.SegmentReverse
