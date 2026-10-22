module

public import Finsler.Geometry.SegmentMomentum
public import Finsler.Geometry.PolygonSmooth

/-! The minimal energy is C¹ through the diagonal, jointly in both points. Near a diagonal point
(y, y) of a chart the two-endpoint chart energy F²(y', V(y', z')) is at most a multiple of
‖z' − y'‖² and its derivative off the diagonal, the boundary covector (terminal momentum minus
initial momentum), is at most a multiple of ‖z' − y'‖. Hence the joint energy is differentiable
at the diagonal with derivative zero, and its derivative is continuous there; off the diagonal
it is C³. So the joint chart energy is C¹ at the diagonal points, the minimal energy extended
to ambient pairs by normalization is C¹ at every pair of sufficiently close sphere points,
equal or not, and the polygon energy with normalized vertices is C¹ at every short polygon,
with or without zero edges. -/

@[expose] public section

namespace Finsler.EnergyDiagonal

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.ExpInverseRegularity
open Finsler.EikonalChart Finsler.EnergyJointSmooth Finsler.ShortCalibrator
open Finsler.SegmentMomentum Finsler.SphereRetraction Finsler.SegmentAtlas
open Finsler.EnergySphereSmooth Finsler.PolygonSmooth Finsler.PolygonLoop
open Finsler.AmbientEnergyRegularity Finsler.AmbientCalibrator Finsler.SegmentContinuity
open Finsler.SphereDistance (minEnergy)
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

section Diagonal

variable {y : Coordinates n} (hy : y ∈ ball y₀ r) (hyt : y ∈ (extChartAt (𝓡 n) p).target)

include hy hyt in
/-- Near a diagonal point the joint energy is at most a multiple of the squared distance of
the two points, and the boundary covector is at most a multiple of their distance. -/
theorem exists_diagonal_bounds :
    ∃ ε K : ℝ, 0 < ε ∧ 0 ≤ K ∧ ∀ y' z' : Coordinates n, ‖y' - y‖ < ε → ‖z' - y‖ < ε →
      y' ∈ ball y₀ r ∧ ‖z' - y'‖ < D.ρ / 2 ∧ y' ∈ (extChartAt (𝓡 n) p).target ∧
      jointEnergy D (y', z') ≤ K * ‖z' - y'‖ ^ 2 ∧
      ‖boundaryCovector D y' z'‖ ≤ K * ‖z' - y'‖ := by
  obtain ⟨ε₀, C, hε₀, hC, hsub, hb⟩ := exists_lagrangian_quadratic (F := F) hyt
  obtain ⟨M, hM0, hM⟩ := exists_endVel_bound D
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp isOpen_ball y hy
  have hρ := D.ρ_pos
  refine ⟨min ε₀ (min ε₁ (D.ρ / 4)), 2 * C * (M + 1),
    lt_min hε₀ (lt_min hε₁ (by positivity)), by positivity, ?_⟩
  intro y' z' hy' hz'
  have hy0 : ‖y' - y‖ < ε₀ := hy'.trans_le (min_le_left _ _)
  have hz0 : ‖z' - y‖ < ε₀ := hz'.trans_le (min_le_left _ _)
  have hy1 : ‖y' - y‖ < ε₁ := hy'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hy4 : ‖y' - y‖ < D.ρ / 4 := hy'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hz4 : ‖z' - y‖ < D.ρ / 4 := hz'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hyb : y' ∈ ball y₀ r := hball (by rwa [mem_ball, dist_eq_norm])
  have hyc : y' ∈ closedBall y ε₀ := by
    rw [mem_closedBall, dist_eq_norm]
    exact hy0.le
  have hzc : z' ∈ closedBall y ε₀ := by
    rw [mem_closedBall, dist_eq_norm]
    exact hz0.le
  have hzy : ‖z' - y'‖ < D.ρ / 2 := by
    have h : z' - y' = (z' - y) - (y' - y) := by abel
    rw [h]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hV := norm_expInv_le D (ball_subset_closedBall hyb) hzy.le
  refine ⟨hyb, hzy, hsub hyc, ?_, ?_⟩
  · have h1 := (hb y' hyc (expInv D y' z')).2
    have h2 : ‖expInv D y' z'‖ ^ 2 ≤ (2 * ‖z' - y'‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hV 2
    have h4 : C / 2 * ‖expInv D y' z'‖ ^ 2 ≤ C / 2 * (2 * ‖z' - y'‖) ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : 0 ≤ C * M * ‖z' - y'‖ ^ 2 := by positivity
    have h6 : C / 2 * (2 * ‖z' - y'‖) ^ 2 = 2 * C * ‖z' - y'‖ ^ 2 := by ring
    have h7 : 2 * C * (M + 1) * ‖z' - y'‖ ^ 2 =
        2 * C * ‖z' - y'‖ ^ 2 + 2 * (C * M * ‖z' - y'‖ ^ 2) := by ring
    change coordinateLagrangian F p (y', expInv D y' z') ≤ _
    linarith
  · have hA : ‖velocityTerm (coordinateLagrangian F p) (z', endVel D y' z')‖ ≤
        C * (M * (2 * ‖z' - y'‖)) :=
      ((hb z' hzc (endVel D y' z')).1).trans (mul_le_mul_of_nonneg_left
        ((hM y' (ball_subset_closedBall hyb) z' hzy.le).trans
          (mul_le_mul_of_nonneg_left hV hM0)) hC.le)
    have hB : ‖velocityTerm (coordinateLagrangian F p) (y', expInv D y' z')‖ ≤
        C * (2 * ‖z' - y'‖) :=
      ((hb y' hyc (expInv D y' z')).1).trans (mul_le_mul_of_nonneg_left hV hC.le)
    have h1 : ‖(velocityTerm (coordinateLagrangian F p) (z', endVel D y' z')).comp
        (ContinuousLinearMap.snd ℝ (Coordinates n) (Coordinates n))‖ ≤
        C * (M * (2 * ‖z' - y'‖)) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)).trans hA)
    have h2 : ‖(velocityTerm (coordinateLagrangian F p) (y', expInv D y' z')).comp
        (ContinuousLinearMap.fst ℝ (Coordinates n) (Coordinates n))‖ ≤ C * (2 * ‖z' - y'‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)).trans hB)
    unfold boundaryCovector
    refine (norm_sub_le _ _).trans ?_
    nlinarith

include hy hyt in
/-- At a diagonal point the joint energy is differentiable with derivative zero. -/
theorem jointEnergy_hasFDerivAt_self :
    HasFDerivAt (jointEnergy D) (0 : Coordinates n × Coordinates n →L[ℝ] ℝ) (y, y) := by
  obtain ⟨ε, K, hε, hK, hb⟩ := exists_diagonal_bounds D hy hyt
  apply hasFDerivAt_of_eventually_quadratic (K := 4 * K)
  filter_upwards [Metric.ball_mem_nhds (0 : Coordinates n × Coordinates n) hε] with d hd
  have hdn : ‖d‖ < ε := mem_ball_zero_iff.mp hd
  have h1 : ‖(y + d.1) - y‖ < ε := by
    rw [add_sub_cancel_left]
    exact (norm_fst_le d).trans_lt hdn
  have h2 : ‖(y + d.2) - y‖ < ε := by
    rw [add_sub_cancel_left]
    exact (norm_snd_le d).trans_lt hdn
  obtain ⟨-, -, -, hq, -⟩ := hb (y + d.1) (y + d.2) h1 h2
  have h0 : jointEnergy D (y, y) = 0 := energyFn_self D (ball_subset_closedBall hy)
  have hpos : 0 ≤ jointEnergy D ((y, y) + d) := by
    change 0 ≤ Finsler.AmbientLagrangian.lagrangian F _
    exact sq_nonneg _
  rw [h0, sub_zero, zero_apply, sub_zero, Real.norm_of_nonneg hpos]
  have he : (y + d.2) - (y + d.1) = d.2 - d.1 := by abel
  have hn : ‖d.2 - d.1‖ ≤ 2 * ‖d‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_fst_le d, norm_snd_le d])
  have hsq : ‖d.2 - d.1‖ ^ 2 ≤ (2 * ‖d‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hq' : jointEnergy D ((y, y) + d) ≤ K * ‖d.2 - d.1‖ ^ 2 := by
    rw [← he]
    exact hq
  nlinarith

end Diagonal

open Classical in
/-- The derivative of the joint energy: zero on the diagonal, the boundary covector off it. -/
def jointDeriv (q : Coordinates n × Coordinates n) :
    Coordinates n × Coordinates n →L[ℝ] ℝ :=
  if q.2 = q.1 then 0 else boundaryCovector D q.1 q.2

/-- The joint chart energy is C¹ at the diagonal points. -/
theorem jointEnergy_contDiffAt_one {y : Coordinates n} (hy : y ∈ ball y₀ r)
    (hyt : y ∈ (extChartAt (𝓡 n) p).target) : ContDiffAt ℝ 1 (jointEnergy D) (y, y) := by
  obtain ⟨ε, K, hε, hK, hb⟩ := exists_diagonal_bounds D hy hyt
  set u : Set (Coordinates n × Coordinates n) := {q | ‖q.1 - y‖ < ε ∧ ‖q.2 - y‖ < ε} with hu
  have huo : IsOpen u :=
    (isOpen_lt ((continuous_fst.sub continuous_const).norm) continuous_const).inter
      (isOpen_lt ((continuous_snd.sub continuous_const).norm) continuous_const)
  have hyu : (y, y) ∈ u := by
    change ‖y - y‖ < ε ∧ ‖y - y‖ < ε
    rw [sub_self, norm_zero]
    exact ⟨hε, hε⟩
  have hder : ∀ q ∈ u, HasFDerivAt (jointEnergy D) (jointDeriv D q) q := by
    intro q hq
    obtain ⟨h1, h2, h3, -, -⟩ := hb q.1 q.2 hq.1 hq.2
    by_cases hd : q.2 = q.1
    · have hq' : q = (q.1, q.1) := Prod.ext rfl hd
      rw [jointDeriv, ite_eq_left hd, hq']
      exact jointEnergy_hasFDerivAt_self D h1 h3
    · rw [jointDeriv, ite_eq_right hd]
      exact jointEnergy_hasFDerivAt D h1 h2 hd
  rw [contDiffAt_one_iff]
  refine ⟨jointDeriv D, u, huo.mem_nhds hyu, ?_, hder⟩
  intro q₀ hq₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨h1, h2, h3, -, -⟩ := hb q₀.1 q₀.2 hq₀.1 hq₀.2
  by_cases hd : q₀.2 = q₀.1
  · have h0 : jointDeriv D q₀ = 0 := by rw [jointDeriv, ite_eq_left hd]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun q : Coordinates n × Coordinates n => K * ‖q.2 - q.1‖) (𝓝 q₀)
        (𝓝 0) := by
      have hc : Continuous fun q : Coordinates n × Coordinates n => K * ‖q.2 - q.1‖ :=
        continuous_const.mul (continuous_snd.sub continuous_fst).norm
      have h := hc.tendsto q₀
      rwa [hd, sub_self, norm_zero, mul_zero] at h
    refine squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) ?_ hlim
    filter_upwards [huo.mem_nhds hq₀] with q hq
    by_cases hq' : q.2 = q.1
    · rw [jointDeriv, ite_eq_left hq', norm_zero]
      exact mul_nonneg hK (norm_nonneg _)
    · rw [jointDeriv, ite_eq_right hq']
      exact (hb q.1 q.2 hq.1 hq.2).2.2.2.2
  · have hC : ContDiffAt ℝ 3 (jointEnergy D) q₀ := by
      have h := energy_contDiffAt_joint D h1 h2 hd h3
      exact h
    have hcf := hC.continuousAt_fderiv (by norm_num)
    have hopen : IsOpen {q : Coordinates n × Coordinates n | q.2 ≠ q.1} :=
      isOpen_ne_fun continuous_snd continuous_fst
    refine hcf.congr ?_
    filter_upwards [huo.mem_nhds hq₀, hopen.mem_nhds hd] with q hq hq'
    rw [(hder q hq).fderiv]

variable (F)

/-- At every pair of sphere points in a chart package, equal or not, the extended minimal
energy is C¹. -/
theorem ambientMinEnergy_contDiffAt_one_of_package (S : SegChart F) {P₀ Q₀ : Sphere n}
    (hP₀ : P₀ ∈ segDom S) (hQ₀ : ‖(Q₀ : Ambient n) - P₀‖ < S.δ) :
    ContDiffAt ℝ 1 (ambientMinEnergy F) ((P₀ : Ambient n), (Q₀ : Ambient n)) := by
  by_cases hne : Q₀ = P₀
  · subst hne
    have hP0 := sphere_ne_zero Q₀
    have hPs : normalize (Q₀ : Ambient n) ∈ (extChartAt (𝓡 n) S.p).source := by
      rw [normalize_inclusion]
      exact hP₀.1
    set Φ : Ambient n × Ambient n → Coordinates n × Coordinates n :=
      fun x => (chartNormalize S.p x.1, chartNormalize S.p x.2) with hΦ
    have hΦs : ContDiffAt ℝ 1 Φ ((Q₀ : Ambient n), (Q₀ : Ambient n)) := by
      have h1 : ContDiffAt ℝ 1 (chartNormalize S.p) (Q₀ : Ambient n) :=
        (chartNormalize_smoothAt S.p hP0 hPs).of_le (by simp)
      exact (ContDiffAt.comp (g := chartNormalize S.p)
        (f := fun x : Ambient n × Ambient n => x.1)
        (x := ((Q₀ : Ambient n), (Q₀ : Ambient n))) h1 contDiffAt_fst).prodMk
        (ContDiffAt.comp (g := chartNormalize S.p) (f := fun x : Ambient n × Ambient n => x.2)
          (x := ((Q₀ : Ambient n), (Q₀ : Ambient n))) h1 contDiffAt_snd)
    have hy₁ : chartNormalize S.p (Q₀ : Ambient n) ∈ ball S.y₀ S.r := by
      rw [← chartNormalize_normalize, normalize_inclusion, chartNormalize_sphere]
      exact ball_subset_ball S.hr'r hP₀.2
    have hyt : chartNormalize S.p (Q₀ : Ambient n) ∈ (extChartAt (𝓡 n) S.p).target :=
      S.hball (ball_subset_closedBall hy₁)
    have he := jointEnergy_contDiffAt_one S.D hy₁ hyt
    have hcomp := he.comp ((Q₀ : Ambient n), (Q₀ : Ambient n)) hΦs
    apply hcomp.congr_of_eventuallyEq
    have hnorm1 : ContinuousAt (fun x : Ambient n × Ambient n => normalize x.1)
        ((Q₀ : Ambient n), (Q₀ : Ambient n)) :=
      ContinuousAt.comp (g := normalize) (f := fun x : Ambient n × Ambient n => x.1)
        (x := ((Q₀ : Ambient n), (Q₀ : Ambient n))) (normalize_smoothAt hP0).continuousAt
        continuousAt_fst
    have hnorm2 : ContinuousAt (fun x : Ambient n × Ambient n => normalize x.2)
        ((Q₀ : Ambient n), (Q₀ : Ambient n)) :=
      ContinuousAt.comp (g := normalize) (f := fun x : Ambient n × Ambient n => x.2)
        (x := ((Q₀ : Ambient n), (Q₀ : Ambient n))) (normalize_smoothAt hP0).continuousAt
        continuousAt_snd
    have hev1 : ∀ᶠ x : Ambient n × Ambient n in 𝓝 ((Q₀ : Ambient n), (Q₀ : Ambient n)),
        normalize x.1 ∈ segDom S := by
      have h := hnorm1.preimage_mem_nhds ((segDom_isOpen F S).mem_nhds (by
        change normalize (Q₀ : Ambient n) ∈ segDom S
        rw [normalize_inclusion]
        exact hP₀))
      exact h
    have hev2 : ∀ᶠ x : Ambient n × Ambient n in 𝓝 ((Q₀ : Ambient n), (Q₀ : Ambient n)),
        ‖(normalize x.2 : Ambient n) - normalize x.1‖ < S.δ := by
      have hc : ContinuousAt (fun x : Ambient n × Ambient n =>
          ‖(normalize x.2 : Ambient n) - normalize x.1‖)
          ((Q₀ : Ambient n), (Q₀ : Ambient n)) :=
        ((continuous_subtype_val.continuousAt.comp hnorm2).sub
          (continuous_subtype_val.continuousAt.comp hnorm1)).norm
      apply hc.eventually (gt_mem_nhds _)
      simp only [normalize_inclusion]
      exact hQ₀
    filter_upwards [hev1, hev2] with x hx1 hx2
    unfold ambientMinEnergy
    rw [minE_of_dom S hx1 hx2]
    unfold ambientEnergy Finsler.EikonalChart.energyFn
    rw [chartNormalize_normalize, ← chartNormalize_sphere, chartNormalize_normalize]
    rfl
  · exact (ambientMinEnergy_contDiffAt_of_package F S hP₀ hQ₀ hne).of_le (by norm_num)

/-- A uniform δ below which the extended minimal energy is C¹ at every pair of sphere points,
equal or not. -/
theorem exists_ambientMinEnergy_contDiffAt_one :
    ∃ δ > 0, ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)) := by
  obtain ⟨δ, hδ, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  refine ⟨δ, hδ, fun P Q hQ => ?_⟩
  obtain ⟨P₀, hP₀, hP⟩ := hcover P
  exact ambientMinEnergy_contDiffAt_one_of_package F (S P₀) hP (hQ.trans_le (hδS P₀ hP₀))

/-- The polygon energy with normalized vertices is C¹ at every short polygon, with or without
zero edges. -/
theorem polyEnergyN_contDiffAt_one {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {N : ℕ} [NeZero N] {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    ContDiffAt ℝ 1 (polyEnergyN F N) (fun i => (q i : Ambient n)) := by
  unfold polyEnergyN
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro k _
  have hproj : ContDiffAt ℝ 1 (fun Q : ZMod N → Ambient n => (Q k, Q ((k : ZMod N) + 1)))
      (fun i => (q i : Ambient n)) :=
    ((contDiff_apply ℝ (Ambient n) (k : ZMod N)).prodMk
      (contDiff_apply ℝ (Ambient n) ((k : ZMod N) + 1))).contDiffAt
  exact ContDiffAt.comp (g := ambientMinEnergy F)
    (f := fun Q : ZMod N → Ambient n => (Q k, Q ((k : ZMod N) + 1)))
    (x := fun i => (q i : Ambient n)) (hδ _ _ (hq k)) hproj

end

end Finsler.EnergyDiagonal
