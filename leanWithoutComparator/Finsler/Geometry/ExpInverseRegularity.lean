module

public import Finsler.Geometry.CoordinateExpInverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-! Continuity of the local inverse of the coordinate exponential map. On its domain
{(y,z) : y in the chart ball, ‖z − y‖ ≤ ρ/2}, the inverse V(y,z) satisfies
‖V(q) − V(q₀)‖ ≤ 2‖Δ‖ + 2‖rad(y,v₀) − rad(y₀,v₀)‖, where Δ is the change of z − y and v₀ = V(q₀),
because the radial remainder is 1/2-Lipschitz in v; the right side tends to 0 since the radial
remainder is continuous in y for fixed v. Off the diagonal, exp(y,·) is C³ with derivative
id + D rad, invertible because ‖D rad‖ ≤ 1/2, so by the C³ inverse function theorem and uniqueness
V(y,·) is C³ there. -/

@[expose] public section

namespace Finsler.ExpInverseRegularity

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.CoordinateExpInverse Finsler.RadialRemainder
open Set Filter Metric
open scoped Topology Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- The domain of the local inverse. -/
def invDomain : Set (Coordinates n × Coordinates n) :=
  {q | q.1 ∈ closedBall y₀ r ∧ ‖q.2 - q.1‖ ≤ D.ρ / 2}

theorem rad_continuous_left (v : Coordinates n) : Continuous (fun y => rad D.R y v) := by
  unfold rad polar
  exact (continuous_const : Continuous fun _ : Coordinates n => ‖v‖ ^ 2).smul
    (D.R_smooth.continuous.comp ((continuous_id.prodMk continuous_const).prodMk continuous_const))

/-- The basic estimate for the inverse at two points of its domain. -/
theorem norm_expInv_sub_le {q q₀ : Coordinates n × Coordinates n} (hq : q ∈ invDomain D)
    (hq₀ : q₀ ∈ invDomain D) :
    ‖expInv D q.1 q.2 - expInv D q₀.1 q₀.2‖ ≤
      2 * ‖(q.2 - q.1) - (q₀.2 - q₀.1)‖ +
        2 * ‖rad D.R q.1 (expInv D q₀.1 q₀.2) - rad D.R q₀.1 (expInv D q₀.1 q₀.2)‖ := by
  obtain ⟨hv, hvs⟩ := expInv_spec D hq.1 hq.2
  obtain ⟨hv₀, hv₀s⟩ := expInv_spec D hq₀.1 hq₀.2
  set v := expInv D q.1 q.2 with hvdef
  set v₀ := expInv D q₀.1 q₀.2 with hv₀def
  have hlip := D.lip q.1 hq.1 v hv v₀ hv₀
  have heq : v - v₀ = ((q.2 - q.1) - (q₀.2 - q₀.1)) - (rad D.R q.1 v - rad D.R q.1 v₀) -
      (rad D.R q.1 v₀ - rad D.R q₀.1 v₀) := by
    have h1 : q.2 - q.1 = v + rad D.R q.1 v := by rw [← hvs]; abel
    have h2 : q₀.2 - q₀.1 = v₀ + rad D.R q₀.1 v₀ := by rw [← hv₀s]; abel
    rw [h1, h2]
    abel
  have h3 : ‖v - v₀‖ ≤ ‖(q.2 - q.1) - (q₀.2 - q₀.1)‖ + ‖rad D.R q.1 v - rad D.R q.1 v₀‖ +
      ‖rad D.R q.1 v₀ - rad D.R q₀.1 v₀‖ := by
    rw [heq]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  linarith

/-- The local inverse is continuous on its domain. -/
theorem expInv_continuousOn : ContinuousOn (fun q : Coordinates n × Coordinates n =>
    expInv D q.1 q.2) (invDomain D) := by
  intro q₀ hq₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  set v₀ := expInv D q₀.1 q₀.2
  let g : Coordinates n × Coordinates n → ℝ := fun q =>
    2 * ‖(q.2 - q.1) - (q₀.2 - q₀.1)‖ + 2 * ‖rad D.R q.1 v₀ - rad D.R q₀.1 v₀‖
  have hg : Continuous g := by
    have h1 : Continuous fun q : Coordinates n × Coordinates n => (q.2 - q.1) - (q₀.2 - q₀.1) :=
      (continuous_snd.sub continuous_fst).sub continuous_const
    have h2 : Continuous fun q : Coordinates n × Coordinates n =>
        rad D.R q.1 v₀ - rad D.R q₀.1 v₀ :=
      ((rad_continuous_left D v₀).comp continuous_fst).sub continuous_const
    exact (continuous_const.mul h1.norm).add (continuous_const.mul h2.norm)
  have hg0 : g q₀ = 0 := by simp [g]
  have htend : Tendsto g (𝓝[invDomain D] q₀) (𝓝 0) := by
    rw [← hg0]
    exact hg.continuousAt.continuousWithinAt.tendsto
  apply squeeze_zero' (Eventually.of_forall fun q => norm_nonneg _) _ htend
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact norm_expInv_sub_le D hq hq₀

section Smooth

/-- The coordinate exponential map in flow form. -/
def expMap (y v : Coordinates n) : Coordinates n := (D.Φ (y, ‖v‖⁻¹ • v) ‖v‖).1

theorem expMap_eq {y : Coordinates n} (hy : y ∈ closedBall y₀ r) (v : Coordinates n) :
    expMap D y v = y + v + rad D.R y v := by
  rcases eq_or_ne v 0 with h | h
  · subst h
    simp [expMap, D.init, rad_zero]
  · exact (D.exp_eq y hy v h).symm

theorem polar_contDiffAt (y : Coordinates n) {v : Coordinates n} (hv : v ≠ 0) :
    ContDiffAt ℝ 3 (fun w : Coordinates n => ((y, ‖w‖⁻¹ • w), ‖w‖)) v := by
  have hn : ContDiffAt ℝ 3 (fun w : Coordinates n => ‖w‖) v := contDiffAt_norm ℝ hv
  have hinv : ContDiffAt ℝ 3 (fun w : Coordinates n => ‖w‖⁻¹) v :=
    hn.inv (norm_ne_zero_iff.mpr hv)
  exact (contDiffAt_const.prodMk (hinv.smul contDiffAt_id)).prodMk hn

theorem expMap_contDiffAt (y : Coordinates n) {v : Coordinates n} (hv : v ≠ 0) :
    ContDiffAt ℝ 3 (expMap D y) v := by
  have h := D.smooth.contDiffAt.comp v (polar_contDiffAt y hv)
  exact contDiffAt_fst.comp v h

/-- The identity plus an operator of norm at most 1/2, as a continuous linear equivalence. -/
def idAddEquiv (T : Coordinates n →L[ℝ] Coordinates n) (hT : ‖T‖ ≤ 1 / 2) :
    Coordinates n ≃L[ℝ] Coordinates n :=
  (LinearEquiv.ofInjectiveEndo ((ContinuousLinearMap.id ℝ (Coordinates n) + T :
      Coordinates n →L[ℝ] Coordinates n) : Coordinates n →ₗ[ℝ] Coordinates n) (by
    intro h k hhk
    have h0 : (ContinuousLinearMap.id ℝ (Coordinates n) + T) (h - k) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hhk
    have h1 : h - k = -T (h - k) := by
      rw [add_apply, ContinuousLinearMap.id_apply] at h0
      exact eq_neg_of_add_eq_zero_left h0
    have h2 : ‖h - k‖ ≤ ‖h - k‖ / 2 := by
      calc ‖h - k‖ = ‖T (h - k)‖ := by rw [h1, norm_neg] ; rw [← h1]
        _ ≤ ‖T‖ * ‖h - k‖ := T.le_opNorm _
        _ ≤ 1 / 2 * ‖h - k‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
        _ = ‖h - k‖ / 2 := by ring
    have h3 : ‖h - k‖ = 0 := le_antisymm (by linarith [norm_nonneg (h - k)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h3))).toContinuousLinearEquiv

theorem idAddEquiv_coe (T : Coordinates n →L[ℝ] Coordinates n) (hT : ‖T‖ ≤ 1 / 2) :
    (idAddEquiv T hT : Coordinates n →L[ℝ] Coordinates n) =
      ContinuousLinearMap.id ℝ (Coordinates n) + T := by
  ext w
  rfl

/-- Off the diagonal the local inverse is C³ in the endpoint. -/
theorem expInv_contDiffAt {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) :
    ContDiffAt ℝ 3 (fun z' => expInv D y z') z := by
  have hz' : ‖z - y‖ ≤ D.ρ / 2 := hz.le
  set v₁ := expInv D y z with hv₁
  have hv₁0 : v₁ ≠ 0 := expInv_ne_zero D hy hz' hne
  have hv₁ρ : ‖v₁‖ < D.ρ := by
    have h := norm_expInv_le D hy hz'
    linarith
  have hf := expMap_contDiffAt D y hv₁0
  -- the derivative is id + D rad, with ‖D rad‖ ≤ 1/2
  have hfun : expMap D y = fun w => y + w + rad D.R y w := funext (expMap_eq D hy)
  have hrad_d : DifferentiableAt ℝ (rad D.R y) v₁ := by
    have h1 : DifferentiableAt ℝ (expMap D y) v₁ := hf.differentiableAt (by norm_num)
    have h2 : rad D.R y = fun w => expMap D y w - y - w := by
      funext w
      rw [expMap_eq D hy]
      abel
    rw [h2]
    exact (h1.sub_const y).sub differentiableAt_id
  set T := fderiv ℝ (rad D.R y) v₁ with hT
  have hTb : ‖T‖ ≤ 1 / 2 := by
    have hball : closedBall (0 : Coordinates n) D.ρ ∈ 𝓝 v₁ :=
      mem_of_superset (isOpen_ball.mem_nhds (by simpa using hv₁ρ)) ball_subset_closedBall
    have hlip : LipschitzOnWith (1 / 2 : NNReal) (rad D.R y) (closedBall (0 : Coordinates n) D.ρ) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm]
      have h := D.lip y hy a ha b hb
      push_cast
      linarith
    have h := norm_fderiv_le_of_lipschitzOn ℝ hball hlip
    simpa using h
  have hf' : HasFDerivAt (expMap D y) ((idAddEquiv T hTb : Coordinates n →L[ℝ] Coordinates n)) v₁ := by
    rw [idAddEquiv_coe, hfun]
    have h1 : HasFDerivAt (fun w : Coordinates n => y + w) (ContinuousLinearMap.id ℝ (Coordinates n)) v₁ :=
      (hasFDerivAt_id v₁).const_add y
    exact h1.add hrad_d.hasFDerivAt
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hs := hf.hasStrictFDerivAt' hf' hn
  -- V(y,·) is a left inverse of exp(y,·) near v₁
  have hg : ∀ᶠ w in 𝓝 v₁, expInv D y (expMap D y w) = w := by
    have hcont : ContinuousAt (expMap D y) v₁ := hf.continuousAt
    have hval : expMap D y v₁ = z := by
      rw [expMap_eq D hy]
      exact (expInv_spec D hy hz').2
    have hnear : ∀ᶠ w in 𝓝 v₁, ‖expMap D y w - y‖ < D.ρ / 2 := by
      have h := hcont.sub_const y |>.norm
      have hlt : ‖expMap D y v₁ - y‖ < D.ρ / 2 := by rw [hval]; exact hz
      exact h.eventually (isOpen_Iio.mem_nhds hlt)
    have hball : ∀ᶠ w in 𝓝 v₁, ‖w‖ < D.ρ :=
      continuous_norm.continuousAt.eventually (isOpen_Iio.mem_nhds hv₁ρ)
    filter_upwards [hnear, hball] with w hw hwρ
    have hspec := expInv_spec D hy hw.le
    apply eq_of_exp_eq D hy hspec.1 (by simpa using hwρ.le)
    rw [hspec.2, expMap_eq D hy]
  have huniq := hs.localInverse_unique hg
  have hval : expMap D y v₁ = z := by
    rw [expMap_eq D hy]
    exact (expInv_spec D hy hz').2
  have hloc := hf.to_localInverse hf' hn
  rw [hval] at huniq hloc
  exact hloc.congr_of_eventuallyEq huniq

end Smooth

end

end Finsler.ExpInverseRegularity
