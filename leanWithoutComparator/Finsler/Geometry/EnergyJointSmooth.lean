module

public import Finsler.Geometry.ShortCalibrator

/-! Joint smoothness of the local inverse of the coordinate exponential map. The map
(y, v) ↦ (y, exp(y, v)) is C³ off v = 0 with block triangular derivative whose velocity block is
id + D rad, of norm distance at most 1/2 from the identity; it is injective, hence invertible in
finite dimension. By the C³ inverse function theorem and the uniqueness of the local inverse,
(y, z) ↦ V(y, z) is C³ near every off-diagonal point, and so is the chart energy F²(y, V(y, z)). -/

@[expose] public section

namespace Finsler.EnergyJointSmooth

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.ExpInverseRegularity
open Finsler.RadialRemainder
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- The exponential map as a function of the pair (y, v). -/
def expPair (q : Coordinates n × Coordinates n) : Coordinates n := expMap D q.1 q.2

theorem expPair_contDiffAt {q : Coordinates n × Coordinates n} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ 3 (expPair D) q := by
  have hn : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n => ‖w.2‖) q :=
    (contDiffAt_norm ℝ hq).comp q contDiffAt_snd
  have hinv : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n => ‖w.2‖⁻¹) q :=
    hn.inv (norm_ne_zero_iff.mpr hq)
  have hpol : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n =>
      ((w.1, ‖w.2‖⁻¹ • w.2), ‖w.2‖)) q :=
    (contDiffAt_fst.prodMk (hinv.smul contDiffAt_snd)).prodMk hn
  exact contDiffAt_fst.comp q (D.smooth.contDiffAt.comp q hpol)

/-- The velocity derivative of exp at a point of the ρ-ball is id + T with ‖T‖ ≤ 1/2. -/
theorem exists_expMap_hasFDerivAt {y : Coordinates n} (hy : y ∈ closedBall y₀ r)
    {v : Coordinates n} (hv : v ≠ 0) (hvρ : ‖v‖ < D.ρ) :
    ∃ T : Coordinates n →L[ℝ] Coordinates n, ‖T‖ ≤ 1 / 2 ∧
      HasFDerivAt (expMap D y) (ContinuousLinearMap.id ℝ (Coordinates n) + T) v := by
  have hf := expMap_contDiffAt D y hv
  have hfun : expMap D y = fun w => y + w + rad D.R y w := funext (expMap_eq D hy)
  have hrad_d : DifferentiableAt ℝ (rad D.R y) v := by
    have h1 : DifferentiableAt ℝ (expMap D y) v := hf.differentiableAt (by norm_num)
    have h2 : rad D.R y = fun w => expMap D y w - y - w := by
      funext w
      rw [expMap_eq D hy]
      abel
    rw [h2]
    exact (h1.sub_const y).sub differentiableAt_id
  refine ⟨fderiv ℝ (rad D.R y) v, ?_, ?_⟩
  · have hball : closedBall (0 : Coordinates n) D.ρ ∈ 𝓝 v :=
      mem_of_superset (isOpen_ball.mem_nhds (by simpa using hvρ)) ball_subset_closedBall
    have hlip : LipschitzOnWith (1 / 2 : NNReal) (rad D.R y)
        (closedBall (0 : Coordinates n) D.ρ) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm]
      have h := D.lip y hy a ha b hb
      push_cast
      linarith
    have h := norm_fderiv_le_of_lipschitzOn ℝ hball hlip
    simpa using h
  · rw [hfun]
    have h1 : HasFDerivAt (fun w : Coordinates n => y + w)
        (ContinuousLinearMap.id ℝ (Coordinates n)) v :=
      (hasFDerivAt_id v).const_add y
    exact h1.add hrad_d.hasFDerivAt

/-- Joint C³ smoothness of the local inverse off the diagonal. -/
theorem expInv_contDiffAt_joint {y₁ z₁ : Coordinates n} (hy₁ : y₁ ∈ ball y₀ r)
    (hz₁ : ‖z₁ - y₁‖ < D.ρ / 2) (hne : z₁ ≠ y₁) :
    ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n => expInv D q.1 q.2) (y₁, z₁) := by
  have hy₁' : y₁ ∈ closedBall y₀ r := ball_subset_closedBall hy₁
  set v₁ := expInv D y₁ z₁ with hv₁
  have hv₁0 : v₁ ≠ 0 := expInv_ne_zero D hy₁' hz₁.le hne
  have hv₁ρ : ‖v₁‖ < D.ρ := by
    have h := norm_expInv_le D hy₁' hz₁.le
    linarith
  set G : Coordinates n × Coordinates n → Coordinates n × Coordinates n :=
    fun q => (q.1, expPair D q) with hGdef
  have hE := expPair_contDiffAt D (q := (y₁, v₁)) hv₁0
  have hG : ContDiffAt ℝ 3 G (y₁, v₁) := contDiffAt_fst.prodMk hE
  have hEd : DifferentiableAt ℝ (expPair D) (y₁, v₁) := hE.differentiableAt (by norm_num)
  set DE := fderiv ℝ (expPair D) (y₁, v₁) with hDE
  set DG : Coordinates n × Coordinates n →L[ℝ] Coordinates n × Coordinates n :=
    (ContinuousLinearMap.fst ℝ (Coordinates n) (Coordinates n)).prod DE with hDG
  have hGd : HasFDerivAt G DG (y₁, v₁) := hasFDerivAt_fst.prodMk hEd.hasFDerivAt
  -- the velocity block is the derivative of exp(y₁,·)
  obtain ⟨T, hT, hTd⟩ := exists_expMap_hasFDerivAt D hy₁' hv₁0 hv₁ρ
  have hslice : HasFDerivAt (expMap D y₁) (DE.comp (ContinuousLinearMap.inr ℝ _ _)) v₁ := by
    have hin : HasFDerivAt (fun v : Coordinates n => ((y₁, v) : Coordinates n × Coordinates n))
        (ContinuousLinearMap.inr ℝ (Coordinates n) (Coordinates n)) v₁ :=
      hasFDerivAt_prodMk_right y₁ v₁
    exact hEd.hasFDerivAt.comp v₁ hin
  have hblock : DE.comp (ContinuousLinearMap.inr ℝ _ _) =
      ContinuousLinearMap.id ℝ (Coordinates n) + T := hslice.unique hTd
  have hinj : Injective DG := by
    intro a b hab
    have h1 : a.1 = b.1 := by
      have h := congrArg Prod.fst hab
      simpa [hDG] using h
    have h2 : DE a = DE b := by
      have h := congrArg Prod.snd hab
      simpa [hDG] using h
    have hsplit : ∀ c : Coordinates n × Coordinates n,
        DE c = DE (c.1, 0) + (ContinuousLinearMap.id ℝ (Coordinates n) + T) c.2 := by
      intro c
      rw [← hblock, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_add]
      simp
    rw [hsplit a, hsplit b, h1] at h2
    have h3 : (ContinuousLinearMap.id ℝ (Coordinates n) + T) a.2 =
        (ContinuousLinearMap.id ℝ (Coordinates n) + T) b.2 := add_left_cancel h2
    rw [← idAddEquiv_coe T hT] at h3
    exact Prod.ext h1 ((idAddEquiv T hT).injective h3)
  set DGe : (Coordinates n × Coordinates n) ≃L[ℝ] (Coordinates n × Coordinates n) :=
    (LinearEquiv.ofInjectiveEndo (DG : Coordinates n × Coordinates n →ₗ[ℝ]
      Coordinates n × Coordinates n) hinj).toContinuousLinearEquiv with hDGe
  have hDGe_coe : (DGe : Coordinates n × Coordinates n →L[ℝ] Coordinates n × Coordinates n) = DG :=
    ContinuousLinearMap.ext fun x => rfl
  have hGd' : HasFDerivAt G (DGe : Coordinates n × Coordinates n →L[ℝ]
      Coordinates n × Coordinates n) (y₁, v₁) := by
    rw [hDGe_coe]
    exact hGd
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hs := hG.hasStrictFDerivAt' hGd' hn
  -- (y, z) ↦ (y, V(y,z)) is a left inverse of G near (y₁, v₁)
  set Ginv : Coordinates n × Coordinates n → Coordinates n × Coordinates n :=
    fun q => (q.1, expInv D q.1 q.2) with hGinv
  have hval : expPair D (y₁, v₁) = z₁ := by
    change expMap D y₁ v₁ = z₁
    rw [expMap_eq D hy₁']
    exact (expInv_spec D hy₁' hz₁.le).2
  have hg : ∀ᶠ q in 𝓝 (y₁, v₁), Ginv (G q) = q := by
    have hcont : ContinuousAt (fun q : Coordinates n × Coordinates n => ‖expPair D q - q.1‖)
        (y₁, v₁) := ((hE.continuousAt).sub continuousAt_fst).norm
    have hlt : ‖expPair D (y₁, v₁) - (y₁, v₁).1‖ < D.ρ / 2 := by rw [hval]; exact hz₁
    have hnear : ∀ᶠ q in 𝓝 (y₁, v₁), ‖expPair D q - q.1‖ < D.ρ / 2 :=
      hcont.eventually (isOpen_Iio.mem_nhds hlt)
    have hball : ∀ᶠ q : Coordinates n × Coordinates n in 𝓝 (y₁, v₁), ‖q.2‖ < D.ρ :=
      (continuous_norm.comp continuous_snd).continuousAt.eventually
        (isOpen_Iio.mem_nhds (show ‖((y₁, v₁) : Coordinates n × Coordinates n).2‖ ∈ Iio D.ρ from hv₁ρ))
    have hy : ∀ᶠ q : Coordinates n × Coordinates n in 𝓝 (y₁, v₁), q.1 ∈ ball y₀ r :=
      continuous_fst.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hy₁)
    filter_upwards [hnear, hball, hy] with q hq1 hq2 hq3
    have hq3' : q.1 ∈ closedBall y₀ r := ball_subset_closedBall hq3
    have hspec := expInv_spec D hq3' hq1.le
    have heq : expInv D q.1 (expPair D q) = q.2 := by
      apply eq_of_exp_eq D hq3' hspec.1 (by simpa using hq2.le)
      rw [hspec.2]
      change expMap D q.1 q.2 = _
      rw [expMap_eq D hq3']
    change (q.1, expInv D q.1 (expPair D q)) = q
    rw [heq]
  have huniq := hs.localInverse_unique hg
  have hloc := hG.to_localInverse hGd' hn
  have hGv : G (y₁, v₁) = (y₁, z₁) := by
    change ((y₁, v₁).1, expPair D (y₁, v₁)) = (y₁, z₁)
    rw [hval]
  rw [hGv] at huniq hloc
  have hGinv : ContDiffAt ℝ 3 Ginv (y₁, z₁) := hloc.congr_of_eventuallyEq huniq
  exact contDiffAt_snd.comp (y₁, z₁) hGinv

/-- Joint C³ smoothness of the chart energy F²(y, V(y, z)) off the diagonal. -/
theorem energy_contDiffAt_joint {y₁ z₁ : Coordinates n} (hy₁ : y₁ ∈ ball y₀ r)
    (hz₁ : ‖z₁ - y₁‖ < D.ρ / 2) (hne : z₁ ≠ y₁)
    (hyt : y₁ ∈ (extChartAt (𝓡 n) p).target) :
    ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n =>
      coordinateLagrangian F p (q.1, expInv D q.1 q.2)) (y₁, z₁) := by
  have hy₁' : y₁ ∈ closedBall y₀ r := ball_subset_closedBall hy₁
  have hV0 : expInv D y₁ z₁ ≠ 0 := expInv_ne_zero D hy₁' hz₁.le hne
  have hL : ContDiffAt ℝ 3 (coordinateLagrangian F p) (y₁, expInv D y₁ z₁) :=
    (coordinateLagrangian_smoothAt_nonzero F p (z := (y₁, expInv D y₁ z₁)) hyt hV0).of_le
      (by simp)
  have hpair : ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n =>
      (q.1, expInv D q.1 q.2)) (y₁, z₁) :=
    contDiffAt_fst.prodMk (expInv_contDiffAt_joint D hy₁ hz₁ hne)
  exact hL.comp (y₁, z₁) hpair

end

end Finsler.EnergyJointSmooth
