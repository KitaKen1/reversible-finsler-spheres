module

public import Finsler.Analysis.LagrangianSpray
public import Finsler.Analysis.IntervalH1SmoothRegularity
public import Finsler.Geometry.CoordinateEnergyRegularity
public import TauCeti.Analysis.ODE.InitialCondition

/-! The geodesic spray in a standard sphere chart. The velocity Hessian of a pullback Lagrangian
is the ambient velocity Hessian evaluated on pushed-forward vectors. For the actual Finsler
density in a sphere chart this is positive on nonzero vectors at nonzero velocity, so the
coordinate spray is defined, smooth away from zero velocity, quadratic in the velocity, and its
integral curves have vanishing coordinate Euler–Lagrange residual. -/

@[expose] public section

namespace Finsler.CoordinateSpray

open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientLagrangian
open Finsler.EulerCovariance Finsler.LagrangianSpray Finsler.SphereCoordinateEuler
open Finsler.CoordinateEnergyRegularity Function Filter
open scoped ContDiff Topology Manifold RealInnerProductSpace

noncomputable section

section Pullback

variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- The velocity Hessian of a pullback Lagrangian, evaluated on a pair of equal vectors. -/
theorem velocityHessian_pullback_apply {L : A × A → ℝ} {φ : E → A} {y η : E}
    (hφ : ContDiffAt ℝ 2 φ y) (hL1 : ∀ η' : E, ContDiffAt ℝ 1 L (jetMap φ (y, η')))
    (hL2 : ContDiffAt ℝ 2 L (jetMap φ (y, η))) (w : E) :
    velocityHessian (pullback L φ) (y, η) w w =
      fderiv ℝ (fderiv ℝ L) (jetMap φ (y, η)) ((0 : A), fderiv ℝ φ y w)
        ((0 : A), fderiv ℝ φ y w) := by
  set D := fderiv ℝ φ y with hD
  have hv : (fun η' : E => velocityTerm (pullback L φ) (y, η')) =
      fun η' => (velocityTerm L (φ y, D η')).comp D := by
    funext η'
    exact pullback_velocity hφ (hL1 η')
  have hdv : DifferentiableAt ℝ (velocityTerm L) (jetMap φ (y, η)) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ L) (jetMap φ (y, η)) :=
      hL2.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun a => (fderiv ℝ L a).comp
        (ContinuousLinearMap.inr ℝ A A)) (jetMap φ (y, η)) := h1.clm_comp contDiffAt_const
    exact h2.differentiableAt (by norm_num)
  have hin : HasFDerivAt (fun η' : E => (φ y, D η'))
      ((ContinuousLinearMap.inr ℝ A A).comp D) η := by
    have h := (hasFDerivAt_prodMk_right (𝕜 := ℝ) (φ y) (D η)).comp η D.hasFDerivAt
    simpa [Function.comp_def] using h
  have hdv' : DifferentiableAt ℝ (velocityTerm L) (φ y, D η) := hdv
  have hg0 := hdv'.hasFDerivAt.comp η hin
  have hg : HasFDerivAt (fun η' : E => velocityTerm L (φ y, D η'))
      ((fderiv ℝ (velocityTerm L) (φ y, D η)).comp
        ((ContinuousLinearMap.inr ℝ A A).comp D)) η := hg0
  let P : (A →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E A ℝ).flip D
  have hP0 := P.hasFDerivAt.comp η hg
  have hP : HasFDerivAt (fun η' : E => (velocityTerm L (φ y, D η')).comp D)
      (P.comp ((fderiv ℝ (velocityTerm L) (φ y, D η)).comp
        ((ContinuousLinearMap.inr ℝ A A).comp D))) η := hP0
  unfold velocityHessian
  simp only
  rw [hv, hP.fderiv]
  have hvt : fderiv ℝ (velocityTerm L) (φ y, D η) =
      fun a => (fderiv ℝ (fderiv ℝ L) (φ y, D η) a).comp (ContinuousLinearMap.inr ℝ A A) := by
    have h1 : DifferentiableAt ℝ (fderiv ℝ L) (φ y, D η) :=
      (hL2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h2 := ((ContinuousLinearMap.compL ℝ A (A × A) ℝ).flip
      (ContinuousLinearMap.inr ℝ A A)).hasFDerivAt.comp (φ y, D η) h1.hasFDerivAt
    ext a b
    have h3 := congrArg (fun T : A × A →L[ℝ] A →L[ℝ] ℝ => T a b) h2.fderiv
    exact h3
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.inr_apply, P]
  rw [hvt]
  rfl

end Pullback

variable {n : ℕ}

/-- The coordinate velocity Hessian is positive at nonzero velocity. -/
theorem coordinate_velocityHessian_pos (F : ReversibleMetric n) (p : Sphere n)
    {y η w : Coordinates n} (hy : y ∈ (extChartAt (𝓡 n) p).target) (hη : η ≠ 0) (hw : w ≠ 0) :
    0 < velocityHessian (coordinateLagrangian F p) (y, η) w w := by
  have hφ : ContDiffAt ℝ 2 (inverseAmbient p) y :=
    (inverseAmbient_smoothAt p hy).of_le (by simp)
  have hjet := inverseAmbient_jet_mem_slitDomain p (z := (y, η)) hy hη
  have hL1 : ∀ η' : Coordinates n,
      ContDiffAt ℝ 1 (lagrangian F) (jetMap (inverseAmbient p) (y, η')) := by
    intro η'
    exact Finsler.AmbientEnergyRegularity.lagrangian_contDiffAt_one F
      (ne_zero_of_mem_unit_sphere (inverseSphere p y))
  have hL2 : ContDiffAt ℝ 2 (lagrangian F) (jetMap (inverseAmbient p) (y, η)) :=
    (lagrangian_smoothAt F hjet).of_le (by simp)
  change 0 < velocityHessian (pullback (lagrangian F) (inverseAmbient p)) (y, η) w w
  rw [velocityHessian_pullback_apply hφ hL1 hL2 w]
  have hq : ‖inverseAmbient p y‖ = 1 := by simp [inverseAmbient]
  have htan : ∀ a : Coordinates n, ⟪inverseAmbient p y, fderiv ℝ (inverseAmbient p) y a⟫ = 0 :=
    fun a => inverseAmbient_fderiv_tangent p hy a
  have hinj : ∀ a : Coordinates n, a ≠ 0 → fderiv ℝ (inverseAmbient p) y a ≠ 0 := by
    intro a ha
    rw [inverseAmbient_fderiv p hy]
    change ambientMap (inverseSphere p y)
      (mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y a) ≠ 0
    intro h0
    apply inverseSphere_derivative_ne_zero p hy ha
    exact (ambientMap_injective (inverseSphere p y)) (h0.trans (map_zero _).symm)
  exact Finsler.SobolevSmoothRegularity.lagrangian_hessian_tangent_pos F hq (htan η)
    (hinj η hη) (htan w) (hinj w hw)

theorem coordinate_velocityHessian_injective (F : ReversibleMetric n) (p : Sphere n)
    {y η : Coordinates n} (hy : y ∈ (extChartAt (𝓡 n) p).target) (hη : η ≠ 0) :
    Injective (velocityHessian (coordinateLagrangian F p) (y, η)) :=
  injective_of_pos _ fun _ hw => coordinate_velocityHessian_pos F p hy hη hw

/-- The coordinate spray is smooth (every finite order) away from zero velocity. -/
theorem coordinate_spray_contDiffAt (F : ReversibleMetric n) (p : Sphere n)
    {y η : Coordinates n} (hy : y ∈ (extChartAt (𝓡 n) p).target) (hη : η ≠ 0) (k : ℕ) :
    ContDiffAt ℝ k (spray (coordinateLagrangian F p)) (y, η) :=
  spray_contDiffAt _ ((coordinateLagrangian_smoothAt_nonzero F p (z := (y, η)) hy hη).of_le
    (by simp)) (coordinate_velocityHessian_injective F p hy hη)

/-- Integral curves of the coordinate spray solve the coordinate Euler–Lagrange equation. -/
theorem coordinate_residual_eq_zero (F : ReversibleMetric n) (p : Sphere n) {x : ℝ → Coordinates n}
    {t : ℝ} (hx : ContDiffAt ℝ 2 x t) (hy : x t ∈ (extChartAt (𝓡 n) p).target)
    (hv : deriv x t ≠ 0)
    (hacc : deriv (deriv x) t = spray (coordinateLagrangian F p) (curveJet x t)) :
    residual (coordinateLagrangian F p) x t = 0 :=
  residual_eq_zero_of_spray _ hx
    ((coordinateLagrangian_smoothAt_nonzero F p (z := curveJet x t) hy hv).of_le (by simp))
    (coordinate_velocityHessian_injective F p hy hv) hacc

/-- The coordinate spray is quadratic in the velocity. -/
theorem coordinate_spray_smul (F : ReversibleMetric n) (p : Sphere n)
    {y η : Coordinates n} (hy : y ∈ (extChartAt (𝓡 n) p).target) (hη : η ≠ 0) {r : ℝ}
    (hr : r ≠ 0) :
    spray (coordinateLagrangian F p) (y, r • η) = (r ^ 2) • spray (coordinateLagrangian F p) (y, η) := by
  have hdiff : ∀ y' ∈ (extChartAt (𝓡 n) p).target, ∀ w' : Coordinates n,
      DifferentiableAt ℝ (coordinateLagrangian F p) (y', w') :=
    fun y' hy' w' => (coordinateLagrangian_contDiffAt_one F p (z := (y', w')) hy').differentiableAt
      (by norm_num)
  have hvt : ∀ {z : Coordinates n × Coordinates n}, z.1 ∈ (extChartAt (𝓡 n) p).target → z.2 ≠ 0 →
      DifferentiableAt ℝ (velocityTerm (coordinateLagrangian F p)) z := by
    intro z hz1 hz2
    have h2 : ContDiffAt ℝ 2 (coordinateLagrangian F p) z :=
      (coordinateLagrangian_smoothAt_nonzero F p hz1 hz2).of_le (by simp)
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (coordinateLagrangian F p)) z :=
      h2.fderiv_right (m := 1) (by norm_num)
    exact (h1.clm_comp contDiffAt_const).differentiableAt (by norm_num)
  have hv : DifferentiableAt ℝ (fun w' => velocityTerm (coordinateLagrangian F p) (y, w')) η :=
    (hvt (z := (y, η)) hy hη).comp η (differentiableAt_const y |>.prodMk differentiableAt_id)
  have hvr : DifferentiableAt ℝ (fun w' => velocityTerm (coordinateLagrangian F p) (y, w'))
      (r • η) :=
    (hvt (z := (y, r • η)) hy (smul_ne_zero hr hη)).comp (r • η)
      (differentiableAt_const y |>.prodMk differentiableAt_id)
  have hm0 := (hvt (z := (y, η)) hy hη).comp y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) y η).differentiableAt
  have hm : DifferentiableAt ℝ (fun y' => velocityTerm (coordinateLagrangian F p) (y', η)) y := hm0
  exact spray_smul (fun y' w' r' => coordinateLagrangian_velocity_smul F p y' r' w')
    (chartTarget_isOpen p) hy hr hdiff hv hvr hm

section Flow

/-- The coordinate geodesic vector field (position, velocity) ↦ (velocity, spray). -/
def geodesicField (F : ReversibleMetric n) (p : Sphere n) (z : Coordinates n × Coordinates n) :
    Coordinates n × Coordinates n :=
  (z.2, spray (coordinateLagrangian F p) z)

/-- Jets with position in the chart and nonzero velocity. -/
def slitJets (p : Sphere n) : Set (Coordinates n × Coordinates n) :=
  {z | z.1 ∈ (extChartAt (𝓡 n) p).target ∧ z.2 ≠ 0}

theorem slitJets_isOpen (p : Sphere n) : IsOpen (slitJets p) :=
  ((chartTarget_isOpen p).preimage continuous_fst).inter
    (isOpen_ne_fun continuous_snd continuous_const)

theorem geodesicField_contDiffOn (F : ReversibleMetric n) (p : Sphere n) (k : ℕ) :
    ContDiffOn ℝ k (geodesicField F p) (slitJets p) :=
  fun _ hz => (contDiffAt_snd.prodMk (coordinate_spray_contDiffAt F p hz.1 hz.2 k)).contDiffWithinAt

/-- Local geodesic flow in a sphere chart, C^(k+1) in the initial jet and the time. -/
theorem exists_localFlow (F : ReversibleMetric n) (p : Sphere n)
    {z₀ : Coordinates n × Coordinates n} (hz₀ : z₀ ∈ slitJets p) (k : ℕ) :
    ∃ Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n,
      ContDiffAt ℝ (k + 1) (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2) (z₀, 0) ∧
      (∀ z, Φ z 0 = z) ∧ (∀ z t u, Φ z (t + u) = Φ (Φ z t) u) ∧
      ∀ᶠ q in 𝓝 ((z₀, 0) : (Coordinates n × Coordinates n) × ℝ),
        HasDerivAt (Φ q.1) (geodesicField F p (Φ q.1 q.2)) q.2 := by
  have hv : ContDiffOn ℝ (((k : ℕ∞) + 1 : ℕ∞) : WithTop ℕ∞) (geodesicField F p) (slitJets p) := by
    have h := geodesicField_contDiffOn F p (k + 1)
    exact_mod_cast h
  obtain ⟨Φ, hΦ, h0, hadd, hode⟩ := ODE.exists_contDiffAt_localFlow (geodesicField F p)
    hv ((slitJets_isOpen p).mem_nhds hz₀)
  refine ⟨Φ, ?_, h0, hadd, hode⟩
  exact_mod_cast hΦ

end Flow

end

end Finsler.CoordinateSpray
