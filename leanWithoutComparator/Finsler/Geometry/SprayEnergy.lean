module

public import Finsler.Geometry.CoordinateSpray

/-! Energy conservation along Euler–Lagrange curves of a Lagrangian that is quadratic in the
velocity. The momentum paired with the velocity is twice the Lagrangian (Euler), its derivative
is the derivative of the Lagrangian along the jet when the residual vanishes, so the derivative of
the Lagrangian along the curve is zero. For the coordinate Finsler Lagrangian this gives constant
speed along coordinate geodesics. -/

@[expose] public section

namespace Finsler.SprayEnergy

open Finsler.EulerCovariance Finsler.LagrangianSpray Function Filter
open scoped ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Euler's identity for a differentiable Lagrangian quadratic in the velocity. -/
theorem velocityTerm_self (L : E × E → ℝ)
    (hhom : ∀ (y w : E) (r : ℝ), L (y, r • w) = r ^ 2 * L (y, w)) {z : E × E}
    (hd : DifferentiableAt ℝ L z) : velocityTerm L z z.2 = 2 * L z := by
  have hv : HasFDerivAt (fun w : E => L (z.1, w))
      ((fderiv ℝ L z).comp (ContinuousLinearMap.inr ℝ E E)) z.2 := by
    have h := hd.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
    simpa [Function.comp_def] using h
  have h := hv.apply_self_eq_nsmul_of_homogeneous (k := 2)
    (fun r w => by simpa only [smul_eq_mul] using hhom z.1 w r)
  simpa only [nsmul_eq_mul, Nat.cast_ofNat, velocityTerm, Prod.mk.eta] using h

/-- Along a C² curve with vanishing Euler–Lagrange residual, the Lagrangian of a velocity-quadratic
Lagrangian has zero derivative. -/
theorem lagrangian_hasDerivAt_zero (L : E × E → ℝ)
    (hhom : ∀ (y w : E) (r : ℝ), L (y, r • w) = r ^ 2 * L (y, w))
    {x : ℝ → E} {t : ℝ} (hdiff : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ L (curveJet x s))
    (hx : ContDiffAt ℝ 2 x t) (hL : ContDiffAt ℝ 2 L (curveJet x t))
    (hres : residual L x t = 0) :
    HasDerivAt (fun s => L (curveJet x s)) 0 t := by
  have h1 : HasDerivAt x (deriv x t) t := (hx.differentiableAt (by norm_num)).hasDerivAt
  have hd1 : ContDiffAt ℝ 1 (deriv x) t := hx.derivWithin (m := 1) (by norm_num)
  have h2 : HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    (hd1.differentiableAt (by norm_num)).hasDerivAt
  have hjet : HasDerivAt (curveJet x) (deriv x t, deriv (deriv x) t) t := h1.prodMk h2
  have hLd : HasDerivAt (fun s => L (curveJet x s))
      (fderiv ℝ L (curveJet x t) (deriv x t, deriv (deriv x) t)) t :=
    hdiff.self_of_nhds.hasFDerivAt.comp_hasDerivAt t hjet
  -- momentum and its derivative
  have hmom : ContDiffAt ℝ 1 (momentum L x) t := momentum_smoothAt hx hL
  have hm : HasDerivAt (momentum L x) (deriv (momentum L x) t) t :=
    (hmom.differentiableAt (by norm_num)).hasDerivAt
  have hpair : HasDerivAt (fun s => momentum L x s (deriv x s))
      (deriv (momentum L x) t (deriv x t) + momentum L x t (deriv (deriv x) t)) t :=
    hm.clm_apply h2
  have heul : (fun s => momentum L x s (deriv x s)) =ᶠ[𝓝 t] fun s => 2 * L (curveJet x s) := by
    filter_upwards [hdiff] with s hs
    exact velocityTerm_self L hhom hs
  replace hpair := hpair.congr_of_eventuallyEq heul.symm
  have hpair' := hLd.const_mul 2
  have huniq := hpair.unique hpair'
  have hres' : deriv (momentum L x) t = positionTerm L (curveJet x t) := by
    have := hres
    rw [Finsler.EulerCovariance.residual, sub_eq_zero] at this
    exact this.symm
  rw [hres'] at huniq
  have hsplit := differential_split L (curveJet x t) (deriv x t) (deriv (deriv x) t)
  change positionTerm L (curveJet x t) (deriv x t) +
      velocityTerm L (curveJet x t) (deriv (deriv x) t) =
    2 * fderiv ℝ L (curveJet x t) (deriv x t, deriv (deriv x) t) at huniq
  rw [hsplit] at huniq hLd
  have hzero : positionTerm L (curveJet x t) (deriv x t) +
      velocityTerm L (curveJet x t) (deriv (deriv x) t) = 0 := by linarith
  rw [hzero] at hLd
  exact hLd

section Coordinate

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open scoped Manifold

variable {n : ℕ}

/-- Constant speed along coordinate geodesics: a C² chart curve whose acceleration is the
coordinate spray has locally constant coordinate Finsler energy density. -/
theorem coordinate_lagrangian_hasDerivAt_zero (F : ReversibleMetric n) (p : Sphere n)
    {x : ℝ → Coordinates n} {t : ℝ} (hx : ContDiffAt ℝ 2 x t)
    (hy : x t ∈ (extChartAt (𝓡 n) p).target) (hv : deriv x t ≠ 0)
    (hacc : deriv (deriv x) t = spray (coordinateLagrangian F p) (curveJet x t)) :
    HasDerivAt (fun s => coordinateLagrangian F p (curveJet x s)) 0 t := by
  have hcont : ContinuousAt x t := hx.continuousAt
  have hev : ∀ᶠ s in 𝓝 t, x s ∈ (extChartAt (𝓡 n) p).target :=
    hcont.preimage_mem_nhds ((chartTarget_isOpen p).mem_nhds hy)
  have hdiff : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ (coordinateLagrangian F p) (curveJet x s) := by
    filter_upwards [hev] with s hs
    exact (coordinateLagrangian_contDiffAt_one F p (z := curveJet x s) hs).differentiableAt
      (by norm_num)
  exact lagrangian_hasDerivAt_zero _ (fun y w r => coordinateLagrangian_velocity_smul F p y r w)
    hdiff hx ((coordinateLagrangian_smoothAt_nonzero F p (z := curveJet x t) hy hv).of_le (by simp))
    (coordinate_residual_eq_zero F p hx hy hv hacc)

end Coordinate

end

end Finsler.SprayEnergy
