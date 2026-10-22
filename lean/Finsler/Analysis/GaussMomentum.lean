module

public import Finsler.Analysis.LagrangianSpray
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The Gauss lemma in momentum form, without differentiating under an integral. For a C³ family
c(ε,t) of Euler–Lagrange curves with fixed initial point and with energy density L(c,ċ)
independent of t, the pairing φ(t) of the momentum with the Jacobi field J = ∂_ε c has
derivative ∂_ε L(c,ċ) (Euler–Lagrange equation and symmetry of mixed partials), which is the
constant ε-derivative of the energy; since J(0) = 0, the endpoint pairing equals that
derivative. -/

@[expose] public section

namespace Finsler.GaussMomentum

open Finsler.EulerCovariance Function Filter Set
open scoped ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The ε-derivative (Jacobi field) of a two-parameter family. -/
def jacobi (c : ℝ × ℝ → E) (q : ℝ × ℝ) : E := fderiv ℝ c q (1, 0)

/-- The t-derivative (velocity) of a two-parameter family. -/
def vel (c : ℝ × ℝ → E) (q : ℝ × ℝ) : E := fderiv ℝ c q (0, 1)

theorem hasDerivAt_t {c : ℝ × ℝ → E} {ε t : ℝ} (hc : DifferentiableAt ℝ c (ε, t)) :
    HasDerivAt (fun s => c (ε, s)) (vel c (ε, t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => (ε, s)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t ε).prodMk (hasDerivAt_id t)
  exact hc.hasFDerivAt.comp_hasDerivAt t h1

theorem hasDerivAt_ε {c : ℝ × ℝ → E} {ε t : ℝ} (hc : DifferentiableAt ℝ c (ε, t)) :
    HasDerivAt (fun e => c (e, t)) (jacobi c (ε, t)) ε := by
  have h1 : HasDerivAt (fun e : ℝ => (e, t)) ((1 : ℝ), (0 : ℝ)) ε :=
    (hasDerivAt_id ε).prodMk (hasDerivAt_const ε t)
  exact hc.hasFDerivAt.comp_hasDerivAt ε h1

/-- Symmetry of mixed partials: the t-derivative of the Jacobi field is the ε-derivative of the
velocity. -/
theorem jacobi_vel_symm {c : ℝ × ℝ → E} {q : ℝ × ℝ} (hc : ContDiffAt ℝ 2 c q) :
    fderiv ℝ (jacobi c) q (0, 1) = fderiv ℝ (vel c) q (1, 0) := by
  have hdd : DifferentiableAt ℝ (fderiv ℝ c) q :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hJ : fderiv ℝ (jacobi c) q = (fderiv ℝ (fderiv ℝ c) q).flip (1, 0) := by
    have h := (ContinuousLinearMap.apply ℝ E ((1 : ℝ), (0 : ℝ))).hasFDerivAt.comp q hdd.hasFDerivAt
    exact ContinuousLinearMap.ext fun w => congrArg (fun T : ℝ × ℝ →L[ℝ] E => T w) h.fderiv
  have hV : fderiv ℝ (vel c) q = (fderiv ℝ (fderiv ℝ c) q).flip (0, 1) := by
    have h := (ContinuousLinearMap.apply ℝ E ((0 : ℝ), (1 : ℝ))).hasFDerivAt.comp q hdd.hasFDerivAt
    exact ContinuousLinearMap.ext fun w => congrArg (fun T : ℝ × ℝ →L[ℝ] E => T w) h.fderiv
  rw [hJ, hV]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hc.isSymmSndFDerivAt (by simp)) _ _

/-- The Gauss lemma in momentum form: the endpoint momentum paired with the Jacobi field equals the
ε-derivative of the (t-independent) energy density. -/
theorem endpoint_momentum {L : E × E → ℝ} {c : ℝ × ℝ → E} (hc : ContDiff ℝ 3 c)
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 L (c (0, t), vel c (0, t)))
    (hres : ∀ t ∈ Icc (0 : ℝ) 1, residual L (fun s => c (0, s)) t = 0)
    (hfix : ∀ ε, c (ε, 0) = c (0, 0))
    (hconst : ∀ ε t, L (c (ε, t), vel c (ε, t)) = L (c (ε, 0), vel c (ε, 0)))
    {D : ℝ} (hD : HasDerivAt (fun ε => L (c (ε, 0), vel c (ε, 0))) D 0) :
    velocityTerm L (c (0, 1), vel c (0, 1)) (jacobi c (0, 1)) = D := by
  set x : ℝ → E := fun s => c (0, s) with hx
  have hcd : ∀ q, DifferentiableAt ℝ c q := fun q => (hc.differentiable (by norm_num)) q
  have hc2 : ∀ q, ContDiffAt ℝ 2 c q := fun q => (hc.of_le (by norm_num)).contDiffAt
  -- the velocity of x is vel c
  have hxd : ∀ t, deriv x t = vel c (0, t) := fun t => (hasDerivAt_t (hcd (0, t))).deriv
  have hjet : ∀ t, curveJet x t = (c (0, t), vel c (0, t)) := by
    intro t
    change (x t, deriv x t) = _
    rw [hxd t]
  -- smoothness of x
  have hxC2 : ∀ t, ContDiffAt ℝ 2 x t := by
    intro t
    have h : ContDiff ℝ 3 x := hc.comp (contDiff_const.prodMk contDiff_id)
    exact (h.of_le (by norm_num)).contDiffAt
  -- the Jacobi and velocity fields are differentiable
  have hJd : ∀ q, DifferentiableAt ℝ (jacobi c) q := by
    intro q
    have h : ContDiff ℝ 2 (fderiv ℝ c) := hc.fderiv_right (m := 2) (by norm_num)
    exact ((h.clm_apply contDiff_const).differentiable (by norm_num)) q
  have hVd : ∀ q, DifferentiableAt ℝ (vel c) q := by
    intro q
    have h : ContDiff ℝ 2 (fderiv ℝ c) := hc.fderiv_right (m := 2) (by norm_num)
    exact ((h.clm_apply contDiff_const).differentiable (by norm_num)) q
  -- the pairing φ and its derivative
  let φ : ℝ → ℝ := fun t => momentum L x t (jacobi c (0, t))
  have hφ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ D t := by
    intro t ht
    have hLt : ContDiffAt ℝ 2 L (curveJet x t) := by rw [hjet t]; exact hL t ht
    have hmom : HasDerivAt (momentum L x) (deriv (momentum L x) t) t :=
      ((momentum_smoothAt (hxC2 t) hLt).differentiableAt (by norm_num)).hasDerivAt
    have hJ : HasDerivAt (fun s => jacobi c (0, s)) (fderiv ℝ (jacobi c) (0, t) (0, 1)) t :=
      hasDerivAt_t (hJd (0, t))
    have hpair := hmom.clm_apply hJ
    have hEL : deriv (momentum L x) t = positionTerm L (curveJet x t) := by
      have h := hres t ht
      rw [Finsler.EulerCovariance.residual, sub_eq_zero] at h
      exact h.symm
    rw [hEL, jacobi_vel_symm (hc2 (0, t))] at hpair
    -- the ε-derivative of the energy density at t
    have hLd : DifferentiableAt ℝ L (c (0, t), vel c (0, t)) :=
      (hL t ht).differentiableAt (by norm_num)
    have hjetε : HasDerivAt (fun e => (c (e, t), vel c (e, t)))
        (jacobi c (0, t), fderiv ℝ (vel c) (0, t) (1, 0)) 0 :=
      (hasDerivAt_ε (hcd (0, t))).prodMk (hasDerivAt_ε (hVd (0, t)))
    have hE : HasDerivAt (fun e => L (c (e, t), vel c (e, t)))
        (fderiv ℝ L (c (0, t), vel c (0, t))
          (jacobi c (0, t), fderiv ℝ (vel c) (0, t) (1, 0))) 0 :=
      hLd.hasFDerivAt.comp_hasDerivAt 0 hjetε
    have hE' : HasDerivAt (fun e => L (c (e, t), vel c (e, t))) D 0 := by
      have hfun : (fun e => L (c (e, t), vel c (e, t))) = fun e => L (c (e, 0), vel c (e, 0)) :=
        funext fun e => hconst e t
      rw [hfun]
      exact hD
    have huniq := hE.unique hE'
    rw [differential_split] at huniq
    rw [hjet t] at hpair
    have heq : positionTerm L (c (0, t), vel c (0, t)) (jacobi c (0, t)) +
        momentum L x t (fderiv ℝ (vel c) (0, t) (1, 0)) = D := by
      rw [← huniq]
      simp only [momentum, hjet t]
    rw [heq] at hpair
    exact hpair
  -- φ(1) − φ(0) = D and φ(0) = 0
  have hψ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => φ t - D * t) 0 t := by
    intro t ht
    have h := (hφ t ht).sub ((hasDerivAt_id t).const_mul D)
    exact h.congr_deriv (by ring)
  have hconstψ := constant_of_has_deriv_right_zero
    (f := fun t => φ t - D * t) (a := 0) (b := 1)
    (fun t ht => (hψ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hψ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 (right_mem_Icc.mpr zero_le_one)
  have hJ0 : jacobi c (0, 0) = 0 := by
    have h := hasDerivAt_ε (hcd (0, 0))
    have hconst0 : (fun e => c (e, 0)) = fun _ => c (0, 0) := funext hfix
    rw [hconst0] at h
    exact h.unique (hasDerivAt_const 0 (c (0, 0)))
  have hφ0 : φ 0 = 0 := by
    simp only [φ, hJ0, map_zero]
  have hφ1 : φ 1 = velocityTerm L (c (0, 1), vel c (0, 1)) (jacobi c (0, 1)) := by
    simp only [φ, momentum, hjet 1]
  simp only [hφ0, mul_zero, sub_zero, mul_one] at hconstψ
  rw [← hφ1]
  linarith

end

end Finsler.GaussMomentum
