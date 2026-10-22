module

public import Finsler.Analysis.GaussMomentumLocal

/-! The first variation for a local family of Euler--Lagrange curves with both endpoints moving.
Constant energy density and the Euler equation give the endpoint momentum difference. The
identity uses the actual derivatives of the family and does not assume fixed endpoints. -/

@[expose] public section

namespace Finsler.BoundaryMomentum

open Finsler.EulerCovariance Finsler.GaussMomentum Function Filter Set
open scoped ContDiff Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the constant energy density equals final momentum minus initial momentum,
each evaluated on its endpoint variation. -/
theorem boundary_momentum_local {L : E × E → ℝ} {c : ℝ × ℝ → E}
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 3 c (0, t))
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 L (c (0, t), vel c (0, t)))
    (hres : ∀ t ∈ Icc (0 : ℝ) 1, residual L (fun s => c (0, s)) t = 0)
    (hconst : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ ε in 𝓝 (0 : ℝ),
      L (c (ε, t), vel c (ε, t)) = L (c (ε, 0), vel c (ε, 0)))
    {D : ℝ} (hD : HasDerivAt (fun ε => L (c (ε, 0), vel c (ε, 0))) D 0) :
    velocityTerm L (c (0, 1), vel c (0, 1)) (jacobi c (0, 1)) -
      velocityTerm L (c (0, 0), vel c (0, 0)) (jacobi c (0, 0)) = D := by
  set x : ℝ → E := fun s => c (0, s) with hx
  have hcd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ c (0, t) :=
    fun t ht => (hc t ht).differentiableAt (by norm_num)
  have hc2 : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 c (0, t) :=
    fun t ht => (hc t ht).of_le (by norm_num)
  have hxd : ∀ t ∈ Icc (0 : ℝ) 1, deriv x t = vel c (0, t) :=
    fun t ht => (hasDerivAt_t (hcd t ht)).deriv
  have hjet : ∀ t ∈ Icc (0 : ℝ) 1, curveJet x t = (c (0, t), vel c (0, t)) := by
    intro t ht
    change (x t, deriv x t) = _
    rw [hxd t ht]
  have hxC2 : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 x t := by
    intro t ht
    have h : ContDiffAt ℝ 3 x t :=
      (hc t ht).comp t (contDiffAt_const.prodMk contDiffAt_id)
    exact h.of_le (by norm_num)
  have hfd : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (fderiv ℝ c) (0, t) :=
    fun t ht => (hc t ht).fderiv_right (m := 2) (by norm_num)
  have hJd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (jacobi c) (0, t) := by
    intro t ht
    have h : ContDiffAt ℝ 2 (jacobi c) (0, t) := (hfd t ht).clm_apply contDiffAt_const
    exact h.differentiableAt (by norm_num)
  have hVd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (vel c) (0, t) := by
    intro t ht
    have h : ContDiffAt ℝ 2 (vel c) (0, t) := (hfd t ht).clm_apply contDiffAt_const
    exact h.differentiableAt (by norm_num)
  let φ : ℝ → ℝ := fun t => momentum L x t (jacobi c (0, t))
  have hφ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt φ D t := by
    intro t ht
    have hLt : ContDiffAt ℝ 2 L (curveJet x t) := by rw [hjet t ht]; exact hL t ht
    have hmom : HasDerivAt (momentum L x) (deriv (momentum L x) t) t :=
      ((momentum_smoothAt (hxC2 t ht) hLt).differentiableAt (by norm_num)).hasDerivAt
    have hJ : HasDerivAt (fun s => jacobi c (0, s)) (fderiv ℝ (jacobi c) (0, t) (0, 1)) t :=
      hasDerivAt_t (hJd t ht)
    have hpair := hmom.clm_apply hJ
    have hEL : deriv (momentum L x) t = positionTerm L (curveJet x t) := by
      have h := hres t ht
      rw [Finsler.EulerCovariance.residual, sub_eq_zero] at h
      exact h.symm
    rw [hEL, jacobi_vel_symm (hc2 t ht)] at hpair
    have hLd : DifferentiableAt ℝ L (c (0, t), vel c (0, t)) :=
      (hL t ht).differentiableAt (by norm_num)
    have hjetε : HasDerivAt (fun e => (c (e, t), vel c (e, t)))
        (jacobi c (0, t), fderiv ℝ (vel c) (0, t) (1, 0)) 0 :=
      (hasDerivAt_ε (hcd t ht)).prodMk (hasDerivAt_ε (hVd t ht))
    have hE : HasDerivAt (fun e => L (c (e, t), vel c (e, t)))
        (fderiv ℝ L (c (0, t), vel c (0, t))
          (jacobi c (0, t), fderiv ℝ (vel c) (0, t) (1, 0))) 0 :=
      hLd.hasFDerivAt.comp_hasDerivAt 0 hjetε
    have hE' : HasDerivAt (fun e => L (c (e, t), vel c (e, t))) D 0 :=
      hD.congr_of_eventuallyEq ((hconst t ht).mono fun e he => he)
    have huniq := hE.unique hE'
    rw [differential_split] at huniq
    rw [hjet t ht] at hpair
    have heq : positionTerm L (c (0, t), vel c (0, t)) (jacobi c (0, t)) +
        momentum L x t (fderiv ℝ (vel c) (0, t) (1, 0)) = D := by
      rw [← huniq]
      simp only [momentum, hjet t ht]
    rw [heq] at hpair
    exact hpair
  have hψ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => φ t - D * t) 0 t := by
    intro t ht
    have h := (hφ t ht).sub ((hasDerivAt_id t).const_mul D)
    exact h.congr_deriv (by ring)
  have hconstψ := constant_of_has_deriv_right_zero
    (f := fun t => φ t - D * t) (a := 0) (b := 1)
    (fun t ht => (hψ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hψ t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 (right_mem_Icc.mpr zero_le_one)
  have hφ0 : φ 0 = velocityTerm L (c (0, 0), vel c (0, 0)) (jacobi c (0, 0)) := by
    simp only [φ, momentum, hjet 0 (left_mem_Icc.mpr zero_le_one)]
  have hφ1 : φ 1 = velocityTerm L (c (0, 1), vel c (0, 1)) (jacobi c (0, 1)) := by
    simp only [φ, momentum, hjet 1 (right_mem_Icc.mpr zero_le_one)]
  simp only [hφ0, hφ1, mul_zero, sub_zero, mul_one] at hconstψ
  linarith


end

end Finsler.BoundaryMomentum
