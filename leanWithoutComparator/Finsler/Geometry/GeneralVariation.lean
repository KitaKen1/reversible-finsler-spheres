module

public import Finsler.Geometry.PointwiseEuler

/-! The actual jet of every smooth periodic sphere variation.
Its transverse derivative is a genuine smooth periodic tangent field, and its
jet derivative is (eta, eta'). Thus its first variation agrees with the explicit
normalized variation realizing that same field. This proves both directions
between actual variational stationarity and the constrained ambient Euler
condition for regular smooth loops. Ordinary coordinate comparison is separate. -/

@[expose] public section

namespace Finsler.GeneralVariation

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.SphereVariation Finsler.AmbientLagrangian Finsler.WeakEulerLagrange
open Finsler.PointwiseEuler TauCeti.Manifold Function
open scoped Manifold ContDiff Interval RealInnerProductSpace

noncomputable section

variable {n : ℕ}

def ambientFamily (V : SmoothVariation n) (z : ℝ × ℝ) : Ambient n := (V.family z : Ambient n)

theorem ambientFamily_smooth (V : SmoothVariation n) : ContDiff ℝ ∞ (ambientFamily V) :=
  ((inclusion_smooth n).comp V.smooth).contDiff

def transverse (V : SmoothVariation n) (t : ℝ) : Ambient n :=
  fderiv ℝ (ambientFamily V) (0, t) (1, 0)

theorem transverse_hasDerivAt (V : SmoothVariation n) (t : ℝ) :
    HasDerivAt (fun s => ambientFamily V (s, t)) (transverse V t) 0 := by
  simpa only [timeFDeriv_apply, transverse] using
    hasDerivAt_parameterCurve ((ambientFamily_smooth V).differentiable (by simp) (0, t))

theorem transverse_smooth (V : SmoothVariation n) : ContDiff ℝ ∞ (transverse V) :=
  (((ambientFamily_smooth V).fderiv_right (by simp)).clm_apply contDiff_const).comp
    ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)

theorem transverse_periodic (V : SmoothVariation n) : Periodic (transverse V) 1 := by
  intro t
  have he : (fun s => ambientFamily V (s, t + 1)) =
      (fun s => ambientFamily V (s, t)) :=
    funext fun s => congrArg Subtype.val (V.periodic s t)
  have hh := transverse_hasDerivAt V (t + 1)
  rw [he] at hh
  exact hh.unique (transverse_hasDerivAt V t)

theorem transverse_tangent (V : SmoothVariation n) (t : ℝ) :
    ⟪(V.family (0, t) : Ambient n), transverse V t⟫ = 0 := by
  have hh := (transverse_hasDerivAt V t).norm_sq
  have he : (fun s => ‖ambientFamily V (s, t)‖ ^ 2) = (fun _ : ℝ => (1 : ℝ)) := by
    funext s
    simp [ambientFamily]
  rw [he] at hh
  have hz := hh.unique (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  change 2 * ⟪(V.family (0, t) : Ambient n), transverse V t⟫ = 0 at hz
  linarith

/-- The actual transverse field of the given family, on its actual central loop. -/
def transverseField (V : SmoothVariation n) : SmoothTangentField (loopAt V 0) where
  value := transverse V
  smooth := transverse_smooth V
  periodic := transverse_periodic V
  tangent := transverse_tangent V

def timeVelocity (V : SmoothVariation n) (z : ℝ × ℝ) : Ambient n :=
  fderiv ℝ (ambientFamily V) z (0, 1)

theorem timeVelocity_eq_deriv (V : SmoothVariation n) (s t : ℝ) :
    timeVelocity V (s, t) = deriv (fun r => ambientFamily V (s, r)) t := by
  have h := (hasFDerivAt_timeSlice
    ((ambientFamily_smooth V).differentiable (by simp) (s, t))).hasDerivAt
  simpa only [spatialFDeriv_apply, timeVelocity] using h.deriv.symm

theorem timeVelocity_smooth (V : SmoothVariation n) : ContDiff ℝ ∞ (timeVelocity V) :=
  ((ambientFamily_smooth V).fderiv_right (by simp)).clm_apply contDiff_const

theorem timeVelocity_eq_ambientVelocity (V : SmoothVariation n) (s t : ℝ) :
    ambientVector n (Finsler.FirstVariation.velocityLift V (s, t)) =
      timeVelocity V (s, t) := by
  have hd := hasDerivAt_comp_curve (t := t) (g := inclusion n)
    ((inclusion_smooth n).mdifferentiableAt (by simp))
    (hasMFDerivAt_curveVelocity ((loopAt V s).smooth.mdifferentiableAt (by simp)))
  rw [Finsler.FirstVariation.velocityLift_eq_loopVelocity,
    Finsler.LoopEnergy.velocityLift, curveVelocityLift_apply, timeVelocity_eq_deriv]
  exact hd.deriv.symm

theorem ambientJet_eq (V : SmoothVariation n) (z : ℝ × ℝ) :
    ambientJet V z = (ambientFamily V z, timeVelocity V z) := by
  rcases z with ⟨s, t⟩
  exact congrArg (fun v => (ambientFamily V (s, t), v))
    (timeVelocity_eq_ambientVelocity V s t)

theorem mixed_deriv (V : SmoothVariation n) (t : ℝ) :
    deriv (fun s => deriv (fun r => ambientFamily V (s, r)) t) 0 =
      deriv (transverse V) t := by
  have h := deriv_deriv_comm (t := 0) (x := t)
    ((ambientFamily_smooth V).contDiffAt.of_le (by simp))
  rw [h]
  have he : (fun r => deriv (fun s => ambientFamily V (s, r)) 0) = transverse V :=
    funext fun r => (transverse_hasDerivAt V r).deriv
  rw [he]

theorem timeVelocity_hasDerivAt (V : SmoothVariation n) (t : ℝ) :
    HasDerivAt (fun s => timeVelocity V (s, t)) (deriv (transverse V) t) 0 := by
  have hd : DifferentiableAt ℝ (fun s => timeVelocity V (s, t)) 0 :=
    ((timeVelocity_smooth V).comp (contDiff_id.prodMk contDiff_const)).differentiable
      (by simp) (0 : ℝ)
  have he : deriv (fun s => timeVelocity V (s, t)) 0 = deriv (transverse V) t := by
    have hf : (fun s => timeVelocity V (s, t)) =
        (fun s => deriv (fun r => ambientFamily V (s, r)) t) :=
      funext fun s => timeVelocity_eq_deriv V s t
    rw [hf]
    exact mixed_deriv V t
  have hh := hd.hasDerivAt
  rwa [he] at hh

theorem ambientJet_hasDerivAt (V : SmoothVariation n) (t : ℝ) :
    HasDerivAt (fun s => ambientJet V (s, t))
      ((transverseField V).value t, deriv (transverseField V).value t) 0 := by
  convert! HasDerivAt.prodMk (transverse_hasDerivAt V t) (timeVelocity_hasDerivAt V t)
    using 1
  funext s
  exact ambientJet_eq V (s, t)

theorem density_hasDerivAt (F : ReversibleMetric n) (V : SmoothVariation n)
    (hreg : Regular (loopAt V 0)) (t : ℝ) :
    HasDerivAt (fun s => Finsler.FirstVariation.density F V (s, t))
      (fderiv ℝ (lagrangian F) (ambientJet V (0, t))
        ((transverseField V).value t, deriv (transverseField V).value t)) 0 := by
  have hz := (Finsler.FirstVariation.mem_regularDomain_iff V 0 t).mpr (hreg t)
  have hd := (lagrangian_smoothAt F (ambientJet_mem_slitDomain V hz)).differentiableAt
    (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt 0 (ambientJet_hasDerivAt V t)
  simpa only [Function.comp_def, lagrangian_ambientJet] using hh

theorem partial_density_eq (F : ReversibleMetric n) (V : SmoothVariation n)
    (hreg : Regular (loopAt V 0)) (t : ℝ) :
    fderiv ℝ (Finsler.FirstVariation.density F V) (0, t) (1, 0) =
      positionDifferential F (loopJet (loopAt V 0) t) ((transverseField V).value t) +
      velocityDifferential F (loopJet (loopAt V 0) t) (deriv (transverseField V).value t) := by
  have hz := (Finsler.FirstVariation.mem_regularDomain_iff V 0 t).mpr (hreg t)
  have hd := ((Finsler.FirstVariation.density_smoothOn F V) (0, t) hz).contDiffAt
    ((Finsler.FirstVariation.regularDomain_isOpen V).mem_nhds hz)
  have he := (hasDerivAt_parameterCurve (hd.differentiableAt (by simp))).unique
    (density_hasDerivAt F V hreg t)
  simpa only [timeFDeriv_apply, ambientJet_eq_loopJet, differential_split] using he

/-- First variation depends only on the actual central loop and transverse jet. -/
theorem firstVariation_eq_explicit (F : ReversibleMetric n) (V : SmoothVariation n)
    (hreg : Regular (loopAt V 0)) :
    Finsler.FirstVariation.firstVariation F V 0 =
      Finsler.FirstVariation.firstVariation F (variation (transverseField V)) 0 := by
  rw [firstVariation_loopJet F hreg (transverseField V)]
  apply intervalIntegral.integral_congr
  intro t _
  exact partial_density_eq F V hreg t

theorem firstVariation_residual (F : ReversibleMetric n) (V : SmoothVariation n)
    (hreg : Regular (loopAt V 0)) :
    Finsler.FirstVariation.firstVariation F V 0 =
      ∫ t in 0..1, residual F (loopAt V 0) t ((transverseField V).value t) := by
  rw [firstVariation_eq_explicit F V hreg]
  exact Finsler.WeakEulerLagrange.firstVariation_residual F hreg (transverseField V)

theorem constrainedEuler_stationary (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (he : ConstrainedEuler F γ) : Stationary F γ := by
  intro V hV
  have hr : Regular (loopAt V 0) := hV.symm ▸ hreg
  have hc : ConstrainedEuler F (loopAt V 0) := hV.symm ▸ he
  have hz : Finsler.FirstVariation.firstVariation F V 0 = 0 := by
    rw [firstVariation_residual F V hr]
    have hi : (fun t => residual F (loopAt V 0) t ((transverseField V).value t)) =
        (fun _ : ℝ => (0 : ℝ)) :=
      funext fun t => hc t _ ((transverseField V).tangent t)
    rw [hi, intervalIntegral.integral_zero]
  have hd := Finsler.FirstVariation.energy_hasDerivAt F V hr
  rwa [hz] at hd

theorem stationary_iff_constrainedEuler (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) : Stationary F γ ↔ ConstrainedEuler F γ :=
  ⟨stationary_constrainedEuler F hreg, constrainedEuler_stationary F hreg⟩

end

end Finsler.GeneralVariation
