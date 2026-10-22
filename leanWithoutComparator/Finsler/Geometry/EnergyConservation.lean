module

public import Finsler.Geometry.GeneralVariation
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-! Constant actual Finsler speed of regular stationary smooth loops.
The velocity homogeneity of the constructed ambient Lagrangian gives its
Euler identity. The constrained Euler equation and the genuine jet chain
rule then force the derivative of the actual density to vanish. No separate
energy-conservation or constant-speed assumption is added. -/

@[expose] public section

namespace Finsler.EnergyConservation

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.SphereRetraction Finsler.SphereVariation Finsler.AmbientLagrangian
open Finsler.WeakEulerLagrange Finsler.PointwiseEuler TauCeti.Manifold Function
open scoped Manifold ContDiff Interval RealInnerProductSpace

noncomputable section

variable {n : ℕ}

theorem lagrangian_velocity_smul (F : ReversibleMetric n) (q v : Ambient n) (r : ℝ) :
    lagrangian F (q, r • v) = r ^ 2 * lagrangian F (q, v) := by
  let D : Ambient n →L[ℝ] TangentSpace (𝓡 n) (normalize q) :=
    mfderiv 𝓘(ℝ, Ambient n) (𝓡 n) normalize q
  change F.value ⟨normalize q, D (r • v)⟩ ^ 2 =
    r ^ 2 * F.value ⟨normalize q, D v⟩ ^ 2
  rw [map_smul, value_smul, mul_pow, sq_abs]

theorem velocity_euler_identity (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z ∈ slitDomain n) : velocityDifferential F z z.2 = 2 * lagrangian F z := by
  have hd := ((lagrangian_smoothAt F hz).differentiableAt (by simp)).hasFDerivAt
  have hp : HasFDerivAt (fun v : Ambient n => (z.1, v))
      (ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have h : HasFDerivAt (fun v : Ambient n => lagrangian F (z.1, v))
      ((fderiv ℝ (lagrangian F) z).comp (ContinuousLinearMap.inr ℝ _ _)) z.2 := by
    convert! hd.comp z.2 hp using 1
  have he := h.apply_self_eq_nsmul_of_homogeneous (k := 2) (fun r v => by
    simpa only [smul_eq_mul] using lagrangian_velocity_smul F z.1 v r)
  simpa only [velocityDifferential, Prod.mk.eta, nsmul_eq_mul, Nat.cast_ofNat] using he

def position (γ : SmoothLoop n) (t : ℝ) : Ambient n := (γ t : Ambient n)
def velocity (γ : SmoothLoop n) (t : ℝ) : Ambient n := (loopJet γ t).2

theorem position_smooth (γ : SmoothLoop n) : ContDiff ℝ ∞ (position γ) :=
  ((inclusion_smooth n).comp γ.smooth).contDiff

theorem velocity_smooth (γ : SmoothLoop n) : ContDiff ℝ ∞ (velocity γ) :=
  contDiff_snd.comp (loopJet_smooth γ)

theorem velocity_eq_deriv (γ : SmoothLoop n) (t : ℝ) : velocity γ t = deriv (position γ) t := by
  have h := Finsler.GeneralVariation.timeVelocity_eq_ambientVelocity (constantVariation γ) 0 t
  rw [Finsler.FirstVariation.velocityLift_eq_loopVelocity, loopAt_constantVariation,
    Finsler.GeneralVariation.timeVelocity_eq_deriv] at h
  exact h

theorem position_hasDerivAt (γ : SmoothLoop n) (t : ℝ) :
    HasDerivAt (position γ) (velocity γ t) t := by
  rw [velocity_eq_deriv]
  exact ((position_smooth γ).differentiable (by simp) t).hasDerivAt

theorem velocity_tangent (γ : SmoothLoop n) (t : ℝ) :
    ⟪(γ t : Ambient n), velocity γ t⟫ = 0 := by
  have h := (position_hasDerivAt γ t).norm_sq
  have he : (fun u => ‖position γ u‖ ^ 2) = (fun _ : ℝ => (1 : ℝ)) := by
    funext u
    simp [position]
  rw [he] at h
  have hz := h.unique (hasDerivAt_const t (1 : ℝ))
  change 2 * ⟪(γ t : Ambient n), velocity γ t⟫ = 0 at hz
  linarith

theorem loopJet_eq (γ : SmoothLoop n) (t : ℝ) :
    loopJet γ t = (position γ t, velocity γ t) := by
  apply Prod.ext
  · simp only [loopJet, ambientPair, Finsler.LoopEnergy.velocityLift,
      curveVelocityLift_apply, position]
  · rfl

theorem loopJet_hasDerivAt (γ : SmoothLoop n) (t : ℝ) :
    HasDerivAt (loopJet γ) (velocity γ t, deriv (velocity γ) t) t := by
  convert! HasDerivAt.prodMk (position_hasDerivAt γ t)
    (((velocity_smooth γ).differentiable (by simp) t).hasDerivAt) using 1
  funext u
  exact loopJet_eq γ u

def density (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) : ℝ :=
  lagrangian F (loopJet γ t)

def densityDerivative (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) : ℝ :=
  fderiv ℝ (lagrangian F) (loopJet γ t) (velocity γ t, deriv (velocity γ) t)

theorem density_eq (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) :
    density F γ t = Finsler.LoopEnergy.density F γ t := by
  rw [density, loopJet, lagrangian_ambientPair]
  rfl

theorem density_hasDerivAt (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (t : ℝ) : HasDerivAt (density F γ) (densityDerivative F γ t) t :=
  ((lagrangian_smoothAt F (loopJet_mem_slitDomain γ hreg t)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t (loopJet_hasDerivAt γ t)

theorem momentum_velocity_eq (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (t : ℝ) : momentum F γ t (velocity γ t) = 2 * density F γ t :=
  velocity_euler_identity F (loopJet_mem_slitDomain γ hreg t)

theorem densityDerivative_eq_zero (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (he : ConstrainedEuler F γ) (t : ℝ) : densityDerivative F γ t = 0 := by
  have hM := ((momentum_smooth F hreg).differentiable (by simp) t).hasDerivAt.clm_apply
    (((velocity_smooth γ).differentiable (by simp) t).hasDerivAt)
  have hL := (density_hasDerivAt F hreg t).const_mul 2
  have hf : (fun u => momentum F γ u (velocity γ u)) = (fun u => 2 * density F γ u) :=
    funext (momentum_velocity_eq F hreg)
  rw [hf] at hM
  have hD := hM.unique hL
  have hR := he t (velocity γ t) (velocity_tangent γ t)
  change positionDifferential F (loopJet γ t) (velocity γ t) -
    deriv (momentum F γ) t (velocity γ t) = 0 at hR
  have hsplit := differential_split F (loopJet γ t) (velocity γ t) (deriv (velocity γ) t)
  change densityDerivative F γ t =
    positionDifferential F (loopJet γ t) (velocity γ t) +
      momentum F γ t (deriv (velocity γ) t) at hsplit
  linarith

theorem density_hasDerivAt_zero (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (he : ConstrainedEuler F γ) (t : ℝ) : HasDerivAt (density F γ) 0 t := by
  have h := density_hasDerivAt F hreg t
  rwa [densityDerivative_eq_zero F hreg he t] at h

theorem density_constant (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (he : ConstrainedEuler F γ) (s t : ℝ) : density F γ s = density F γ t :=
  is_const_of_deriv_eq_zero (fun u => (density_hasDerivAt_zero F hreg he u).differentiableAt)
    (fun u => (density_hasDerivAt_zero F hreg he u).deriv) s t

theorem stationary_density_constant (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (hstat : Stationary F γ) (s t : ℝ) :
    Finsler.LoopEnergy.density F γ s = Finsler.LoopEnergy.density F γ t := by
  simpa only [density_eq] using density_constant F hreg (stationary_constrainedEuler F hreg hstat) s t

theorem stationary_speed_constant (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (hstat : Stationary F γ) (s t : ℝ) :
    F.value (Finsler.LoopEnergy.velocityLift γ s) =
      F.value (Finsler.LoopEnergy.velocityLift γ t) := by
  have hs : 0 ≤ F.value (Finsler.LoopEnergy.velocityLift γ s) := by
    rw [Finsler.LoopEnergy.velocityLift, curveVelocityLift_apply]
    exact value_nonneg F _ _
  have ht : 0 ≤ F.value (Finsler.LoopEnergy.velocityLift γ t) := by
    rw [Finsler.LoopEnergy.velocityLift, curveVelocityLift_apply]
    exact value_nonneg F _ _
  exact (sq_eq_sq₀ hs ht).mp (stationary_density_constant F hreg hstat s t)

theorem stationary_energy_eq_density (F : ReversibleMetric n) {γ : SmoothLoop n}
    (hreg : Regular γ) (hstat : Stationary F γ) (t : ℝ) :
    Finsler.LoopEnergy.energy F γ = Finsler.LoopEnergy.density F γ t := by
  have hf : Finsler.LoopEnergy.density F γ =
      (fun _ : ℝ => Finsler.LoopEnergy.density F γ t) :=
    funext (fun u => stationary_density_constant F hreg hstat u t)
  rw [Finsler.LoopEnergy.energy, hf]
  simp

end

end Finsler.EnergyConservation
