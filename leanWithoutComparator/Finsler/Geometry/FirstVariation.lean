module

public import Finsler.Definitions.Geodesic
public import TauCeti.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! Differentiation of the actual integral Finsler energy along smooth periodic
variations with a regular central loop. The joint velocity lift is the genuine
manifold differential in the time direction. Smoothness is used only on the
preimage of the slit tangent bundle. Coordinate integration by parts and the
Euler--Lagrange comparison are not asserted here. -/

@[expose] public section

namespace Finsler.FirstVariation

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open TauCeti.Manifold Bundle
open scoped Manifold ContDiff Interval

noncomputable section

variable {n : ℕ}

def velocityLift (V : SmoothVariation n) (z : ℝ × ℝ) : Total n :=
  tangentMap 𝓘(ℝ, ℝ × ℝ) (𝓡 n) V.family ⟨z, (0, 1)⟩

theorem velocityLift_apply (V : SmoothVariation n) (z : ℝ × ℝ) :
    velocityLift V z = ⟨V.family z,
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 n) V.family z (0, 1)⟩ := rfl

theorem velocityLift_smooth (V : SmoothVariation n) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞ (velocityLift V) := by
  have hs : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ)).tangent ∞
      (fun z : ℝ × ℝ => (⟨z, (0, 1)⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) := by
    exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact (V.smooth.contMDiff_tangentMap (m := ∞) (by simp)).comp hs

theorem velocityLift_eq_loopVelocity (V : SmoothVariation n) (s t : ℝ) :
    velocityLift V (s, t) = Finsler.LoopEnergy.velocityLift (loopAt V s) t := by
  have h := curveVelocity_eq_mfderiv_snd
    (f := fun s t => V.family (s, t))
    (V.smooth.mdifferentiableAt (by simp) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) (𝓡 n) V.family (s, t))
  simp only [velocityLift_apply, Finsler.LoopEnergy.velocityLift, curveVelocityLift_apply]
  exact congrArg (fun v => (⟨V.family (s, t), v⟩ : Total n)) h.symm

def regularDomain (V : SmoothVariation n) : Set (ℝ × ℝ) :=
  velocityLift V ⁻¹' slitBundle n

theorem regularDomain_isOpen (V : SmoothVariation n) : IsOpen (regularDomain V) :=
  (slitBundle_isOpen n).preimage (velocityLift_smooth V).continuous

theorem mem_regularDomain_iff (V : SmoothVariation n) (s t : ℝ) :
    (s, t) ∈ regularDomain V ↔ curveVelocity (𝓡 n) (loopAt V s) t ≠ 0 := by
  change (velocityLift V (s, t)).2 ≠ 0 ↔ _
  rw [velocityLift_eq_loopVelocity]
  simp only [Finsler.LoopEnergy.velocityLift, curveVelocityLift_snd]
  rfl

theorem central_segment_subset (V : SmoothVariation n) {s a b : ℝ}
    (hreg : Regular (loopAt V s)) :
    {s} ×ˢ Set.uIcc a b ⊆ regularDomain V := by
  rintro ⟨u, t⟩ ⟨hu, _⟩
  have he : u = s := Set.mem_singleton_iff.mp hu
  subst u
  exact (mem_regularDomain_iff V s t).mpr (hreg t)

def density (F : ReversibleMetric n) (V : SmoothVariation n) (z : ℝ × ℝ) : ℝ :=
  F.value (velocityLift V z) ^ 2

theorem density_eq_loopDensity (F : ReversibleMetric n) (V : SmoothVariation n)
    (s t : ℝ) : density F V (s, t) = Finsler.LoopEnergy.density F (loopAt V s) t := by
  simp only [density, Finsler.LoopEnergy.density, velocityLift_eq_loopVelocity]

theorem density_smoothOn (F : ReversibleMetric n) (V : SmoothVariation n) :
    ContDiffOn ℝ ∞ (density F V) (regularDomain V) := by
  intro z hz
  exact (((value_smoothAt F (velocityLift V z) hz).comp z
    (velocityLift_smooth V).contMDiffAt).contDiffAt.pow 2).contDiffWithinAt

/-- The actual differential of F evaluated on the transverse derivative of
the joint velocity lift. Both maps here are genuine manifold derivatives. -/
def valueDifferential (F : ReversibleMetric n) (V : SmoothVariation n)
    (z : ℝ × ℝ) : ℝ :=
  mvfderiv (𝓡 n).tangent F.value (velocityLift V z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent (velocityLift V) z (1, 0))

theorem partial_value_eq (F : ReversibleMetric n) (V : SmoothVariation n)
    (z : ℝ × ℝ) (hz : z ∈ regularDomain V) :
    fderiv ℝ (fun u => F.value (velocityLift V u)) z (1, 0) =
      valueDifferential F V z := by
  have h := mvfderiv_comp_apply z
    ((value_smoothAt F (velocityLift V z) hz).mdifferentiableAt (by simp))
    ((velocityLift_smooth V).mdifferentiableAt (by simp)) ((1 : ℝ), (0 : ℝ))
  rw [mvfderiv_eq_fderiv] at h
  exact h

theorem partial_density_eq (F : ReversibleMetric n) (V : SmoothVariation n)
    (z : ℝ × ℝ) (hz : z ∈ regularDomain V) :
    fderiv ℝ (density F V) z (1, 0) =
      2 * F.value (velocityLift V z) * valueDifferential F V z := by
  have hd : DifferentiableAt ℝ (fun u => F.value (velocityLift V u)) z :=
    ((value_smoothAt F (velocityLift V z) hz).comp z
      (velocityLift_smooth V).contMDiffAt).contDiffAt.differentiableAt (by simp)
  change fderiv ℝ (fun u => F.value (velocityLift V u) ^ 2) z (1, 0) = _
  rw [fderiv_fun_pow 2 hd]
  simp only [smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, partial_value_eq F V z hz]

/-- The integral of the actual partial derivative in the variation parameter.
No derivative or differentiability hypothesis is added to the metric data. -/
def firstVariation (F : ReversibleMetric n) (V : SmoothVariation n) (s : ℝ) : ℝ :=
  ∫ t in 0..1, fderiv ℝ (density F V) (s, t) (1, 0)

theorem firstVariation_eq (F : ReversibleMetric n) (V : SmoothVariation n)
    {s : ℝ} (hreg : Regular (loopAt V s)) :
    firstVariation F V s =
      ∫ t in 0..1, 2 * F.value (velocityLift V (s, t)) * valueDifferential F V (s, t) := by
  apply intervalIntegral.integral_congr
  intro t _
  exact partial_density_eq F V (s, t) ((mem_regularDomain_iff V s t).mpr (hreg t))

theorem partial_intervalIntegrable (F : ReversibleMetric n) (V : SmoothVariation n)
    {s : ℝ} (hreg : Regular (loopAt V s)) :
    IntervalIntegrable (fun t => fderiv ℝ (density F V) (s, t) (1, 0))
      MeasureTheory.volume 0 1 :=
  (TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn (regularDomain_isOpen V)
    ((density_smoothOn F V).of_le (by simp)) (central_segment_subset V hreg)).1

theorem energy_hasDerivAt (F : ReversibleMetric n) (V : SmoothVariation n)
    {s : ℝ} (hreg : Regular (loopAt V s)) :
    HasDerivAt (fun u => Finsler.LoopEnergy.energy F (loopAt V u))
      (firstVariation F V s) s := by
  have h := (TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn (regularDomain_isOpen V)
    ((density_smoothOn F V).of_le (by simp)) (central_segment_subset V hreg)
    (a := 0) (b := 1)).2
  simpa only [firstVariation, Finsler.LoopEnergy.energy, ← density_eq_loopDensity] using h

theorem stationary_iff_firstVariation_zero (F : ReversibleMetric n) (γ : SmoothLoop n)
    (hreg : Regular γ) :
    Stationary F γ ↔ ∀ V : SmoothVariation n, loopAt V 0 = γ → firstVariation F V 0 = 0 := by
  constructor
  · intro h V hV
    exact (energy_hasDerivAt F V (hV.symm ▸ hreg)).unique (h V hV)
  · intro h V hV
    have hd := energy_hasDerivAt F V (s := 0) (hV.symm ▸ hreg)
    rwa [h V hV] at hd

end

end Finsler.FirstVariation
