module

public import Finsler.Geometry.FirstVariation
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import TauCeti.Analysis.Calculus.ParametricFDeriv

/-! Explicit variations of smooth sphere loops. A periodic smooth ambient
field orthogonal to the loop is a genuine tangent field. Normalizing gamma+s*eta
works for every real s: its inner product with gamma is one, so it never vanishes.
No exponential map, flow, bounded parameter or uniform field bound is needed. -/

@[expose] public section

namespace Finsler.SphereVariation

open Finsler.SphereGeometry Finsler.Loops Finsler.Geodesics
open TauCeti.Manifold Function
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

structure SmoothTangentField (γ : SmoothLoop n) where
  value : ℝ → Ambient n
  smooth : ContDiff ℝ ∞ value
  periodic : Periodic value 1
  tangent : ∀ t, ⟪(γ t : Ambient n), value t⟫ = 0

variable {γ : SmoothLoop n}

theorem field_has_unique_tangent_lift (η : SmoothTangentField γ) (t : ℝ) :
    ∃! v : Fiber n (γ t), ambientMap (γ t) v = η.value t := by
  have h : η.value t ∈ (ambientMap (γ t)).range := by
    rw [ambientMap_range]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (η.tangent t)
  obtain ⟨v, hv⟩ := h
  exact ⟨v, hv, fun w hw => ambientMap_injective (γ t) (hw.trans hv.symm)⟩

def raw (η : SmoothTangentField γ) (z : ℝ × ℝ) : Ambient n :=
  (γ z.2 : Ambient n) + z.1 • η.value z.2

theorem raw_zero (η : SmoothTangentField γ) (t : ℝ) :
    raw η (0, t) = (γ t : Ambient n) := by simp [raw]

theorem raw_inner (η : SmoothTangentField γ) (z : ℝ × ℝ) :
    ⟪(γ z.2 : Ambient n), raw η z⟫ = 1 := by
  simp [raw, inner_add_right, inner_smul_right, η.tangent]

theorem raw_ne_zero (η : SmoothTangentField γ) (z : ℝ × ℝ) : raw η z ≠ 0 := by
  intro h
  have he := raw_inner η z
  rw [h, inner_zero_right] at he
  norm_num at he

theorem raw_smooth (η : SmoothTangentField γ) : ContDiff ℝ ∞ (raw η) := by
  have hg : ContDiff ℝ ∞ (fun t : ℝ => (γ t : Ambient n)) :=
    ((inclusion_smooth n).comp γ.smooth).contDiff
  exact (hg.comp contDiff_snd).add (contDiff_fst.smul (η.smooth.comp contDiff_snd))

def normalized (η : SmoothTangentField γ) (z : ℝ × ℝ) : Ambient n :=
  ‖raw η z‖⁻¹ • raw η z

theorem normalized_mem_sphere (η : SmoothTangentField γ) (z : ℝ × ℝ) :
    normalized η z ∈ Metric.sphere (0 : Ambient n) 1 := by
  have hn : ‖raw η z‖ ≠ 0 := norm_ne_zero_iff.mpr (raw_ne_zero η z)
  simp [normalized, norm_smul, inv_mul_cancel₀ hn]

theorem normalized_smooth (η : SmoothTangentField γ) : ContDiff ℝ ∞ (normalized η) :=
  (((raw_smooth η).norm ℝ (raw_ne_zero η)).inv
    (fun z => norm_ne_zero_iff.mpr (raw_ne_zero η z))).smul (raw_smooth η)

def variation (η : SmoothTangentField γ) : SmoothVariation n where
  family := fun z => ⟨normalized η z, normalized_mem_sphere η z⟩
  smooth := (normalized_smooth η).contMDiff.codRestrict_sphere (normalized_mem_sphere η)
  periodic := by
    intro s t
    apply Subtype.ext
    change normalized η (s, t + 1) = normalized η (s, t)
    simp only [normalized, raw, γ.periodic t, η.periodic t]

theorem variation_at_zero (η : SmoothTangentField γ) (t : ℝ) :
    (variation η).family (0, t) = γ t := by
  apply Subtype.ext
  simp [variation, normalized, raw_zero]

theorem loopAt_variation_zero (η : SmoothTangentField γ) :
    loopAt (variation η) 0 = γ := by
  apply loop_ext
  exact variation_at_zero η

theorem variation_fixed (η : SmoothTangentField γ) {t : ℝ} (ht : η.value t = 0) (s : ℝ) :
    (variation η).family (s, t) = γ t := by
  apply Subtype.ext
  simp [variation, normalized, raw, ht]

theorem raw_hasDerivAt (η : SmoothTangentField γ) (t : ℝ) :
    HasDerivAt (fun s => raw η (s, t)) (η.value t) 0 := by
  simpa [raw] using ((hasDerivAt_id (0 : ℝ)).smul_const (η.value t)).const_add
    (γ t : Ambient n)

theorem norm_raw_hasDerivAt (η : SmoothTangentField γ) (t : ℝ) :
    HasDerivAt (fun s => ‖raw η (s, t)‖) 0 0 := by
  have hs : HasDerivAt (fun s => ‖raw η (s, t)‖ ^ 2) 0 0 := by
    simpa [raw_zero, η.tangent t] using (raw_hasDerivAt η t).norm_sq
  have h := hs.sqrt (by simp [raw_zero])
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, zero_div] using h

theorem normalized_hasDerivAt (η : SmoothTangentField γ) (t : ℝ) :
    HasDerivAt (fun s => normalized η (s, t)) (η.value t) 0 := by
  have hi := (norm_raw_hasDerivAt η t).inv (by simp [raw_zero])
  convert! hi.smul (raw_hasDerivAt η t) using 1
  simp [raw_zero]

theorem normalized_mixed_deriv (η : SmoothTangentField γ) (t : ℝ) :
    deriv (fun s => deriv (fun r => normalized η (s, r)) t) 0 = deriv η.value t := by
  have h := deriv_deriv_comm (t := 0) (x := t)
    ((normalized_smooth η).contDiffAt.of_le (by simp))
  rw [h]
  have he : (fun r => deriv (fun s => normalized η (s, r)) 0) = η.value :=
    funext fun r => (normalized_hasDerivAt η r).deriv
  rw [he]

/-- The actual time derivative of the normalized ambient family. -/
def timeVelocity (η : SmoothTangentField γ) (z : ℝ × ℝ) : Ambient n :=
  fderiv ℝ (normalized η) z (0, 1)

theorem timeVelocity_eq_deriv (η : SmoothTangentField γ) (s t : ℝ) :
    timeVelocity η (s, t) = deriv (fun r => normalized η (s, r)) t := by
  have h := (hasFDerivAt_timeSlice
    ((normalized_smooth η).differentiable (by simp) (s, t))).hasDerivAt
  simpa only [spatialFDeriv_apply, timeVelocity] using h.deriv.symm

theorem timeVelocity_smooth (η : SmoothTangentField γ) : ContDiff ℝ ∞ (timeVelocity η) :=
  ((normalized_smooth η).fderiv_right (by simp)).clm_apply contDiff_const

theorem timeVelocity_hasDerivAt (η : SmoothTangentField γ) (t : ℝ) :
    HasDerivAt (fun s => timeVelocity η (s, t)) (deriv η.value t) 0 := by
  have hd : DifferentiableAt ℝ (fun s => timeVelocity η (s, t)) 0 :=
    ((timeVelocity_smooth η).comp
      (contDiff_id.prodMk contDiff_const)).differentiable (by simp) (0 : ℝ)
  have he : deriv (fun s => timeVelocity η (s, t)) 0 = deriv η.value t := by
    have hf : (fun s => timeVelocity η (s, t)) =
        (fun s => deriv (fun r => normalized η (s, r)) t) :=
      funext fun s => timeVelocity_eq_deriv η s t
    rw [hf]
    exact normalized_mixed_deriv η t
  have hh := hd.hasDerivAt
  rwa [he] at hh

theorem timeVelocity_eq_ambientVelocity (η : SmoothTangentField γ) (s t : ℝ) :
    ambientVector n (Finsler.FirstVariation.velocityLift (variation η) (s, t)) =
      timeVelocity η (s, t) := by
  have hd := hasDerivAt_comp_curve (t := t) (g := inclusion n)
    ((inclusion_smooth n).mdifferentiableAt (by simp))
    (hasMFDerivAt_curveVelocity ((loopAt (variation η) s).smooth.mdifferentiableAt (by simp)))
  rw [Finsler.FirstVariation.velocityLift_eq_loopVelocity,
    Finsler.LoopEnergy.velocityLift, curveVelocityLift_apply, timeVelocity_eq_deriv]
  exact hd.deriv.symm

/-- The actual position and velocity lift read in the ambient Euclidean space. -/
def ambientJet (V : SmoothVariation n) (z : ℝ × ℝ) : Ambient n × Ambient n :=
  ((V.family z : Ambient n), ambientVector n (Finsler.FirstVariation.velocityLift V z))

theorem ambientJet_variation_eq (η : SmoothTangentField γ) (z : ℝ × ℝ) :
    ambientJet (variation η) z = (normalized η z, timeVelocity η z) := by
  rcases z with ⟨s, t⟩
  exact congrArg (fun v => (normalized η (s, t), v))
    (timeVelocity_eq_ambientVelocity η s t)

theorem ambientJet_variation_hasDerivAt (η : SmoothTangentField γ) (t : ℝ) :
    HasDerivAt (fun s => ambientJet (variation η) (s, t))
      (η.value t, deriv η.value t) 0 := by
  convert! HasDerivAt.prodMk (normalized_hasDerivAt η t) (timeVelocity_hasDerivAt η t)
    using 1
  funext s
  exact ambientJet_variation_eq η (s, t)

theorem variation_realizes_field (η : SmoothTangentField γ) (t : ℝ) :
    ambientMap ((variation η).family (0, t))
      (curveVelocity (𝓡 n) (fun s => (variation η).family (s, t)) 0) = η.value t := by
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun s => (variation η).family (s, t)) :=
    (variation η).smooth.comp (contDiff_id.prodMk contDiff_const).contMDiff
  have h := hasDerivAt_comp_curve (t := 0)
    ((inclusion_smooth n).mdifferentiableAt (by simp))
    (hasMFDerivAt_curveVelocity (hc.mdifferentiableAt (by simp)))
  exact h.unique (normalized_hasDerivAt η t)

theorem exists_variation_realizing (η : SmoothTangentField γ) :
    ∃ V : SmoothVariation n, loopAt V 0 = γ ∧
      ∀ t, ambientMap (V.family (0, t))
        (curveVelocity (𝓡 n) (fun s => V.family (s, t)) 0) = η.value t :=
  ⟨variation η, loopAt_variation_zero η, variation_realizes_field η⟩

theorem stationary_explicit_firstVariation_zero (F : Finsler.Geometry.ReversibleMetric n)
    (hreg : Regular γ) (hstat : Stationary F γ) (η : SmoothTangentField γ) :
    Finsler.FirstVariation.firstVariation F (variation η) 0 = 0 :=
  (Finsler.FirstVariation.stationary_iff_firstVariation_zero F γ hreg).mp hstat
    (variation η) (loopAt_variation_zero η)

/-- Orthogonally project an arbitrary smooth periodic ambient test field.
This gives actual tangent test fields without a coordinate frame. -/
def projectedField (h : ℝ → Ambient n) (hs : ContDiff ℝ ∞ h) (hp : Periodic h 1) :
    SmoothTangentField γ where
  value := fun t => h t - ⟪(γ t : Ambient n), h t⟫ • (γ t : Ambient n)
  smooth := by
    have hg : ContDiff ℝ ∞ (fun t : ℝ => (γ t : Ambient n)) :=
      ((inclusion_smooth n).comp γ.smooth).contDiff
    exact hs.sub ((hg.inner ℝ hs).smul hg)
  periodic := by
    intro t
    dsimp only
    rw [γ.periodic t, hp t]
  tangent := by
    intro t
    simp [inner_sub_right, inner_smul_right]

theorem projectedField_eq_of_tangent (h : ℝ → Ambient n) (hs : ContDiff ℝ ∞ h)
    (hp : Periodic h 1) {t : ℝ} (ht : ⟪(γ t : Ambient n), h t⟫ = 0) :
    (projectedField (γ := γ) h hs hp).value t = h t := by
  simp [projectedField, ht]

theorem projectedField_zero (h : ℝ → Ambient n) (hs : ContDiff ℝ ∞ h)
    (hp : Periodic h 1) {t : ℝ} (ht : h t = 0) :
    (projectedField (γ := γ) h hs hp).value t = 0 := by
  simp [projectedField, ht]

theorem projected_variation_fixed (h : ℝ → Ambient n) (hs : ContDiff ℝ ∞ h)
    (hp : Periodic h 1) {t : ℝ} (ht : h t = 0) (s : ℝ) :
    (variation (projectedField (γ := γ) h hs hp)).family (s, t) = γ t :=
  variation_fixed _ (projectedField_zero h hs hp ht) s

theorem stationary_projected_firstVariation_zero (F : Finsler.Geometry.ReversibleMetric n)
    (hreg : Regular γ) (hstat : Stationary F γ) (h : ℝ → Ambient n)
    (hs : ContDiff ℝ ∞ h) (hp : Periodic h 1) :
    Finsler.FirstVariation.firstVariation F (variation (projectedField (γ := γ) h hs hp)) 0 = 0 :=
  stationary_explicit_firstVariation_zero F hreg hstat (projectedField (γ := γ) h hs hp)

end

end Finsler.SphereVariation
