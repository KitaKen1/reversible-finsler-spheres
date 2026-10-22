module

public import Finsler.Analysis.IntervalH1Tangent

/-! First variation along actual differentiable sphere-valued H¹ curves.
The original ambient integral energy equals the actual sphere energy on every
sphere loop, so its certified Fréchet derivative gives the curve chain rule.
The restricted functional uses the original closed tangent model and norm.
This does not assert charts, realization of every tangent field, or regularity
of positive critical points.
-/

@[expose] public section

namespace Finsler.SobolevCurveVariation

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevTangent Finsler.SobolevEnergyDifferential
open Set Filter
open scoped Topology ENNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def tangentVariationL (F : ReversibleMetric n) (u : SphereLoop n) :
    TangentSpace u →L[ℝ] ℝ :=
  (variationL F u).comp (tangentSubmodule u).subtypeL

theorem tangentVariationL_apply (F : ReversibleMetric n) (u : SphereLoop n)
    (h : TangentSpace u) :
    tangentVariationL F u h = variationCandidate F u (h : Space n) := rfl

theorem tangentVariationL_eq_full_differential (F : ReversibleMetric n)
    (u : SphereLoop n) (h : TangentSpace u) :
    tangentVariationL F u h =
      ∫ t, fderiv ℝ (Finsler.AmbientLagrangian.lagrangian F) (weakJet u t)
        (continuousRepresentative (h : Space n) t, velocity (h : Space n) t)
        ∂intervalMeasure :=
  variationL_apply_eq_full_differential F u h

theorem tangentVariationL_opNorm_le (F : ReversibleMetric n) (u : SphereLoop n) :
    ‖tangentVariationL F u‖ ≤ variationBound F *
      (2 * ‖velocity (u.data : Space n)‖ ^ 2 + ‖velocity (u.data : Space n)‖) := by
  change sInf {c : ℝ | 0 ≤ c ∧ ∀ h : TangentSpace u,
    ‖tangentVariationL F u h‖ ≤ c * ‖h‖} ≤ _
  apply csInf_le (show BddBelow {c : ℝ | 0 ≤ c ∧ ∀ h : TangentSpace u,
    ‖tangentVariationL F u h‖ ≤ c * ‖h‖} from ⟨0, fun _ hc => hc.1⟩)
  exact ⟨by have hh := variationBound_pos F; positivity,
    fun h => variationCandidate_norm_le F u h⟩

theorem tangentVariationL_constantSphereLoop (F : ReversibleMetric n) (x : Sphere n) :
    tangentVariationL F (constantSphereLoop x) = 0 := by
  ext h
  change variationL F (constantSphereLoop x) (h : Space n) = 0
  rw [variationL_constantSphereLoop]
  rfl

theorem energy_hasDerivAt_curve (F : ReversibleMetric n) (γ : ℝ → SphereLoop n)
    {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    HasDerivAt (fun r => Finsler.SobolevEnergy.energy F (γ r))
      (variationL F (γ s) h) s := by
  exact (Finsler.AmbientSobolevEnergy.ambientEnergy_hasFDerivAt_sphere_centre F
    (γ s)).comp_hasDerivAt s hd

theorem energy_deriv_curve (F : ReversibleMetric n) (γ : ℝ → SphereLoop n)
    {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    deriv (fun r => Finsler.SobolevEnergy.energy F (γ r)) s =
      variationL F (γ s) h :=
  (energy_hasDerivAt_curve F γ hd).deriv

theorem energy_hasDerivAt_curve_tangent (F : ReversibleMetric n)
    (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    HasDerivAt (fun r => Finsler.SobolevEnergy.energy F (γ r))
      (tangentVariationL F (γ s) (curveTangent γ hd)) s :=
  energy_hasDerivAt_curve F γ hd

theorem energy_hasDerivAt_curve_integral (F : ReversibleMetric n)
    (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    HasDerivAt (fun r => Finsler.SobolevEnergy.energy F (γ r))
      (∫ t, fderiv ℝ (Finsler.AmbientLagrangian.lagrangian F) (weakJet (γ s) t)
        (continuousRepresentative h t, velocity h t) ∂intervalMeasure) s := by
  rw [← variationL_apply_eq_full_differential F (γ s) h]
  exact energy_hasDerivAt_curve F γ hd

def TangentCritical (F : ReversibleMetric n) (u : SphereLoop n) : Prop :=
  tangentVariationL F u = 0

theorem tangentCritical_iff (F : ReversibleMetric n) (u : SphereLoop n) :
    TangentCritical F u ↔ ∀ h : TangentSpace u, variationCandidate F u (h : Space n) = 0 := by
  constructor
  · intro hc h
    change tangentVariationL F u h = 0
    rw [hc]
    rfl
  · intro hc
    apply ContinuousLinearMap.ext
    exact hc

theorem tangentCritical_constantSphereLoop (F : ReversibleMetric n) (x : Sphere n) :
    TangentCritical F (constantSphereLoop x) :=
  tangentVariationL_constantSphereLoop F x

theorem tangentCritical_curve_stationary (F : ReversibleMetric n)
    (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hc : TangentCritical F (γ s))
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    HasDerivAt (fun r => Finsler.SobolevEnergy.energy F (γ r)) 0 s := by
  have hh := energy_hasDerivAt_curve_tangent F γ hd
  rw [show tangentVariationL F (γ s) = 0 from hc] at hh
  exact hh

theorem tangentCritical_of_curve_realization (F : ReversibleMetric n) (u : SphereLoop n)
    (hr : ∀ h : TangentSpace u, ∃ γ : ℝ → SphereLoop n, γ 0 = u ∧
      HasDerivAt (fun r => ((γ r).data : Space n)) (h : Space n) 0)
    (hs : ∀ (γ : ℝ → SphereLoop n) (h : Space n), γ 0 = u →
      HasDerivAt (fun r => ((γ r).data : Space n)) h 0 →
      HasDerivAt (fun r => Finsler.SobolevEnergy.energy F (γ r)) 0 0) :
    TangentCritical F u := by
  apply (tangentCritical_iff F u).mpr
  intro h
  obtain ⟨γ, hγ, hd⟩ := hr h
  have hh := (energy_hasDerivAt_curve F γ hd).unique (hs γ h hγ hd)
  rw [hγ] at hh
  exact hh

end

end Finsler.SobolevCurveVariation
