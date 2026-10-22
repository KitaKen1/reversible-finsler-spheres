module

public import Finsler.Analysis.IntervalH1CurveVariation

/-! First variation for arbitrary normed parameter spaces of actual H¹ loops.
An actual Fréchet derivative into the original graph automatically takes values
in the closed periodic tangent model. Its codomain restriction and the actual
integral energy obey the usual Fréchet chain rule. No chart construction or
curve-realization hypothesis is needed for these parameterized-family results.
-/

@[expose] public section

namespace Finsler.SobolevFamilyVariation

open Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevTangent
open Finsler.SobolevEnergyDifferential Finsler.SobolevCurveVariation
open scoped Topology ENNReal

noncomputable section

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

set_option maxHeartbeats 800000 in
theorem family_line_hasDerivAt (γ : P → SphereLoop n) {x : P}
    {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) (k : P) :
    HasDerivAt (fun r : ℝ => ((γ (x + r • k)).data : Space n)) (D k) 0 := by
  have hp : HasDerivAt (fun r : ℝ => x + r • k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add x
  have hd' : HasFDerivAt (fun y => ((γ y).data : Space n)) D (x + (0 : ℝ) • k) := by
    simpa using hd
  exact hd'.comp_hasDerivAt 0 hp

theorem family_derivative_mem_tangent (γ : P → SphereLoop n) {x : P}
    {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) (k : P) :
    D k ∈ tangentSubmodule (γ x) := by
  simpa only [zero_smul, add_zero] using
    curve_derivative_mem_tangent (fun r : ℝ => γ (x + r • k))
      (family_line_hasDerivAt γ hd k)

def familyTangentDerivative (γ : P → SphereLoop n) {x : P}
    {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    P →L[ℝ] TangentSpace (γ x) :=
  D.codRestrict (tangentSubmodule (γ x)) (family_derivative_mem_tangent γ hd)

theorem familyTangentDerivative_coe_apply (γ : P → SphereLoop n) {x : P}
    {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) (k : P) :
    (familyTangentDerivative γ hd k : Space n) = D k := rfl

theorem familyTangentDerivative_norm_eq (γ : P → SphereLoop n) {x : P}
    {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    ‖familyTangentDerivative γ hd‖ = ‖D‖ := rfl

def familyEnergyDerivative (F : ReversibleMetric n) (γ : P → SphereLoop n) {x : P}
    {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) : P →L[ℝ] ℝ :=
  (tangentVariationL F (γ x)).comp (familyTangentDerivative γ hd)

theorem familyEnergyDerivative_eq (F : ReversibleMetric n) (γ : P → SphereLoop n) {x : P}
    {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    familyEnergyDerivative F γ hd = (variationL F (γ x)).comp D := by
  ext k
  rfl

set_option maxHeartbeats 800000 in
theorem energy_hasFDerivAt_family (F : ReversibleMetric n) (γ : P → SphereLoop n)
    {x : P} {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    HasFDerivAt (fun y => Finsler.SobolevEnergy.energy F (γ y))
      ((variationL F (γ x)).comp D) x := by
  have hh :=
    (Finsler.AmbientSobolevEnergy.ambientEnergy_hasFDerivAt_sphere_centre F (γ x)).comp x hd
  exact hh

theorem energy_hasFDerivAt_family_tangent (F : ReversibleMetric n) (γ : P → SphereLoop n)
    {x : P} {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    HasFDerivAt (fun y => Finsler.SobolevEnergy.energy F (γ y))
      (familyEnergyDerivative F γ hd) x := by
  rw [familyEnergyDerivative_eq]
  exact energy_hasFDerivAt_family F γ hd

theorem energy_fderiv_family (F : ReversibleMetric n) (γ : P → SphereLoop n)
    {x : P} {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    fderiv ℝ (fun y => Finsler.SobolevEnergy.energy F (γ y)) x =
      familyEnergyDerivative F γ hd :=
  (energy_hasFDerivAt_family_tangent F γ hd).fderiv

theorem energy_remainder_family (F : ReversibleMetric n) (γ : P → SphereLoop n)
    {x : P} {D : P →L[ℝ] Space n}
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    (fun y => Finsler.SobolevEnergy.energy F (γ y) -
      Finsler.SobolevEnergy.energy F (γ x) - familyEnergyDerivative F γ hd (y - x))
      =o[𝓝 x] (fun y => y - x) :=
  (energy_hasFDerivAt_family_tangent F γ hd).isLittleO

theorem energy_contDiffAt_family (F : ReversibleMetric n) (γ : P → SphereLoop n)
    {x : P} (hγ : ContDiffAt ℝ 1 (fun y => ((γ y).data : Space n)) x) :
    ContDiffAt ℝ 1 (fun y => Finsler.SobolevEnergy.energy F (γ y)) x := by
  have he : ContDiffAt ℝ 1 (Finsler.AmbientSobolevEnergy.ambientEnergy F)
      ((γ x).data : Space n) :=
    Finsler.AmbientSobolevEnergy.ambientEnergy_contDiffAt_one F
      (Finsler.AmbientSobolevEnergy.centre (γ x))
  have hh := he.comp x hγ
  exact hh

theorem energy_contDiffOn_family (F : ReversibleMetric n) (γ : P → SphereLoop n)
    {s : Set P} (hγ : ContDiffOn ℝ 1 (fun y => ((γ y).data : Space n)) s) :
    ContDiffOn ℝ 1 (fun y => Finsler.SobolevEnergy.energy F (γ y)) s := by
  intro x hx
  have he : ContDiffAt ℝ 1 (Finsler.AmbientSobolevEnergy.ambientEnergy F)
      ((γ x).data : Space n) :=
    Finsler.AmbientSobolevEnergy.ambientEnergy_contDiffAt_one F
      (Finsler.AmbientSobolevEnergy.centre (γ x))
  have hh := he.comp_contDiffWithinAt x (hγ x hx)
  exact hh

theorem tangentCritical_family_stationary (F : ReversibleMetric n)
    (γ : P → SphereLoop n) {x : P} {D : P →L[ℝ] Space n}
    (hc : TangentCritical F (γ x))
    (hd : HasFDerivAt (fun y => ((γ y).data : Space n)) D x) :
    HasFDerivAt (fun y => Finsler.SobolevEnergy.energy F (γ y))
      (0 : P →L[ℝ] ℝ) x := by
  have hh := energy_hasFDerivAt_family_tangent F γ hd
  have he : familyEnergyDerivative F γ hd = 0 := by
    unfold familyEnergyDerivative
    rw [show tangentVariationL F (γ x) = 0 from hc]
    simp
  rw [he] at hh
  exact hh

end

end Finsler.SobolevFamilyVariation
