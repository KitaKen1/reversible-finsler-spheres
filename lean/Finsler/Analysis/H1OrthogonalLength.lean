module

public import Finsler.Geometry.SmallRotationGeneral
public import Finsler.Analysis.IntervalH1SmoothMultiplier
public import Finsler.Analysis.IntervalH1Length

/-! Time-independent ambient orthogonal maps on the actual H¹ loop space.
First fix a length bound M, then choose one rotation radius for all loops below M.
This does not construct the cut-join chain map, subdivisions, or a filling. -/

@[expose] public section

namespace Finsler.H1OrthogonalLength

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSmoothMultiplier Finsler.SobolevLength
open Finsler.SmallRotation Finsler.SmallRotationGeneral
open MeasureTheory Set Filter
open scoped ContDiff Topology RealInnerProductSpace

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def rotateData (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : Space n) : Space n :=
  fieldData (ψ := fun _ : ℝ => (1 : ℝ)) contDiff_const A.toContinuousLinearMap u

theorem representative_rotateData (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : Space n)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    continuousRepresentative (rotateData A u) t = A (continuousRepresentative u t) := by
  change continuousRepresentative (fieldData (ψ := fun _ : ℝ => (1 : ℝ))
    contDiff_const A.toContinuousLinearMap u) t =
      A.toContinuousLinearMap (continuousRepresentative u t)
  exact (representative_fieldData (ψ := fun _ : ℝ => (1 : ℝ))
    contDiff_const A.toContinuousLinearMap u ht).trans (one_smul ℝ _)

theorem velocity_rotateData_ae (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : Space n) :
    velocity (rotateData A u) =ᵐ[intervalMeasure] fun t => A (velocity u t) := by
  filter_upwards [velocity_fieldData_ae (ψ := fun _ : ℝ => (1 : ℝ))
    contDiff_const A.toContinuousLinearMap u] with t ht
  simpa [rotateData] using ht

theorem rotateData_periodic (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : periodicSubmodule n) :
    rotateData A (u : Space n) ∈ periodicSubmodule n :=
  fieldData_periodic (ψ := fun _ : ℝ => (1 : ℝ)) contDiff_const
    A.toContinuousLinearMap u rfl

def rotateLoop (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : SphereLoop n) : SphereLoop n where
  data := ⟨rotateData A (u.data : Space n), rotateData_periodic A u.data⟩
  sphere_constraint := by
    intro t
    change ‖continuousRepresentative (rotateData A (u.data : Space n)) t‖ = 1
    rw [representative_rotateData A _ t.property, A.norm_map]
    exact u.sphere_constraint t

theorem weakJet_rotateLoop_ae (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : SphereLoop n) :
    weakJet (rotateLoop A u) =ᵐ[intervalMeasure] fun t => rotatePair A (weakJet u t) := by
  filter_upwards [velocity_rotateData_ae A (u.data : Space n),
    ae_restrict_mem measurableSet_Ioo] with t hv ht
  exact Prod.ext (representative_rotateData A _ (Ioo_subset_Icc_self ht)) hv

/-- One relative error estimate for every actual H¹ loop, including vanishing velocities. -/
theorem exists_relative_length_control (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Ambient n ≃ₗᵢ[ℝ] Ambient n,
      ‖A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ →
      ∀ u : SphereLoop n,
        |length F (rotateLoop A u) - length F u| ≤ ε * length F u := by
  obtain ⟨δ, hδ, hd⟩ := exists_rotation_speed_control F hε
  refine ⟨δ, hδ, fun A hA u => ?_⟩
  have hpoint : ∀ᵐ t ∂intervalMeasure,
      |speed F (rotateLoop A u) t - speed F u t| ≤ ε * speed F u t := by
    filter_upwards [weakJet_rotateLoop_ae A u, weakVelocity_orthogonal_ae u,
      ae_restrict_mem measurableSet_Ioo] with t hj hi ht
    change |pointSpeed F (weakJet (rotateLoop A u) t) - pointSpeed F (weakJet u t)| ≤
      ε * pointSpeed F (weakJet u t)
    rw [hj]
    exact hd A hA _ _ (u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩) hi
  have hg := speed_integrable F (rotateLoop A u)
  have hf := speed_integrable F u
  change |(∫ t, speed F (rotateLoop A u) t ∂intervalMeasure) -
    (∫ t, speed F u t ∂intervalMeasure)| ≤ _
  rw [← integral_sub hg hf]
  calc
    |∫ t, speed F (rotateLoop A u) t - speed F u t ∂intervalMeasure| ≤
        ∫ t, |speed F (rotateLoop A u) t - speed F u t| ∂intervalMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t, ε * speed F u t ∂intervalMeasure :=
      integral_mono_ae (hg.sub hf).abs (hf.const_mul ε) hpoint
    _ = ε * length F u := integral_const_mul _ _

/-- The finite-chain length bound is fixed before choosing the rotation radius. -/
theorem exists_additive_length_control (F : ReversibleMetric n) (M : ℝ) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Ambient n ≃ₗᵢ[ℝ] Ambient n,
      ‖A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ →
      ∀ u : SphereLoop n, length F u ≤ M →
        |length F (rotateLoop A u) - length F u| < ε := by
  have hden : 0 < M + 1 := by linarith
  have hη : 0 < ε / (M + 1) := div_pos hε hden
  obtain ⟨δ, hδ, hd⟩ := exists_relative_length_control F hη
  refine ⟨δ, hδ, fun A hA u hu => ?_⟩
  have hb := (hd A hA u).trans (mul_le_mul_of_nonneg_left hu hη.le)
  have hid : ε / (M + 1) * (M + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hstrict : ε / (M + 1) * M < ε := by nlinarith
  exact hb.trans_lt hstrict


end
end Finsler.H1OrthogonalLength
