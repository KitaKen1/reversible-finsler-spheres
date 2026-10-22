module

public import Finsler.Analysis.H1OrthogonalLength

/-! Orthogonal maps act on the original strong H¹ loop space.
The map remains continuous when the rotation varies continuously with an
external chain parameter; it is still constant in each loop's time variable. -/

@[expose] public section

namespace Finsler.H1OrthogonalContinuity

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevSmoothMultiplier
open Finsler.H1OrthogonalLength
open MeasureTheory Filter
open scoped Topology ContDiff ENNReal

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem value_rotateData (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : Space n) :
    value (rotateData A u) = A.toContinuousLinearMap.compLp (value u) := by
  rw [rotateData, value_fieldData]
  apply Lp.ext
  filter_upwards [fieldValueLp_ae (ψ := fun _ : ℝ => (1 : ℝ)) contDiff_const
    A.toContinuousLinearMap u, A.toContinuousLinearMap.coeFn_compLp (value u)] with t hv hA
  exact (hv.trans (one_smul ℝ _)).trans hA.symm

theorem velocity_rotateData (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : Space n) :
    velocity (rotateData A u) = A.toContinuousLinearMap.compLp (velocity u) := by
  apply Lp.ext
  filter_upwards [velocity_rotateData_ae A u,
    A.toContinuousLinearMap.coeFn_compLp (velocity u)] with t hv hA
  exact hv.trans hA.symm

theorem continuous_rotateLoop_family {X : Type*} [TopologicalSpace X]
    (A : X → Ambient n ≃ₗᵢ[ℝ] Ambient n)
    (hA : Continuous (fun x => (A x).toContinuousLinearMap))
    (u : X → SphereLoop n) (hu : Continuous u) :
    Continuous (fun x => rotateLoop (A x) (u x)) := by
  let B : (Ambient n →L[ℝ] Ambient n) →L[ℝ] ValueLp n →L[ℝ] ValueLp n :=
    (ContinuousLinearMap.id ℝ (Ambient n →L[ℝ] Ambient n)).compLpL₂ 2 intervalMeasure
  have hB := B.continuous.comp hA
  have hdata : Continuous (fun x => ((u x).data : Space n)) :=
    (sphereLoop_data_isometry n).continuous.comp hu
  have hv := hB.clm_apply ((valueL n).continuous.comp hdata)
  have hd := hB.clm_apply ((velocityL n).continuous.comp hdata)
  change Continuous (fun x => (A x).toContinuousLinearMap.compLp (value ((u x).data : Space n))) at hv
  change Continuous (fun x => (A x).toContinuousLinearMap.compLp (velocity ((u x).data : Space n))) at hd
  apply continuous_iff_continuousAt.mpr
  intro x
  apply sphereLoop_tendsto_iff.mpr
  apply tendsto_iff_value_velocity.mpr
  constructor
  · change Tendsto (fun y => value (rotateData (A y) ((u y).data : Space n))) (𝓝 x)
      (𝓝 (value (rotateData (A x) ((u x).data : Space n))))
    simpa only [value_rotateData, ContinuousAt] using hv.continuousAt
  · change Tendsto (fun y => velocity (rotateData (A y) ((u y).data : Space n))) (𝓝 x)
      (𝓝 (velocity (rotateData (A x) ((u x).data : Space n))))
    simpa only [velocity_rotateData, ContinuousAt] using hd.continuousAt

theorem rotateLoop_refl (u : SphereLoop n) :
    rotateLoop (LinearIsometryEquiv.refl ℝ (Ambient n)) u = u := by
  have hvalue : value (rotateData (LinearIsometryEquiv.refl ℝ (Ambient n))
      (u.data : Space n)) = value (u.data : Space n) := by
    rw [value_rotateData]
    apply Lp.ext
    filter_upwards [(LinearIsometryEquiv.refl ℝ (Ambient n)).toContinuousLinearMap.coeFn_compLp
      (value (u.data : Space n))] with t ht
    exact ht
  apply sphereLoop_data_injective
  apply TauCeti.WeakDerivStep.ext
  simpa only [value, valueL, TauCeti.WeakDerivStep.prevL_apply, rotateLoop] using hvalue

theorem rotateLoop_comp (A B : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : SphereLoop n) :
    rotateLoop A (rotateLoop B u) = rotateLoop (B.trans A) u := by
  have hvalue : value (rotateData A (rotateData B (u.data : Space n))) =
      value (rotateData (B.trans A) (u.data : Space n)) := by
    rw [value_rotateData, value_rotateData, value_rotateData]
    apply Lp.ext
    filter_upwards [A.toContinuousLinearMap.coeFn_compLp
      (B.toContinuousLinearMap.compLp (value (u.data : Space n))),
      B.toContinuousLinearMap.coeFn_compLp (value (u.data : Space n)),
      (B.trans A).toContinuousLinearMap.coeFn_compLp (value (u.data : Space n))] with t hA hB hBA
    rw [hA, hB, hBA]
    rfl
  apply sphereLoop_data_injective
  apply TauCeti.WeakDerivStep.ext
  simpa only [value, valueL, TauCeti.WeakDerivStep.prevL_apply, rotateLoop] using hvalue


end
end Finsler.H1OrthogonalContinuity
