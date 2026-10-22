module

public import Finsler.Definitions.Sphere
public import TauCeti.Analysis.Sobolev.GraphStep
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Actual vector-valued H¹ data on (0,1).
The closed graph records the distributional derivative, not an arbitrary
velocity field. Evaluation at 1 identifies the one-dimensional derivative
operator with its velocity without changing the L² norm. Periodic traces,
continuous representatives and the sphere constraint remain separate work. -/

@[expose] public section

namespace Finsler.IntervalSobolev

open Finsler.SphereGeometry MeasureTheory TopologicalSpace Filter
open scoped Topology ENNReal

noncomputable section

def unitInterval : Opens ℝ := ⟨Set.Ioo 0 1, isOpen_Ioo⟩

abbrev intervalMeasure : Measure ℝ := volume.restrict (unitInterval : Set ℝ)

abbrev ValueLp (n : ℕ) := Lp (Ambient n) 2 intervalMeasure

abbrev DerivativeLp (n : ℕ) := Lp (ℝ →L[ℝ] Ambient n) 2 intervalMeasure

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def base (n : ℕ) : ValueLp n →L[ℝ] ValueLp n := ContinuousLinearMap.id ℝ (ValueLp n)

abbrev Space (n : ℕ) := TauCeti.WeakDerivStep volume unitInterval 2 (base n)

def valueL (n : ℕ) : Space n →L[ℝ] ValueLp n := TauCeti.WeakDerivStep.prevL (base n)

def derivativeL (n : ℕ) : Space n →L[ℝ] DerivativeLp n :=
  TauCeti.WeakDerivStep.weakFDerivL (base n)

def value {n : ℕ} (u : Space n) : ValueLp n := valueL n u

def derivative {n : ℕ} (u : Space n) : DerivativeLp n := derivativeL n u

def derivativeVelocityLp (n : ℕ) : DerivativeLp n →ₗᵢ[ℝ] ValueLp n where
  toLinearMap := ((ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 intervalMeasure).toLinearMap
  norm_map' D := by
    let L := (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).symm.toContinuousLinearEquiv.toContinuousLinearMap
    change ‖L.compLpL 2 intervalMeasure D‖ = ‖D‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [L.coeFn_compLpL D] with t ht
    rw [ht]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).symm.norm_map (D t)

def velocityL (n : ℕ) : Space n →L[ℝ] ValueLp n :=
  (derivativeVelocityLp n).toContinuousLinearMap.comp (derivativeL n)

def velocity {n : ℕ} (u : Space n) : ValueLp n := velocityL n u

theorem derivativeVelocityLp_apply_ae {n : ℕ} (D : DerivativeLp n) :
    derivativeVelocityLp n D =ᵐ[intervalMeasure] fun t => D t 1 := by
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).symm.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL D

theorem value_hasWeakFDeriv {n : ℕ} (u : Space n) :
    TauCeti.HasWeakFDerivOn volume unitInterval (value u) (derivative u) := by
  have hv : value u = TauCeti.WeakDerivStep.prev (base n) u :=
    TauCeti.WeakDerivStep.prevL_apply (base n) u
  have hd : derivative u = TauCeti.WeakDerivStep.weakFDeriv (base n) u :=
    TauCeti.WeakDerivStep.weakFDerivL_apply (base n) u
  rw [hv, hd]
  simpa only [base, ContinuousLinearMap.id_apply]
    using TauCeti.WeakDerivStep.hasWeakFDerivOn_base_prev (base n) u

theorem velocity_apply_ae {n : ℕ} (u : Space n) :
    velocity u =ᵐ[intervalMeasure] fun t => derivative u t 1 :=
  derivativeVelocityLp_apply_ae (derivative u)

theorem velocity_norm_eq {n : ℕ} (u : Space n) : ‖velocity u‖ = ‖derivative u‖ :=
  (derivativeVelocityLp n).norm_map (derivative u)

theorem norm_sq_eq {n : ℕ} (u : Space n) :
    ‖u‖ ^ 2 = ‖value u‖ ^ 2 + ‖velocity u‖ ^ 2 := by
  rw [velocity_norm_eq]
  simpa only [value, valueL, derivative, derivativeL,
    TauCeti.WeakDerivStep.prevL_apply, TauCeti.WeakDerivStep.weakFDerivL_apply]
    using TauCeti.WeakDerivStep.norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq (base n) u

theorem value_norm_le {n : ℕ} (u : Space n) : ‖value u‖ ≤ ‖u‖ := by
  simpa only [value, valueL, TauCeti.WeakDerivStep.prevL_apply]
    using TauCeti.WeakDerivStep.norm_prev_le (base n) u

theorem velocity_norm_le {n : ℕ} (u : Space n) : ‖velocity u‖ ≤ ‖u‖ := by
  rw [velocity_norm_eq]
  simpa only [derivative, derivativeL, TauCeti.WeakDerivStep.weakFDerivL_apply]
    using TauCeti.WeakDerivStep.norm_weakFDeriv_le (base n) u

theorem tendsto_iff_value_velocity {n : ℕ} {I : Type*} {l : Filter I}
    {v : I → Space n} {u : Space n} : Tendsto v l (𝓝 u) ↔
      Tendsto (fun i => value (v i)) l (𝓝 (value u)) ∧
      Tendsto (fun i => velocity (v i)) l (𝓝 (velocity u)) := by
  have h : Tendsto v l (𝓝 u) ↔
      Tendsto (fun i => value (v i)) l (𝓝 (value u)) ∧
      Tendsto (fun i => derivative (v i)) l (𝓝 (derivative u)) := by
    simpa only [value, valueL, derivative, derivativeL,
      TauCeti.WeakDerivStep.prevL_apply, TauCeti.WeakDerivStep.weakFDerivL_apply]
      using TauCeti.WeakDerivStep.tendsto_iff_prev_weakFDeriv
        (base := base n) (v := v) (u := u) (l := l)
  constructor
  · intro hv
    obtain ⟨hvalue, hderiv⟩ := h.mp hv
    refine ⟨hvalue, ?_⟩
    exact (derivativeVelocityLp n).continuous.continuousAt.tendsto.comp hderiv
  · rintro ⟨hvalue, hvelocity⟩
    apply h.mpr
    refine ⟨hvalue, ?_⟩
    exact (derivativeVelocityLp n).isometry.isEmbedding.tendsto_nhds_iff.mpr hvelocity

theorem space_complete (n : ℕ) : IsComplete (Set.univ : Set (Space n)) := isComplete_univ

theorem integrable_velocity_sq {n : ℕ} (u : Space n) :
    Integrable (fun t => ‖velocity u t‖ ^ 2) intervalMeasure :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (velocity u))).mp
    (Lp.memLp (velocity u))

end

end Finsler.IntervalSobolev
