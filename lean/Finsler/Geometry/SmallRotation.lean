module

public import Finsler.Geometry.MetricComparison
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Uniform small-orthogonal-map distortion of the actual Finsler speed.
The tolerance depends only on the metric and the requested relative error.
This is a pointwise ingredient, not a cut-join or filling construction. -/

@[expose] public section

namespace Finsler.SmallRotation

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.AmbientLagrangian Finsler.MetricComparison
open scoped Manifold RealInnerProductSpace

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def pointSpeed (F : ReversibleMetric n) (z : Ambient n × Ambient n) : ℝ :=
  Real.sqrt (lagrangian F z)

theorem pointSpeed_eq_value (F : ReversibleMetric n) (z : Ambient n × Ambient n) :
    pointSpeed F z = F.value (lift z) := by
  rw [pointSpeed, lagrangian, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (value_nonneg F _ _)

theorem pointSpeed_smul (F : ReversibleMetric n) (x v : Ambient n) (a : ℝ) :
    pointSpeed F (x, a • v) = |a| * pointSpeed F (x, v) := by
  have hs := (mfderiv 𝓘(ℝ, Ambient n) (𝓡 n) SphereRetraction.normalize x).map_smul a v
  have hv := congrArg (fun w : Fiber n (SphereRetraction.normalize x) =>
    F.value ⟨SphereRetraction.normalize x, w⟩) hs
  exact (pointSpeed_eq_value F (x, a • v)).trans
    (hv.trans ((value_smul F _ _ a).trans
      (congrArg (fun r : ℝ => |a| * r) (pointSpeed_eq_value F (x, v)).symm)))

theorem exists_unit_relative_control (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ unitTangentPairs n, ∀ w ∈ unitTangentPairs n,
      dist w z < δ → |pointSpeed F w - pointSpeed F z| ≤ ε * pointSpeed F z := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_unit_bounds F
  have hs : ContinuousOn (pointSpeed F) (unitTangentPairs n) :=
    Real.continuous_sqrt.comp_continuousOn (lagrangian_continuousOn_unit F)
  have hu := (unitTangentPairs_compact n).uniformContinuousOn_of_continuous hs
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hu
    (ε * Real.sqrt c) (mul_pos hε (Real.sqrt_pos.mpr hc))
  refine ⟨δ, hδ, fun z hz w hw hdist => ?_⟩
  have he := hd w hw z hz hdist
  rw [Real.dist_eq] at he
  exact he.le.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hb z hz).1) hε.le)

def rotatePair (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (z : Ambient n × Ambient n) :
    Ambient n × Ambient n := (A z.1, A z.2)

theorem rotatePair_unit (A : Ambient n ≃ₗᵢ[ℝ] Ambient n)
    {z : Ambient n × Ambient n} (hz : z ∈ unitTangentPairs n) :
    rotatePair A z ∈ unitTangentPairs n := by
  exact ⟨(A.norm_map _).trans hz.1, (A.norm_map _).trans hz.2.1,
    (A.inner_map_map _ _).trans hz.2.2⟩

theorem pair_dist_le (A : Ambient n ≃ₗᵢ[ℝ] Ambient n)
    {z : Ambient n × Ambient n} (hz : z ∈ unitTangentPairs n) :
    dist (rotatePair A z) z ≤
      ‖A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ := by
  rw [Prod.dist_eq]
  apply max_le
  · simpa [rotatePair, dist_eq_norm, hz.1] using
      (A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)).le_opNorm z.1
  · simpa [rotatePair, dist_eq_norm, hz.2.1] using
      (A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)).le_opNorm z.2

theorem exists_unit_rotation_control (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Ambient n ≃ₗᵢ[ℝ] Ambient n,
      ‖A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ →
      ∀ z ∈ unitTangentPairs n,
        |pointSpeed F (rotatePair A z) - pointSpeed F z| ≤ ε * pointSpeed F z := by
  obtain ⟨δ, hδ, hd⟩ := exists_unit_relative_control F hε
  exact ⟨δ, hδ, fun A hA z hz => hd z hz _ (rotatePair_unit A hz)
    ((pair_dist_le A hz).trans_lt hA)⟩


end
end Finsler.SmallRotation
