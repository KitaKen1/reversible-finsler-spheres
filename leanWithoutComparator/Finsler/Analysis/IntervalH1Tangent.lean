module

public import Finsler.Analysis.IntervalH1FrechetDerivative
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Periodic tangent directions in the original weak H¹ graph.
The tangent model is the closed subspace of genuine H¹ fields whose continuous
representatives are perpendicular to the actual sphere loop at every time.
Every derivative of an actual sphere-valued H¹ curve lies in this model.
Realizing every such field by a curve and constructing charts remain separate.
-/

@[expose] public section

namespace Finsler.SobolevTangent

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Set Filter
open scoped Topology RealInnerProductSpace ENNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def normalTraceL (u : SphereLoop n) (t : ClosedInterval) : Space n →L[ℝ] ℝ :=
  (innerSL ℝ (traceL n t (u.data : Space n))).comp (traceL n t)

theorem normalTraceL_apply (u : SphereLoop n) (t : ClosedInterval) (h : Space n) :
    normalTraceL u t h =
      ⟪continuousRepresentative (u.data : Space n) t, continuousRepresentative h t⟫ := rfl

theorem normalTraceL_norm_le (u : SphereLoop n) (t : ClosedInterval) :
    ‖normalTraceL u t‖ ≤ 2 := by
  apply (normalTraceL u t).opNorm_le_bound (by norm_num)
  intro h
  rw [normalTraceL_apply, Real.norm_eq_abs]
  calc
    _ ≤ ‖continuousRepresentative (u.data : Space n) t‖ *
        ‖continuousRepresentative h t‖ := abs_real_inner_le_norm _ _
    _ ≤ 2 * ‖h‖ := by
      rw [u.sphere_constraint t, one_mul]
      exact continuousRepresentative_norm_le_two h t.property

def tangentSubmodule (u : SphereLoop n) : Submodule ℝ (Space n) :=
  periodicSubmodule n ⊓ ⨅ t : ClosedInterval, (normalTraceL u t).ker

theorem mem_tangentSubmodule_iff (u : SphereLoop n) (h : Space n) :
    h ∈ tangentSubmodule u ↔ h ∈ periodicSubmodule n ∧
      ∀ t : ClosedInterval,
        ⟪continuousRepresentative (u.data : Space n) t, continuousRepresentative h t⟫ = 0 := by
  simp [tangentSubmodule, normalTraceL_apply]

theorem tangentSubmodule_closed (u : SphereLoop n) :
    IsClosed (tangentSubmodule u : Set (Space n)) := by
  have he : (tangentSubmodule u : Set (Space n)) =
      (periodicSubmodule n : Set (Space n)) ∩
        ⋂ t : ClosedInterval, {h : Space n | normalTraceL u t h = 0} := by
    ext h
    simp [tangentSubmodule]
  rw [he]
  exact (periodicSubmodule_closed n).inter
    (isClosed_iInter fun t => isClosed_eq (normalTraceL u t).continuous continuous_const)

theorem tangentSubmodule_complete (u : SphereLoop n) :
    IsComplete (tangentSubmodule u : Set (Space n)) :=
  (tangentSubmodule_closed u).isComplete

abbrev TangentSpace (u : SphereLoop n) := ↥(tangentSubmodule u)

-- Spell out the inherited scalar norm estimate to avoid ambiguous submodule
-- scalar-tower inference through the weak-derivative graph.
instance tangentNormedSpace (u : SphereLoop n) : NormedSpace ℝ (TangentSpace u) where
  norm_smul_le a h := norm_smul_le a (h : Space n)

instance (u : SphereLoop n) : CompleteSpace (TangentSpace u) :=
  (tangentSubmodule_complete u).completeSpace_coe

theorem tangent_periodic (u : SphereLoop n) (h : TangentSpace u) :
    (h : Space n) ∈ periodicSubmodule n :=
  ((mem_tangentSubmodule_iff u h).mp h.property).1

theorem tangent_orthogonal (u : SphereLoop n) (h : TangentSpace u) (t : ClosedInterval) :
    ⟪continuousRepresentative (u.data : Space n) t,
      continuousRepresentative (h : Space n) t⟫ = 0 :=
  ((mem_tangentSubmodule_iff u h).mp h.property).2 t

theorem tangent_trace_endpoints (u : SphereLoop n) (h : TangentSpace u) :
    traceOne (h : Space n) = traceZero (h : Space n) :=
  (mem_periodicSubmodule_iff _).mp (tangent_periodic u h)

theorem tangent_velocity_integral_zero (u : SphereLoop n) (h : TangentSpace u) :
    (∫ t in (0 : ℝ)..1, velocity (h : Space n) t) = 0 :=
  (mem_periodicSubmodule_iff_integral_zero _).mp (tangent_periodic u h)

set_option maxHeartbeats 800000 in
theorem curve_derivative_periodic (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    h ∈ periodicSubmodule n := by
  have hh : HasDerivAt
      (fun r => (traceOneL n - traceZeroL n) ((γ r).data : Space n))
      ((traceOneL n - traceZeroL n) h) s :=
    (traceOneL n - traceZeroL n).hasFDerivAt.comp_hasDerivAt s hd
  have he : (fun r => (traceOneL n - traceZeroL n) ((γ r).data : Space n)) =
      (fun _ : ℝ => (0 : Ambient n)) := by
    funext r
    exact (γ r).data.property
  rw [he] at hh
  exact hh.unique (hasDerivAt_const s (0 : Ambient n))

set_option maxHeartbeats 800000 in
theorem curve_derivative_orthogonal (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) (t : ClosedInterval) :
    ⟪continuousRepresentative ((γ s).data : Space n) t,
      continuousRepresentative h t⟫ = 0 := by
  have hp : HasDerivAt (fun r => traceL n t ((γ r).data : Space n)) (traceL n t h) s :=
    (traceL n t).hasFDerivAt.comp_hasDerivAt s hd
  have hh := hp.norm_sq
  have he : (fun r => ‖traceL n t ((γ r).data : Space n)‖ ^ 2) =
      (fun _ : ℝ => (1 : ℝ)) := by
    funext r
    rw [traceL_apply, (γ r).sphere_constraint t, one_pow]
  rw [he] at hh
  have hz := hh.unique (hasDerivAt_const s (1 : ℝ))
  change 2 * ⟪continuousRepresentative ((γ s).data : Space n) t,
    continuousRepresentative h t⟫ = 0 at hz
  linarith

theorem curve_derivative_mem_tangent (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    h ∈ tangentSubmodule (γ s) :=
  (mem_tangentSubmodule_iff _ _).mpr
    ⟨curve_derivative_periodic γ hd, curve_derivative_orthogonal γ hd⟩

def curveTangent (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) : TangentSpace (γ s) :=
  ⟨h, curve_derivative_mem_tangent γ hd⟩

theorem curveTangent_coe (γ : ℝ → SphereLoop n) {s : ℝ} {h : Space n}
    (hd : HasDerivAt (fun r => ((γ r).data : Space n)) h s) :
    (curveTangent γ hd : Space n) = h := rfl

end

end Finsler.SobolevTangent
