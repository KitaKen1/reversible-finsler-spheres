module

public import Finsler.Definitions.Metric

/-! The round metric, constructed from the derivative of the actual sphere
inclusion. Its smoothness and strong convexity are proved, not postulated. -/

@[expose] public section

namespace Finsler.Geometry

open Finsler.SphereGeometry
open scoped Manifold ContDiff

noncomputable section

def roundValue (n : ℕ) (p : Total n) : ℝ := ‖ambientVector n p‖

theorem roundValue_continuous (n : ℕ) : Continuous (roundValue n) :=
  (ambientVector_continuous n).norm

theorem roundValue_smooth (n : ℕ) :
    ContMDiffOn (𝓡 n).tangent 𝓘(ℝ, ℝ) ∞ (roundValue n) (slitBundle n) := by
  intro p hp
  have hn : ambientVector n p ≠ 0 := ambientMap_ne_zero p.proj hp
  exact ((contDiffAt_norm ℝ hn).contMDiffAt.comp p
    (ambientVector_smooth n p)).contMDiffWithinAt

theorem roundValue_zero (n : ℕ) (x : Sphere n) : roundValue n ⟨x, 0⟩ = 0 := by
  simp [roundValue, ambientVector]

theorem roundValue_positive {n : ℕ} (x : Sphere n) (v : Fiber n x) (hv : v ≠ 0) :
    0 < roundValue n ⟨x, v⟩ :=
  norm_pos_iff.mpr (ambientMap_ne_zero x hv)

theorem roundValue_homogeneous {n : ℕ} (x : Sphere n) (v : Fiber n x)
    (r : ℝ) (hr : 0 ≤ r) : roundValue n ⟨x, r • v⟩ = r * roundValue n ⟨x, v⟩ := by
  simp [roundValue, ambientVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]

theorem roundValue_reversible {n : ℕ} (x : Sphere n) (v : Fiber n x) :
    roundValue n ⟨x, -v⟩ = roundValue n ⟨x, v⟩ := by
  simp [roundValue, ambientVector]

theorem roundValue_hessian {n : ℕ} (x : Sphere n) (v w : Fiber n x) :
    fderiv ℝ (fderiv ℝ (fun u : Fiber n x => roundValue n ⟨x, u⟩ ^ 2 / 2)) v w w =
      ‖ambientMap x w‖ ^ 2 := by
  -- Only for this fiberwise calculation, use the model norm. The derivative
  -- itself is defined on the tangent space's existing topological vector space,
  -- so neither the metric definition nor the resulting Hessian chooses a norm.
  let : NormedAddCommGroup (Fiber n x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (Fiber n x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  change fderiv ℝ (fderiv ℝ (Finsler.NormQuadratic.energy (ambientMap x))) v w w = _
  exact Finsler.NormQuadratic.energy_hessian_diagonal
    (V := Fiber n x) (E := Ambient n) (ambientMap x) v w

theorem roundValue_strongConvex {n : ℕ} (x : Sphere n) (v w : Fiber n x)
    (_hv : v ≠ 0) (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (fun u : Fiber n x => roundValue n ⟨x, u⟩ ^ 2 / 2)) v w w := by
  rw [roundValue_hessian]
  exact sq_pos_of_pos (norm_pos_iff.mpr (ambientMap_ne_zero x hw))

def roundMetric (n : ℕ) : ReversibleMetric n where
  value := roundValue n
  continuous := roundValue_continuous n
  smooth := roundValue_smooth n
  zero := roundValue_zero n
  positive := roundValue_positive
  homogeneous := roundValue_homogeneous
  reversible := roundValue_reversible
  strongConvex := roundValue_strongConvex

theorem reversibleMetric_nonempty (n : ℕ) : Nonempty (ReversibleMetric n) :=
  ⟨roundMetric n⟩

end

end Finsler.Geometry
