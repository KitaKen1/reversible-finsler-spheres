module

public import Finsler.Definitions.Sphere
public import Finsler.Analysis.NormQuadratic

/-! Reversible strongly convex Finsler metrics on the standard sphere.
Smoothness is required on the actual slit tangent bundle. Strong convexity
uses the actual second Fréchet derivative of half the squared norm on each
fiber, rather than an uninterpreted predicate. -/

@[expose] public section

namespace Finsler.Geometry

open Finsler.SphereGeometry
open scoped Manifold ContDiff

noncomputable section

def slitBundle (n : ℕ) : Set (Total n) := {p | p.2 ≠ 0}

theorem slitBundle_eq (n : ℕ) :
    slitBundle n = {p | ambientVector n p ≠ 0} := by
  ext p
  constructor
  · exact ambientMap_ne_zero p.proj
  · intro hp hv
    apply hp
    change ambientMap p.proj p.2 = 0
    rw [hv, map_zero]

theorem slitBundle_isOpen (n : ℕ) : IsOpen (slitBundle n) := by
  rw [slitBundle_eq]
  exact isClosed_singleton.isOpen_compl.preimage (ambientVector_continuous n)

structure ReversibleMetric (n : ℕ) where
  value : Total n → ℝ
  continuous : Continuous value
  smooth : ContMDiffOn (𝓡 n).tangent 𝓘(ℝ, ℝ) ∞ value (slitBundle n)
  zero : ∀ x : Sphere n, value ⟨x, 0⟩ = 0
  positive : ∀ (x : Sphere n) (v : Fiber n x), v ≠ 0 → 0 < value ⟨x, v⟩
  homogeneous : ∀ (x : Sphere n) (v : Fiber n x) (r : ℝ),
    0 ≤ r → value ⟨x, r • v⟩ = r * value ⟨x, v⟩
  reversible : ∀ (x : Sphere n) (v : Fiber n x), value ⟨x, -v⟩ = value ⟨x, v⟩
  strongConvex : ∀ (x : Sphere n) (v w : Fiber n x), v ≠ 0 → w ≠ 0 →
    0 < fderiv ℝ (fderiv ℝ (fun u : Fiber n x => value ⟨x, u⟩ ^ 2 / 2)) v w w

variable {n : ℕ}

theorem value_smoothAt (F : ReversibleMetric n) (p : Total n) (hp : p.2 ≠ 0) :
    ContMDiffAt (𝓡 n).tangent 𝓘(ℝ, ℝ) ∞ F.value p :=
  F.smooth.contMDiffAt ((slitBundle_isOpen n).mem_nhds hp)

def energy (F : ReversibleMetric n) (p : Total n) : ℝ := F.value p ^ 2 / 2

theorem value_nonneg (F : ReversibleMetric n) (x : Sphere n) (v : Fiber n x) :
    0 ≤ F.value ⟨x, v⟩ := by
  by_cases hv : v = 0
  · subst v
    rw [F.zero]
  · exact (F.positive x v hv).le

theorem value_eq_zero_iff (F : ReversibleMetric n) (x : Sphere n) (v : Fiber n x) :
    F.value ⟨x, v⟩ = 0 ↔ v = 0 := by
  constructor
  · intro h
    by_contra hv
    exact (ne_of_gt (F.positive x v hv)) h
  · rintro rfl
    exact F.zero x

theorem value_smul (F : ReversibleMetric n) (x : Sphere n) (v : Fiber n x) (r : ℝ) :
    F.value ⟨x, r • v⟩ = |r| * F.value ⟨x, v⟩ := by
  by_cases hr : 0 ≤ r
  · rw [F.homogeneous x v r hr, abs_of_nonneg hr]
  · have h := F.homogeneous x (-v) (-r) (neg_nonneg.mpr (le_of_not_ge hr))
    simpa [F.reversible, abs_of_neg (lt_of_not_ge hr)] using h

theorem energy_continuous (F : ReversibleMetric n) : Continuous (energy F) :=
  (F.continuous.pow 2).div_const 2

theorem energy_nonneg (F : ReversibleMetric n) (p : Total n) : 0 ≤ energy F p :=
  div_nonneg (sq_nonneg _) (by norm_num)

theorem energy_eq_zero_iff (F : ReversibleMetric n) (x : Sphere n) (v : Fiber n x) :
    energy F ⟨x, v⟩ = 0 ↔ v = 0 := by
  simp [energy, value_eq_zero_iff]

theorem energy_reversible (F : ReversibleMetric n) (x : Sphere n) (v : Fiber n x) :
    energy F ⟨x, -v⟩ = energy F ⟨x, v⟩ := by
  simp only [energy, F.reversible]

theorem energy_smul (F : ReversibleMetric n) (x : Sphere n) (v : Fiber n x) (r : ℝ) :
    energy F ⟨x, r • v⟩ = r ^ 2 * energy F ⟨x, v⟩ := by
  simp only [energy, value_smul, mul_pow, sq_abs]
  ring

end

end Finsler.Geometry
