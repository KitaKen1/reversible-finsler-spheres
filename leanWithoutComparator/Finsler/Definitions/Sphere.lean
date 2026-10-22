module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The standard sphere and its actual mathlib tangent bundle. The derivative
of the inclusion identifies each tangent fiber with the orthogonal complement
of the base point in Euclidean space. -/

@[expose] public section

namespace Finsler.SphereGeometry

open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

abbrev Ambient (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))
abbrev Sphere (n : ℕ) := ↥(Metric.sphere (0 : Ambient n) 1)
abbrev Fiber (n : ℕ) (x : Sphere n) := TangentSpace (𝓡 n) x
abbrev Total (n : ℕ) := TangentBundle (𝓡 n) (Sphere n)

instance ambientDimension (n : ℕ) : Fact (Module.finrank ℝ (Ambient n) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def inclusion (n : ℕ) : Sphere n → Ambient n := fun x => x.val

theorem inclusion_smooth (n : ℕ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, Ambient n) ∞ (inclusion n) := contMDiff_coe_sphere

def ambientMap {n : ℕ} (x : Sphere n) : Fiber n x →L[ℝ] Ambient n :=
  mvfderiv (𝓡 n) (inclusion n) x

theorem ambientMap_injective {n : ℕ} (x : Sphere n) :
    Function.Injective (ambientMap x) := injective_mvfderiv_subtypeVal_sphere x

theorem ambientMap_range {n : ℕ} (x : Sphere n) :
    (ambientMap x).range = (ℝ ∙ (x : Ambient n))ᗮ := range_mvfderiv_subtypeVal x

theorem ambientMap_ne_zero {n : ℕ} (x : Sphere n) {v : Fiber n x} (hv : v ≠ 0) :
    ambientMap x v ≠ 0 := by
  intro h
  exact hv ((ambientMap_injective x) (h.trans (map_zero (ambientMap x)).symm))

def ambientVector (n : ℕ) (p : Total n) : Ambient n := ambientMap p.proj p.2

theorem ambientVector_smooth (n : ℕ) :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, Ambient n) ∞ (ambientVector n) := by
  have ht := (inclusion_smooth n).contMDiff_tangentMap (m := ∞) (by simp)
  have hs := contMDiff_snd_tangentBundle_modelSpace (Ambient n) 𝓘(ℝ, Ambient n) (n := ∞)
  exact hs.comp ht

theorem ambientVector_continuous (n : ℕ) : Continuous (ambientVector n) :=
  (ambientVector_smooth n).continuous

end

end Finsler.SphereGeometry
