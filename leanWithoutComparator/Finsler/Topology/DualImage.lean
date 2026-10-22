module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! UF's kernel equality implies stabilized dual images without finite dimensionality.
Identifying these duals with the actual relative cohomology is a separate comparison. -/

@[expose] public section

namespace Finsler.DualImage

variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

theorem range_eq_of_ker_eq (f : X →ₗ[K] Y) (g : X →ₗ[K] Z)
    (h : LinearMap.ker f = LinearMap.ker g) :
    LinearMap.range f.dualMap = LinearMap.range g.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, h]

/-- A functional extending across the intermediate cut also extends globally
when the two homology kernels agree. -/
theorem stabilized_image_lift (f : X →ₗ[K] Y) (g : X →ₗ[K] Z)
    (h : LinearMap.ker f = LinearMap.ker g) (φ : Module.Dual K Y) :
    ∃ ψ : Module.Dual K Z, g.dualMap ψ = f.dualMap φ := by
  have hr := range_eq_of_ker_eq f g h
  have hm : f.dualMap φ ∈ LinearMap.range g.dualMap := by
    rw [← hr]
    exact ⟨φ, rfl⟩
  exact hm

/-- Vector-space duality reverses an exact pair, without finite dimensionality. -/
theorem exact_duals (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range g.dualMap = LinearMap.ker f.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, h]

/-- A functional vanishing on the incoming image lifts through the outgoing dual. -/
theorem dual_lift_of_exact (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (h : LinearMap.range f = LinearMap.ker g) (φ : Module.Dual K Y)
    (hφ : f.dualMap φ = 0) : ∃ ψ : Module.Dual K Z, g.dualMap ψ = φ := by
  have hm : φ ∈ LinearMap.range g.dualMap := by
    rw [exact_duals f g h]
    exact hφ
  exact hm

end Finsler.DualImage
