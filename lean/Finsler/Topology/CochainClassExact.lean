module

public import Finsler.Topology.CochainClass
public import Finsler.Topology.RelativeCupCommutativity

/-! Equal classes have an actual primitive in the original cochain complex.
In a relative complex this keeps the primitive relative, hence supported. -/

@[expose] public section

namespace Finsler.CochainClassExact

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R] (C : CochainComplex (ModuleCat.{0} R) ℕ)

theorem exists_primitive_of_class_eq (n : ℕ) (hn : 1 ≤ n) (φ ψ : C.X n)
    (hφ : (C.d n (n + 1)).hom φ = 0) (hψ : (C.d n (n + 1)).hom ψ = 0)
    (h : CochainClass.classOf C n φ hφ = CochainClass.classOf C n ψ hψ) :
    ∃ η : C.X (n - 1), (C.d (n - 1) n).hom η = φ - ψ := by
  let u := C.cyclesMk φ (n + 1) (CochainClass.next_eq n) hφ
  let v := C.cyclesMk ψ (n + 1) (CochainClass.next_eq n) hψ
  let S := ShortComplex.mk (C.toCycles (n - 1) n) (C.homologyπ n)
    (C.toCycles_comp_homologyπ (n - 1) n)
  have hp : (ComplexShape.up ℕ).prev n = n - 1 :=
    (ComplexShape.up ℕ).prev_eq' (show n - 1 + 1 = n by omega)
  have he : S.Exact := S.exact_of_g_is_cokernel (C.homologyIsCokernel (n - 1) n hp)
  have hz : (C.homologyπ n).hom (u - v) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr h
  obtain ⟨η, hη⟩ := (ShortComplex.moduleCat_exact_iff S).mp he (u - v) hz
  refine ⟨η, ?_⟩
  have hi := congrArg (C.iCycles n).hom hη
  rw [map_sub] at hi
  have hu : (C.iCycles n).hom u = φ := C.i_cyclesMk _ _ _ _
  have hv : (C.iCycles n).hom v = ψ := C.i_cyclesMk _ _ _ _
  rw [hu, hv] at hi
  exact (ConcreteCategory.congr_hom (C.toCycles_i (n - 1) n) η).symm.trans hi

theorem class_eq_iff_boundary (n : ℕ) (hn : 1 ≤ n) (φ ψ : C.X n)
    (hφ : (C.d n (n + 1)).hom φ = 0) (hψ : (C.d n (n + 1)).hom ψ = 0) :
    CochainClass.classOf C n φ hφ = CochainClass.classOf C n ψ hψ ↔
      ∃ η : C.X (n - 1), (C.d (n - 1) n).hom η = φ - ψ := by
  constructor
  · exact exists_primitive_of_class_eq C n hn φ ψ hφ hψ
  · rintro ⟨η, hη⟩
    exact RelativeCupCommutativity.classOf_eq_of_boundary C (n - 1) n η φ ψ hφ hψ hη.symm

def primitive (n : ℕ) (hn : 1 ≤ n) (φ ψ : C.X n)
    (hφ : (C.d n (n + 1)).hom φ = 0) (hψ : (C.d n (n + 1)).hom ψ = 0)
    (h : CochainClass.classOf C n φ hφ = CochainClass.classOf C n ψ hψ) : C.X (n - 1) :=
  (exists_primitive_of_class_eq C n hn φ ψ hφ hψ h).choose

theorem primitive_d (n : ℕ) (hn : 1 ≤ n) (φ ψ : C.X n)
    (hφ : (C.d n (n + 1)).hom φ = 0) (hψ : (C.d n (n + 1)).hom ψ = 0)
    (h : CochainClass.classOf C n φ hφ = CochainClass.classOf C n ψ hψ) :
    (C.d (n - 1) n).hom (primitive C n hn φ ψ hφ hψ h) = φ - ψ :=
  (exists_primitive_of_class_eq C n hn φ ψ hφ hψ h).choose_spec


end
end Finsler.CochainClassExact
