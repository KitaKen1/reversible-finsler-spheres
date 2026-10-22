module

public import Finsler.Topology.CochainClass
public import Finsler.Topology.BorelCochain
public import Mathlib.Algebra.Homology.Homotopy

/-! A GENUINE F2 chain homotopy from a chain map to itself induces
a degree +1 map on homology. Endpoints cancel, including source
degree zero. This will evaluate actual loop sweep cycles on a sphere. -/

@[expose] public section
namespace Finsler.SelfHomotopySweep
open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {f : C ⟶ D} (H : _root_.Homotopy f f)

def component (q : ℕ) : C.X q ⟶ D.X (q + 1) := H.hom q (q + 1)

theorem boundary_succ (q : ℕ) : component H (q + 1) ≫ D.d (q + 2) (q + 1) =
    C.d (q + 1) q ≫ component H q := by
  have h := H.comm (q + 1)
  simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have hz : C.d (q + 1) q ≫ component H q + component H (q + 1) ≫ D.d (q + 2) (q + 1) = 0 := by
    apply add_right_cancel (b := f.f (q + 1))
    simpa only [zero_add, component] using h.symm
  apply add_right_cancel (b := component H (q + 1) ≫ D.d (q + 2) (q + 1))
  exact (BorelCochain.two_eq_zero_of_mod _).trans hz.symm

theorem boundary_zero : component H 0 ≫ D.d 1 0 = 0 := by
  have h := H.comm 0
  simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
  apply add_right_cancel (b := f.f 0)
  simpa only [zero_add, component] using h.symm

theorem cycles_closed (q : ℕ) : (C.iCycles q ≫ component H q) ≫ D.d (q + 1) q = 0 := by
  cases q with
  | zero => rw [Category.assoc, boundary_zero, comp_zero]
  | succ q =>
    rw [Category.assoc, boundary_succ, ← Category.assoc, C.iCycles_d, zero_comp]

def cycles (q : ℕ) : C.cycles q ⟶ D.cycles (q + 1) :=
  D.liftCycles (C.iCycles q ≫ component H q) q (by simp) (cycles_closed H q)

theorem cycles_i (q : ℕ) : cycles H q ≫ D.iCycles (q + 1) = C.iCycles q ≫ component H q :=
  D.liftCycles_i _ _ _ _

theorem boundary_cycles (q : ℕ) : C.toCycles (q + 1) q ≫ cycles H q =
    component H (q + 1) ≫ D.toCycles (q + 2) (q + 1) := by
  apply (cancel_mono (D.iCycles (q + 1))).mp
  rw [Category.assoc, cycles_i, ← Category.assoc, C.toCycles_i,
    Category.assoc, D.toCycles_i, boundary_succ]

theorem boundary_class_zero (q : ℕ) :
    C.toCycles (q + 1) q ≫ (cycles H q ≫ D.homologyπ (q + 1)) = 0 := by
  rw [← Category.assoc, boundary_cycles, Category.assoc, D.toCycles_comp_homologyπ, comp_zero]

def homology (q : ℕ) : C.homology q ⟶ D.homology (q + 1) :=
  (C.homologyIsCokernel (q + 1) q
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (q + 1) q by rfl))).desc
      (CokernelCofork.ofπ (cycles H q ≫ D.homologyπ (q + 1)) (boundary_class_zero H q))

theorem homologyπ_homology (q : ℕ) : C.homologyπ q ≫ homology H q = cycles H q ≫ D.homologyπ (q + 1) :=
  (C.homologyIsCokernel (q + 1) q
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (q + 1) q by rfl))).fac
      (CokernelCofork.ofπ (cycles H q ≫ D.homologyπ (q + 1)) (boundary_class_zero H q))
      WalkingParallelPair.one

end
end Finsler.SelfHomotopySweep
