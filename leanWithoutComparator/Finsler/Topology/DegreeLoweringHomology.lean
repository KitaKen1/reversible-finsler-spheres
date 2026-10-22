module

public import Finsler.Topology.CochainClass

/-! Descend an actual degree-lowering F₂-style chain operation to homology.
The construction works over any ring when its components commute with boundary
without signs. Degree zero is included; no negative chain degrees are added. -/

@[expose] public section

namespace Finsler.DegreeLoweringHomology

open CategoryTheory CategoryTheory.Limits

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [Ring R]

structure Map (C D : ChainComplex (ModuleCat.{0} R) ℕ) (p : ℕ) where
  component (q : ℕ) : C.X (p + q) ⟶ D.X q
  comm (q : ℕ) : component (q + 1) ≫ D.d (q + 1) q =
    C.d (p + (q + 1)) (p + q) ≫ component q

namespace Map

variable {C D E : ChainComplex (ModuleCat.{0} R) ℕ} {p : ℕ} (f : Map C D p)

theorem cycles_closed (q : ℕ) :
    (C.iCycles (p + q) ≫ f.component q) ≫ D.d q (q - 1) = 0 := by
  cases q with
  | zero => rw [D.shape 0 0 (by decide), comp_zero]
  | succ q =>
    change (C.iCycles (p + (q + 1)) ≫ f.component (q + 1)) ≫ D.d (q + 1) q = 0
    rw [Category.assoc, f.comm, ← Category.assoc, C.iCycles_d, zero_comp]

def cycles (q : ℕ) : C.cycles (p + q) ⟶ D.cycles q :=
  D.liftCycles (C.iCycles (p + q) ≫ f.component q) (q - 1)
    (by cases q <;> simp [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ])
    (f.cycles_closed q)

theorem cycles_i (q : ℕ) :
    f.cycles q ≫ D.iCycles q = C.iCycles (p + q) ≫ f.component q :=
  D.liftCycles_i _ _ _ _

theorem boundary_cycles (q : ℕ) :
    C.toCycles (p + q + 1) (p + q) ≫ f.cycles q =
      f.component (q + 1) ≫ D.toCycles (q + 1) q := by
  apply (cancel_mono (D.iCycles q)).mp
  rw [Category.assoc, f.cycles_i, ← Category.assoc, C.toCycles_i,
    Category.assoc, D.toCycles_i]
  exact (f.comm q).symm

theorem boundary_class_zero (q : ℕ) :
    C.toCycles (p + q + 1) (p + q) ≫ (f.cycles q ≫ D.homologyπ q) = 0 := by
  rw [← Category.assoc, f.boundary_cycles, Category.assoc,
    D.toCycles_comp_homologyπ, comp_zero]

def homology (q : ℕ) : C.homology (p + q) ⟶ D.homology q :=
  (C.homologyIsCokernel (p + q + 1) (p + q)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (p + q + 1) (p + q) by rfl))).desc
    (CokernelCofork.ofπ (f.cycles q ≫ D.homologyπ q) (f.boundary_class_zero q))

theorem homologyπ_homology (q : ℕ) :
    C.homologyπ (p + q) ≫ f.homology q = f.cycles q ≫ D.homologyπ q :=
  (C.homologyIsCokernel (p + q + 1) (p + q)
    ((ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (p + q + 1) (p + q) by rfl))).fac
    (CokernelCofork.ofπ (f.cycles q ≫ D.homologyπ q) (f.boundary_class_zero q))
    WalkingParallelPair.one

theorem homology_unique (q : ℕ) (h : C.homology (p + q) ⟶ D.homology q)
    (hh : C.homologyπ (p + q) ≫ h = f.cycles q ≫ D.homologyπ q) : h = f.homology q := by
  apply (cancel_epi (C.homologyπ (p + q))).mp
  exact hh.trans (f.homologyπ_homology q).symm

def post (e : D ⟶ E) : Map C E p where
  component q := f.component q ≫ e.f q
  comm q := by
    rw [Category.assoc, e.comm, ← Category.assoc, f.comm, Category.assoc]

theorem post_cycles (e : D ⟶ E) (q : ℕ) :
    (f.post e).cycles q = f.cycles q ≫ HomologicalComplex.cyclesMap e q := by
  apply (cancel_mono (E.iCycles q)).mp
  rw [cycles_i, Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc, f.cycles_i,
    Category.assoc]
  rfl

theorem post_homology (e : D ⟶ E) (q : ℕ) :
    (f.post e).homology q = f.homology q ≫ HomologicalComplex.homologyMap e q := by
  apply (cancel_epi (C.homologyπ (p + q))).mp
  rw [homologyπ_homology, post_cycles, Category.assoc, ← HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, ← f.homologyπ_homology, Category.assoc]

def pre {B : ChainComplex (ModuleCat.{0} R) ℕ} (e : B ⟶ C) : Map B D p where
  component q := e.f (p + q) ≫ f.component q
  comm q := by
    rw [Category.assoc, f.comm, ← Category.assoc, e.comm, Category.assoc]

theorem pre_cycles {B : ChainComplex (ModuleCat.{0} R) ℕ} (e : B ⟶ C) (q : ℕ) :
    (f.pre e).cycles q = HomologicalComplex.cyclesMap e (p + q) ≫ f.cycles q := by
  apply (cancel_mono (D.iCycles q)).mp
  rw [cycles_i, Category.assoc, f.cycles_i, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc]
  rfl

theorem pre_homology {B : ChainComplex (ModuleCat.{0} R) ℕ} (e : B ⟶ C) (q : ℕ) :
    (f.pre e).homology q = HomologicalComplex.homologyMap e (p + q) ≫ f.homology q := by
  apply (cancel_epi (B.homologyπ (p + q))).mp
  rw [homologyπ_homology, pre_cycles, Category.assoc, ← f.homologyπ_homology,
    HomologicalComplex.homologyπ_naturality_assoc]

theorem homology_eq_of_components (g : Map C D p) (h : ∀ q, f.component q = g.component q)
    (q : ℕ) : f.homology q = g.homology q := by
  have hc : f.cycles q = g.cycles q := by
    apply (cancel_mono (D.iCycles q)).mp
    rw [f.cycles_i, g.cycles_i, h q]
  apply (cancel_epi (C.homologyπ (p + q))).mp
  rw [f.homologyπ_homology, g.homologyπ_homology, hc]

end Map

end
end Finsler.DegreeLoweringHomology
