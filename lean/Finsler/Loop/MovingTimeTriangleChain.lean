module

public import Finsler.Loop.MovingTimeTriangleGeometry
public import Finsler.Loop.UniversalTimeTriangleChain
public import Finsler.Topology.BorelCochain

/-! The ORIGINAL shuffle time interval splits at a SOURCE-DEPENDENT
clock. The actual universal triangle gives the full chain identity,
retaining both output and SOURCE boundary terms. Closed cochains kill
only the output term; the source term remains explicitly in the formula. -/
@[expose] public section
namespace Finsler.MovingTimeTriangleChain
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

variable {X Y : TopCat.{0}}

def component (f : X ⊗ TopCat.I ⟶ Y) (a b : X ⟶ TopCat.I) (p : ℕ) :=
  UniversalTimeTriangleChain.interval X p ≫ (push (MovingTimeTriangleGeometry.segment a b ≫ f)).f (p + 1)

def comparison (f : X ⊗ TopCat.I ⟶ Y) (a : Fin 3 → (X ⟶ TopCat.I)) (p : ℕ) :=
  UniversalTimeTriangleChain.postTriangle (MovingTimeTriangleGeometry.triangleMap a ≫ f) p

theorem edge_component (f : X ⊗ TopCat.I ⟶ Y) (a : Fin 3 → (X ⟶ TopCat.I)) (i : Fin 3) (p : ℕ) :
    UniversalTimeTriangleChain.postEdge (MovingTimeTriangleGeometry.triangleMap a ≫ f) i p =
      component f (a (i.succAbove 0)) (a (i.succAbove 1)) p := by
  have hm : (X ◁ UniversalTimeTriangle.edgeMap i) ≫ (MovingTimeTriangleGeometry.triangleMap a ≫ f) =
      MovingTimeTriangleGeometry.segment (a (i.succAbove 0)) (a (i.succAbove 1)) ≫ f :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun h => h ≫ f) (MovingTimeTriangleGeometry.edge a i))
  have he := congrArg (fun h => UniversalTimeTriangleChain.interval X p ≫ (push h).f (p + 1)) hm
  simpa only [UniversalTimeTriangleChain.postEdge, UniversalTimeTriangleChain.edge, component,
    push_comp, HomologicalComplex.comp_f, Category.assoc] using he

theorem full_boundary (f : X ⊗ TopCat.I ⟶ Y) (a : Fin 3 → (X ⟶ TopCat.I)) (p : ℕ) :
    comparison f a (p + 1) ≫ (chains Y).d (p + 3) (p + 2) =
      (chains X).d (p + 1) p ≫ comparison f a p + component f (a 1) (a 2) (p + 1) +
        component f (a 0) (a 2) (p + 1) + component f (a 0) (a 1) (p + 1) := by
  have h := UniversalTimeTriangleChain.post_full_boundary (MovingTimeTriangleGeometry.triangleMap a ≫ f) p
  simpa only [comparison, edge_component,
    show (0 : Fin 3).succAbove (0 : Fin 2) = 1 from by decide,
    show (0 : Fin 3).succAbove (1 : Fin 2) = 2 from by decide,
    show (1 : Fin 3).succAbove (0 : Fin 2) = 0 from by decide,
    show (1 : Fin 3).succAbove (1 : Fin 2) = 2 from by decide,
    show (2 : Fin 3).succAbove (0 : Fin 2) = 0 from by decide,
    show (2 : Fin 3).succAbove (1 : Fin 2) = 1 from by decide] using h

theorem closed_relation (f : X ⊗ TopCat.I ⟶ Y) (a : Fin 3 → (X ⟶ TopCat.I)) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (p + 2))
    (hφ : cochainCoboundary (ZMod 2) Y (p + 2) φ = 0) :
    (chains X).d (p + 1) p ≫ comparison f a p ≫ φ +
      component f (a 1) (a 2) (p + 1) ≫ φ + component f (a 0) (a 2) (p + 1) ≫ φ +
      component f (a 0) (a 1) (p + 1) ≫ φ = 0 := by
  have h := congrArg (fun h => h ≫ φ) (full_boundary f a p)
  change (chains Y).d (p + 3) (p + 2) ≫ φ = 0 at hφ
  simp only [Preadditive.add_comp, Category.assoc, hφ, comp_zero] at h
  exact h.symm

theorem closed_split (f : X ⊗ TopCat.I ⟶ Y) (a : Fin 3 → (X ⟶ TopCat.I)) (p : ℕ)
    (φ : singularCochainGroup (ZMod 2) Y (p + 2))
    (hφ : cochainCoboundary (ZMod 2) Y (p + 2) φ = 0) :
    component f (a 0) (a 2) (p + 1) ≫ φ =
      component f (a 0) (a 1) (p + 1) ≫ φ + component f (a 1) (a 2) (p + 1) ≫ φ +
      (chains X).d (p + 1) p ≫ comparison f a p ≫ φ := by
  have h := closed_relation f a p φ hφ
  let R := component f (a 0) (a 1) (p + 1) ≫ φ + component f (a 1) (a 2) (p + 1) ≫ φ +
    (chains X).d (p + 1) p ≫ comparison f a p ≫ φ
  apply add_right_cancel (b := R)
  have hz : R + R = 0 := BorelCochain.two_eq_zero_of_mod R
  calc
    _ = (chains X).d (p + 1) p ≫ comparison f a p ≫ φ +
      component f (a 1) (a 2) (p + 1) ≫ φ + component f (a 0) (a 2) (p + 1) ≫ φ +
      component f (a 0) (a 1) (p + 1) ≫ φ := by dsimp only [R]; abel
    _ = 0 := h
    _ = R + R := hz.symm

end
end Finsler.MovingTimeTriangleChain
