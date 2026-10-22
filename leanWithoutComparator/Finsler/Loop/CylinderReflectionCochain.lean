module

public import Finsler.Loop.ClosedCochainPrismOpposite
public import Finsler.Loop.DoubleRelativeTimeCylinder
public import Finsler.Topology.TimePrismNaturality

/-! A closed cylinder test vanishing at time zero has an ACTUAL
contraction-prism primitive. Opposite endpoint traces then give equality
of forward and reflected prism values on cycles over F2. -/
@[expose] public section
namespace Finsler.CylinderReflectionCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.DoubleRelativeTimeCylinder
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def projection (X : TopCat.{0}) : cylinder X ⟶ X := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

def contraction (X : TopCat.{0}) : TopCat.Homotopy (𝟙 (cylinder X)) (projection X ≫ atTime X 0) where
  toFun z := (unitInterval.symm z.1 * z.2.1, z.2.2)
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change (unitInterval.symm 0 * z.1, z.2) = z
    rw [unitInterval.symm_zero, one_mul]
  map_one_left z := by
    change (unitInterval.symm 1 * z.1, z.2) = (0, z.2)
    rw [unitInterval.symm_one, zero_mul]

def primitive (X : TopCat.{0}) (q : ℕ) (T : singularCochainGroup (ZMod 2) (cylinder X) (q + 1)) :
    singularCochainGroup (ZMod 2) (cylinder X) q :=
  ((contraction X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ T

theorem primitive_boundary (X : TopCat.{0}) (q : ℕ)
    (T : singularCochainGroup (ZMod 2) (cylinder X) (q + 1))
    (hT : cochainCoboundary (ZMod 2) _ (q + 1) T = 0)
    (h0 : cochainPullback (atTime X 0) (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) _ q (primitive X q T) = T := by
  have hz : cochainPullback (projection X) (q + 1) (0 : singularCochainGroup (ZMod 2) X (q + 1)) = 0 := map_zero _
  rw [primitive, ClosedCochainPrismOpposite.closed_boundary _ _ _ hT, pullback_comp, h0, hz, sub_zero]
  change (push (𝟙 (cylinder X))).f (q + 1) ≫ T = T
  have hid : push (𝟙 (cylinder X)) = 𝟙 (chains (cylinder X)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.{0}.map (𝟙 (cylinder X))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.id_f, Category.id_comp]

def reflection (X : TopCat.{0}) : cylinder X ⟶ cylinder X :=
  TopCat.ofHom ⟨fun z => (unitInterval.symm z.1, z.2), by fun_prop⟩

def reversed (X : TopCat.{0}) : TopCat.Homotopy (atTime X 1) (atTime X 0) where
  toFun z := (unitInterval.symm z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left z := by change (unitInterval.symm 0, z) = (1, z); rw [unitInterval.symm_zero]
  map_one_left z := by change (unitInterval.symm 1, z) = (0, z); rw [unitInterval.symm_one]

theorem reflected_prism (X : TopCat.{0}) (q : ℕ) :
    ((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ (push (reflection X)).f (q + 1) =
      ((reversed X).toSSet.chainComplexMap coeff).hom q (q + 1) := by
  rw [TimePrismNaturality.prism_post]
  apply TimePrismNaturality.prism_congr
  ext z : 1
  rfl

theorem cycle_values (X : TopCat.{0}) (q : ℕ)
    (T : singularCochainGroup (ZMod 2) (cylinder X) (q + 1))
    (hT : cochainCoboundary (ZMod 2) _ (q + 1) T = 0)
    (h0 : cochainPullback (atTime X 0) (q + 1) T = 0) :
    (chains X).iCycles q ≫ ((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      cochainPullback (reflection X) (q + 1) T =
    (chains X).iCycles q ≫ ((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ T := by
  change (chains X).iCycles q ≫ (((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫
    (push (reflection X)).f (q + 1) ≫ T) = _
  rw [← Category.assoc (((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1)), reflected_prism]
  rw [← primitive_boundary X q T hT h0]
  exact ClosedCochainPrismOpposite.opposite_boundary_values (reversed X) (homotopy X) q _

end
end Finsler.CylinderReflectionCochain
