module

public import Finsler.Topology.SimplicialTimeModelComparison
public import Finsler.Topology.SingularTimeCylinderMaps
public import Finsler.Topology.FullTensorTimePrism
public import Finsler.Topology.DegreeLoweringExact

/-! Map the constructed simplicial double prism into the actual
singular time space. Both actual product-time and second-input tensor
prisms are identified, including coefficient multiplication. Their
difference on every input cycle is an explicit actual boundary. -/

@[expose] public section
namespace Finsler.SingularTimeModelComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.IntervalSobolev Finsler.SingularTimeCylinderMaps
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem product_component (X Y : TopCat.{0}) (N : ℕ) :
    (SmallRectangleCross.ambient X Y).f N ≫ ((cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) =
    (SimplicialTimeModelComparison.productPrism (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).hom N (N + 1) ≫
      (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 1) := by
  have hx : (SimplicialChainCross.cross (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).f N ≫
      (SSet.chainComplexMap (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y) coeff).f N =
      (SmallRectangleCross.ambient X Y).f N := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun f => f.f N) (SimplicialChainCross.to_top X Y)
  have hh := congrArg
    (fun f => (SimplicialChainCross.cross (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).f N ≫ f)
    (product_prism X Y N)
  simpa only [SimplicialTimeModelComparison.productPrism, Homotopy.compLeft_hom,
    ← Category.assoc, hx] using hh

theorem tensor_cross (X Y : TopCat.{0}) :
    (𝟙 (chains X) ⊗ₘ SSet.chainComplexMap (timePair Y) coeff) ≫
      SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y)) =
    SimplicialChainCross.cross (TopCat.toSSet.obj X) ((Δ[1] : SSet.{0}) ⊗ TopCat.toSSet.obj Y) ≫
      SSet.chainComplexMap (modelMap X Y) coeff := by
  rw [← SimplicialChainCross.to_top X (TopCat.of (ClosedInterval × Y)),
    ← Category.assoc, SimplicialChainCross.identity_left, Category.assoc]
  change _ ≫
    (SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj X) ⊗ₘ timePair Y) coeff ≫
      SSet.chainComplexMap (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X (TopCat.of (ClosedInterval × Y))) coeff) = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

theorem tensor_component (X Y : TopCat.{0}) (N : ℕ) :
    (FullTensorTimePrism.prism X Y).hom N (N + 1) ≫
      (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y))).f (N + 1) =
    (SimplicialTimeModelComparison.tensorPrism (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).hom N (N + 1) ≫
      (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 1) := by
  have hh (k : ℕ) : (𝟙 ((chains Y).X k)) ≫
      ((AnnularTimeTrim.cylinder Y).toSSet.chainComplexMap coeff).hom k (k + 1) =
      ((SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj Y)).chainComplexMap coeff).hom k (k + 1) ≫
        (SSet.chainComplexMap (timePair Y) coeff).f (k + 1) := by
    simpa only [HomologicalComplex.id_f, Category.id_comp, AnnularTimeTrim.prism] using second_prism Y k
  have ht := TensorIdentityPrismNaturality.naturality
    ((SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj Y)).chainComplexMap coeff)
    ((AnnularTimeTrim.cylinder Y).toSSet.chainComplexMap coeff)
    (𝟙 (chains X)) (𝟙 (chains Y)) (SSet.chainComplexMap (timePair Y) coeff) hh N
  have ht' : (FullTensorTimePrism.prism X Y).hom N (N + 1) =
      (TensorIdentityPrismNaturality.prism (chains X)
        ((SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj Y)).chainComplexMap coeff)).hom N (N + 1) ≫
        (𝟙 (chains X) ⊗ₘ SSet.chainComplexMap (timePair Y) coeff).f (N + 1) := by
    simpa only [id_tensorHom_id, HomologicalComplex.id_f, Category.id_comp,
      FullTensorTimePrism.prism, TensorIdentityPrismNaturality.prism] using ht
  have hx : (𝟙 (chains X) ⊗ₘ SSet.chainComplexMap (timePair Y) coeff).f (N + 1) ≫
      (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y))).f (N + 1) =
      (SimplicialChainCross.cross (TopCat.toSSet.obj X) ((Δ[1] : SSet.{0}) ⊗ TopCat.toSSet.obj Y)).f (N + 1) ≫
        (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 1) := by
    simpa only [HomologicalComplex.comp_f] using congrArg (fun f => f.f (N + 1)) (tensor_cross X Y)
  rw [ht', Category.assoc, hx, SimplicialTimeModelComparison.tensor_hom, Category.assoc]

def doublePrism (X Y : TopCat.{0}) (N : ℕ) :
    (chains X ⊗ chains Y).X N ⟶ (chains (X ⊗ TopCat.of (ClosedInterval × Y))).X (N + 2) :=
  SimplicialTimeModelComparison.doublePrism N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
    (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 2)

theorem difference_component (X Y : TopCat.{0}) (N : ℕ) :
    (SmallRectangleCross.ambient X Y).f N ≫ ((cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) -
      (FullTensorTimePrism.prism X Y).hom N (N + 1) ≫
        (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y))).f (N + 1) =
    SimplicialTimeModelComparison.difference N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
      (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 1) := by
  rw [product_component, tensor_component]
  simp only [SimplicialTimeModelComparison.difference, Preadditive.sub_comp]

theorem cycle_boundary (X Y : TopCat.{0}) (N : ℕ) :
    (chains X ⊗ chains Y).iCycles N ≫
      ((SmallRectangleCross.ambient X Y).f N ≫ ((cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) -
        (FullTensorTimePrism.prism X Y).hom N (N + 1) ≫
          (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y))).f (N + 1)) =
    ((chains X ⊗ chains Y).iCycles N ≫ doublePrism X Y N) ≫
      (chains (X ⊗ TopCat.of (ClosedInterval × Y))).d (N + 2) (N + 1) := by
  have hp : (chains X ⊗ chains Y).iCycles N ≫
      SimplicialTimeModelComparison.difference N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) =
      ((chains X ⊗ chains Y).iCycles N ≫
        SimplicialTimeModelComparison.doublePrism N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)) ≫
      ((Finsler.TripleTimeModelExtension.target (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).chainComplex coeff).d
        (N + 2) (N + 1) :=
    SimplicialTimeModelComparison.cycle_boundary N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
  rw [difference_component, ← Category.assoc, hp, Category.assoc,
    ← (SSet.chainComplexMap (modelMap X Y) coeff).comm]
  simp only [doublePrism, Category.assoc]

variable (X Y : TopCat.{0}) {E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (d : ℕ)
  (v : ∀ q, (chains (X ⊗ TopCat.of (ClosedInterval × Y))).X (d + q + 1) ⟶ E.X q)
  (hv : ∀ q, v (q + 1) ≫ E.d (q + 1) q =
    (chains (X ⊗ TopCat.of (ClosedInterval × Y))).d (d + q + 2) (d + q + 1) ≫ v q)

include hv in
theorem capped_cycle_boundary (q : ℕ) :
    (chains X ⊗ chains Y).iCycles (d + q) ≫
      ((SmallRectangleCross.ambient X Y).f (d + q) ≫
        ((cylinder X Y).toSSet.chainComplexMap coeff).hom (d + q) (d + q + 1) ≫ v q -
      (FullTensorTimePrism.prism X Y).hom (d + q) (d + q + 1) ≫
        (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y))).f (d + q + 1) ≫ v q) =
    ((chains X ⊗ chains Y).iCycles (d + q) ≫ doublePrism X Y (d + q) ≫ v (q + 1)) ≫ E.d (q + 1) q := by
  have hh := congrArg (fun f => f ≫ v q) (cycle_boundary X Y (d + q))
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc] at hh
  rw [← hv q] at hh
  simpa only [Category.assoc, Preadditive.comp_sub] using hh

include hv in
theorem homology_eq
    (a b : DegreeLoweringHomology.Map (chains X ⊗ chains Y) E d)
    (ha : ∀ q, a.component q = (SmallRectangleCross.ambient X Y).f (d + q) ≫
      ((cylinder X Y).toSSet.chainComplexMap coeff).hom (d + q) (d + q + 1) ≫ v q)
    (hb : ∀ q, b.component q = (FullTensorTimePrism.prism X Y).hom (d + q) (d + q + 1) ≫
      (SmallRectangleCross.ambient X (TopCat.of (ClosedInterval × Y))).f (d + q + 1) ≫ v q) (q : ℕ) :
    a.homology q = b.homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary a b q
    (doublePrism X Y (d + q) ≫ v (q + 1))
  rw [ha, hb]
  exact capped_cycle_boundary X Y d v hv q

end
end Finsler.SingularTimeModelComparison
