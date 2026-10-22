module

public import Finsler.Loop.FirstFactorSimplicialTimeModelComparison
public import Finsler.Topology.SingularTimeCylinderMaps
public import Finsler.Loop.FullFirstFactorTimePrism
public import Finsler.Topology.DegreeLoweringExact

/-! Map the constructed simplicial double prism into the actual
singular time space. Both actual product-time and first-input tensor
prisms are identified, including coefficient multiplication. Their
difference on every input cycle is an explicit actual boundary. -/

@[expose] public section
namespace Finsler.FirstFactorSingularTimeModelComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.IntervalSobolev Finsler.SingularTimeCylinderMaps
open Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

def reorder (X Y : TopCat.{0}) : TopCat.of (ClosedInterval × X) ⊗ Y ⟶
    X ⊗ TopCat.of (ClosedInterval × Y) :=
  TopCat.ofHom ⟨fun z => (z.1.2, (z.1.1, z.2)), by fun_prop⟩

def cross (X Y : TopCat.{0}) :=
  SmallRectangleCross.ambient (TopCat.of (ClosedInterval × X)) Y ≫ push (reorder X Y)

theorem model_square (X Y : TopCat.{0}) :
    (timePair X ⊗ₘ 𝟙 (TopCat.toSSet.obj Y)) ≫
      CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (ClosedInterval × X)) Y ≫
      TopCat.toSSet.map (reorder X Y) =
    FirstFactorSimplicialTimeModelComparison.reorder (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
      modelMap X Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rcases z with ⟨⟨s, σ⟩, τ⟩
  apply (TopCat.toSSetObjEquiv (X ⊗ TopCat.of (ClosedInterval × Y)) n).injective
  apply ContinuousMap.ext
  intro t
  change (X ⊗ TopCat.of (ClosedInterval × Y)).toSSetObjEquiv n
    ((TopCat.toSSet.map (reorder X Y)).app n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of (ClosedInterval × X)) Y).app n
        ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of ClosedInterval) X).app n
          ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s), σ), τ))) t =
    (X ⊗ TopCat.of (ClosedInterval × Y)).toSSetObjEquiv n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X (TopCat.of (ClosedInterval × Y))).app n
        (σ, (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of ClosedInterval) Y).app n
          ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s), τ))) t
  erw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  simp only [ContinuousMap.comp_apply, mu_eval]
  erw [mu_eval (TopCat.of ClosedInterval) X n
    ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s)) σ t,
    mu_eval (TopCat.of ClosedInterval) Y n
    ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s)) τ t]
  rfl

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
    (SSet.chainComplexMap (timePair X) coeff ⊗ₘ 𝟙 (chains Y)) ≫ cross X Y =
    FirstFactorSimplicialTimeModelComparison.reorderedCross (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
      SSet.chainComplexMap (modelMap X Y) coeff := by
  rw [cross, ← SimplicialChainCross.to_top (TopCat.of (ClosedInterval × X)) Y,
    ← Category.assoc, ← Category.assoc, FirstFactorTensorPrismNaturality.cross_identity_right,
    Category.assoc, Category.assoc]
  change _ ≫
    (SSet.chainComplexMap (timePair X ⊗ₘ 𝟙 (TopCat.toSSet.obj Y)) coeff ≫
      (SSet.chainComplexMap (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet
        (TopCat.of (ClosedInterval × X)) Y) coeff ≫
        SSet.chainComplexMap (TopCat.toSSet.map (reorder X Y)) coeff)) = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    model_square, CategoryTheory.Functor.map_comp]
  rfl

theorem tensor_component (X Y : TopCat.{0}) (N : ℕ) :
    (FullFirstFactorTimePrism.prism X Y).hom N (N + 1) ≫ (cross X Y).f (N + 1) =
    (FirstFactorSimplicialTimeModelComparison.tensorPrism (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).hom
      N (N + 1) ≫ (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 1) := by
  have hh (j : ℕ) : (𝟙 ((chains X).X j)) ≫
      ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).hom j (j + 1) =
      ((SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj X)).chainComplexMap coeff).hom j (j + 1) ≫
        (SSet.chainComplexMap (timePair X) coeff).f (j + 1) := by
    simpa only [HomologicalComplex.id_f, Category.id_comp, AnnularTimeTrim.prism] using second_prism X j
  have ht := FirstFactorTensorPrismNaturality.naturality
    ((SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj X)).chainComplexMap coeff)
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff)
    (𝟙 (chains X)) (SSet.chainComplexMap (timePair X) coeff) (𝟙 (chains Y)) hh N
  have ht' : (FullFirstFactorTimePrism.prism X Y).hom N (N + 1) =
      (FirstFactorTensorPrismNaturality.prism
        ((SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj X)).chainComplexMap coeff)
        (chains Y)).hom N (N + 1) ≫
        (SSet.chainComplexMap (timePair X) coeff ⊗ₘ 𝟙 (chains Y)).f (N + 1) := by
    simpa only [id_tensorHom_id, HomologicalComplex.id_f, Category.id_comp,
      FullFirstFactorTimePrism.prism] using ht
  have hx := congrArg (fun f => f.f (N + 1)) (tensor_cross X Y)
  simp only [HomologicalComplex.comp_f] at hx
  rw [ht', Category.assoc, hx, FirstFactorSimplicialTimeModelComparison.tensor_hom, Category.assoc]

def doublePrism (X Y : TopCat.{0}) (N : ℕ) :
    (chains X ⊗ chains Y).X N ⟶ (chains (X ⊗ TopCat.of (ClosedInterval × Y))).X (N + 2) :=
  FirstFactorSimplicialTimeModelComparison.doublePrism N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
    (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 2)

theorem difference_component (X Y : TopCat.{0}) (N : ℕ) :
    (SmallRectangleCross.ambient X Y).f N ≫ ((cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) -
      (FullFirstFactorTimePrism.prism X Y).hom N (N + 1) ≫
        (cross X Y).f (N + 1) =
    FirstFactorSimplicialTimeModelComparison.difference N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
      (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 1) := by
  rw [product_component, tensor_component]
  simp only [FirstFactorSimplicialTimeModelComparison.difference, Preadditive.sub_comp]

theorem cycle_boundary (X Y : TopCat.{0}) (N : ℕ) :
    (chains X ⊗ chains Y).iCycles N ≫
      ((SmallRectangleCross.ambient X Y).f N ≫ ((cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) -
        (FullFirstFactorTimePrism.prism X Y).hom N (N + 1) ≫
          (cross X Y).f (N + 1)) =
    ((chains X ⊗ chains Y).iCycles N ≫ doublePrism X Y N) ≫
      (chains (X ⊗ TopCat.of (ClosedInterval × Y))).d (N + 2) (N + 1) := by
  have hp : (chains X ⊗ chains Y).iCycles N ≫
      FirstFactorSimplicialTimeModelComparison.difference N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) =
      ((chains X ⊗ chains Y).iCycles N ≫
        FirstFactorSimplicialTimeModelComparison.doublePrism N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)) ≫
      ((Finsler.TripleTimeModelExtension.target (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).chainComplex coeff).d
        (N + 2) (N + 1) :=
    FirstFactorSimplicialTimeModelComparison.cycle_boundary N (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
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
      (FullFirstFactorTimePrism.prism X Y).hom (d + q) (d + q + 1) ≫
        (cross X Y).f (d + q + 1) ≫ v q) =
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
    (hb : ∀ q, b.component q = (FullFirstFactorTimePrism.prism X Y).hom (d + q) (d + q + 1) ≫
      (cross X Y).f (d + q + 1) ≫ v q) (q : ℕ) :
    a.homology q = b.homology q := by
  apply DegreeLoweringExact.homology_eq_of_cycle_boundary a b q
    (doublePrism X Y (d + q) ≫ v (q + 1))
  rw [ha, hb]
  exact capped_cycle_boundary X Y d v hv q

end
end Finsler.FirstFactorSingularTimeModelComparison
