module

public import Finsler.Topology.TimeShuffleComparison
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Basic
public import Finsler.Topology.BorelCochain

/-! The actual singular interval simplex and an affine triangle with
vertices 0, 1/2 and 1. Face and capped shuffle comparison are separate. -/

@[expose] public section
namespace Finsler.IntervalTriangle

open CategoryTheory AlgebraicTopology Convexity
open Finsler.SmallChainCarrier Finsler.CochainComparison
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def intervalMap : C(StdSimplex ℝ (Fin 2), TopCat.I.{0}) :=
  ⟨TopCat.stdSimplexHomeomorphI, TopCat.stdSimplexHomeomorphI.continuous⟩

theorem canonical_interval :
    (TopCat.I.toSSetObjEquiv _ TimeShuffleComparison.intervalSimplex) = intervalMap := by
  have hy : SSet.yonedaEquiv.symm (ULift.up (𝟙 (⦋1⦌ : SimplexCategory))) = 𝟙 (Δ[1] : SSet.{0}) := by
    apply SSet.yonedaEquiv.injective
    rfl
  have he : TimeShuffleComparison.intervalSimplex.down =
      SSet.toTopSimplex.inv.app ⦋1⦌ ≫ SSet.stdSimplex.toTopObjIsoI.hom := by
    unfold TimeShuffleComparison.intervalSimplex SSet.stdSimplex.toSSetObjI
    rw [Adjunction.homEquiv_unit]
    change ((sSetTopAdj.unit.app Δ[1]).app _ (ULift.up (𝟙 (⦋1⦌ : SimplexCategory)))).down ≫
      SSet.stdSimplex.toTopObjIsoI.hom = _
    rw [sSetTopAdj_unit_app_app_down, hy, CategoryTheory.Functor.map_id]
    exact congrArg (fun f => f ≫ SSet.stdSimplex.toTopObjIsoI.hom)
      (Category.comp_id (SSet.toTopSimplex.inv.app ⦋1⦌))
  ext x
  change ((((TimeShuffleComparison.intervalSimplex).down :
    SimplexCategory.toTop.obj ⦋1⦌ ⟶ TopCat.I).hom (ULift.up x)).down : ℝ) =
    ((TopCat.stdSimplexHomeomorphI x).down : ℝ)
  rw [he]
  simp [SSet.stdSimplex.toTopObjIsoI, SimplexCategory.toTopHomeo]
  exact congrArg (fun y : SimplexCategory.toTop.obj ⦋1⦌ =>
    ((TopCat.stdSimplexHomeomorphI (Homeomorph.ulift y)).down : ℝ))
      (ConcreteCategory.congr_hom ((SSet.toTopSimplex.app ⦋1⦌).inv_hom_id) (ULift.up x))

def vertices : Fin 3 → StdSimplex ℝ (Fin 2) :=
  ![StdSimplex.single 0, StdSimplex.barycenter, StdSimplex.single 1]

def triangleMap : C(StdSimplex ℝ (Fin 3), TopCat.I.{0}) :=
  intervalMap.comp (StdSimplex.continuousAffineMapMk vertices)

def triangle : TopCat.toSSet.obj TopCat.I.{0} _⦋2⦌ :=
  (TopCat.I.toSSetObjEquiv _).symm triangleMap

theorem canonical_simplex : TimeShuffleComparison.intervalSimplex =
    (TopCat.I.toSSetObjEquiv _).symm intervalMap := by
  apply (TopCat.I.toSSetObjEquiv _).injective
  rw [canonical_interval, Equiv.apply_symm_apply]

def firstMap : TopCat.I.{0} ⟶ TopCat.I.{0} :=
  TopCat.ofHom ⟨fun t => ULift.up ⟨(t.down : ℝ) / 2, by
    constructor <;> linarith [t.down.property.1, t.down.property.2]⟩, by fun_prop⟩

def secondMap : TopCat.I.{0} ⟶ TopCat.I.{0} :=
  TopCat.ofHom ⟨fun t => ULift.up ⟨(1 + (t.down : ℝ)) / 2, by
    constructor <;> linarith [t.down.property.1, t.down.property.2]⟩, by fun_prop⟩

theorem interval_coordinate (x : StdSimplex ℝ (Fin 2)) :
    ((intervalMap x).down : ℝ) = x.weights 1 := by
  change (StdSimplex.homeomorphI x).val = x.weights 1
  exact StdSimplex.homeomorphI_apply_coe x

private theorem first_coordinate (t : TopCat.I.{0}) :
    ((firstMap t).down : ℝ) = (t.down : ℝ) / 2 := rfl

private theorem second_coordinate (t : TopCat.I.{0}) :
    ((secondMap t).down : ℝ) = (1 + (t.down : ℝ)) / 2 := rfl

theorem face_zero : (TopCat.toSSet.obj TopCat.I).δ (0 : Fin 3) triangle =
    (TopCat.toSSet.map secondMap).app _ TimeShuffleComparison.intervalSimplex := by
  rw [triangle, triangleMap, TauCeti.TopCat.δ_toSSetObjEquiv_symm_comp_affineMapMk,
    canonical_simplex, TauCeti.TopCat.toSSet_map_app_toSSetObjEquiv_symm]
  apply (TopCat.I.toSSetObjEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  ext x
  simp only [ContinuousMap.comp_apply, StdSimplex.continuousAffineMapMk_apply]
  change ((intervalMap (StdSimplex.affineMapMk (vertices ∘ (0 : Fin 3).succAbove) x)).down : ℝ) =
    ((secondMap (intervalMap x)).down : ℝ)
  rw [interval_coordinate, second_coordinate, interval_coordinate]
  have hs' : (∑ i : Fin 2, x.weights i) = 1 := x.total_of_fintype
  have hs : x.weights 0 + x.weights 1 = 1 := by
    simpa only [Fin.sum_univ_two] using hs'
  norm_num [StdSimplex.weights_affineMapMk_apply, vertices, Function.comp_def,
    Fin.sum_univ_two, StdSimplex.weights_barycenter_apply, Finsupp.single_apply]
  linarith

theorem face_one : (TopCat.toSSet.obj TopCat.I).δ (1 : Fin 3) triangle =
    TimeShuffleComparison.intervalSimplex := by
  rw [triangle, triangleMap, TauCeti.TopCat.δ_toSSetObjEquiv_symm_comp_affineMapMk, canonical_simplex]
  apply (TopCat.I.toSSetObjEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  ext x
  simp only [ContinuousMap.comp_apply, StdSimplex.continuousAffineMapMk_apply]
  change ((intervalMap (StdSimplex.affineMapMk (vertices ∘ (1 : Fin 3).succAbove) x)).down : ℝ) =
    ((intervalMap x).down : ℝ)
  rw [interval_coordinate, interval_coordinate]
  norm_num [StdSimplex.weights_affineMapMk_apply, vertices, Function.comp_def,
    Fin.sum_univ_two, Finsupp.single_apply]

theorem face_two : (TopCat.toSSet.obj TopCat.I).δ (2 : Fin 3) triangle =
    (TopCat.toSSet.map firstMap).app _ TimeShuffleComparison.intervalSimplex := by
  rw [triangle, triangleMap, TauCeti.TopCat.δ_toSSetObjEquiv_symm_comp_affineMapMk,
    canonical_simplex, TauCeti.TopCat.toSSet_map_app_toSSetObjEquiv_symm]
  apply (TopCat.I.toSSetObjEquiv _).injective
  simp only [Equiv.apply_symm_apply]
  ext x
  simp only [ContinuousMap.comp_apply, StdSimplex.continuousAffineMapMk_apply]
  change ((intervalMap (StdSimplex.affineMapMk (vertices ∘ (2 : Fin 3).succAbove) x)).down : ℝ) =
    ((firstMap (intervalMap x)).down : ℝ)
  rw [interval_coordinate, first_coordinate, interval_coordinate]
  have hv : (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide
  norm_num [StdSimplex.weights_affineMapMk_apply, vertices, Function.comp_def,
    Fin.sum_univ_two, StdSimplex.weights_barycenter_apply, Finsupp.single_apply, hv]
  ring

private theorem neg_self (f : coeff ⟶ (chains TopCat.I.{0}).X 1) : -f = f := by
  have h := BorelCochain.two_eq_zero_of_mod f
  calc
    -f = -f + (f + f) := by rw [h, add_zero]
    _ = f := by abel

theorem triangle_boundary :
    (TopCat.toSSet.obj TopCat.I).ιChainComplex triangle ≫ (chains TopCat.I).d 2 1 =
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫
        (SupportedCapNaturality.push secondMap).f 1 +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex +
      (TopCat.toSSet.obj TopCat.I).ιChainComplex TimeShuffleComparison.intervalSimplex ≫
        (SupportedCapNaturality.push firstMap).f 1 := by
  rw [SSet.ιChainComplex_d, Fin.sum_univ_three]
  norm_num [face_zero, face_one, face_two, neg_self,
    SupportedCapNaturality.push, SSet.ι_chainComplexMap_f]
  <;> abel

end
end Finsler.IntervalTriangle
