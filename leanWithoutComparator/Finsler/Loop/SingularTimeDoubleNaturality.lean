module

public import Finsler.Topology.SingularTimeModelComparison

/-! Naturality of the SAME constructive double prism in the actual
second topological input. It preserves each second-factor carrier,
including each separate endpoint of an inserted interval. -/
@[expose] public section
namespace Finsler.SingularTimeDoubleNaturality
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open scoped Simplicial
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.IntervalSobolev
open Finsler.SupportedCapNaturality Finsler.SingularTimeCylinderMaps
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

abbrev timeMap {Y Z : TopCat.{0}} (g : Y ⟶ Z) :
    TopCat.of (ClosedInterval × Y) ⟶ TopCat.of (ClosedInterval × Z) :=
  TopCat.of ClosedInterval ◁ g

theorem timePair_natural {Y Z : TopCat.{0}} (g : Y ⟶ Z) :
    ((Δ[1] : SSet.{0}) ◁ TopCat.toSSet.map g) ≫ timePair Z =
      timePair Y ≫ TopCat.toSSet.map (timeMap g) := by
  unfold timePair timeMap
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural_right]
  simp only [tensorHom_def, ← whisker_exchange_assoc, whiskerLeft_id, Category.comp_id]

theorem model_natural (X : TopCat.{0}) {Y Z : TopCat.{0}} (g : Y ⟶ Z) :
    (TopCat.toSSet.obj X ◁ ((Δ[1] : SSet.{0}) ◁ TopCat.toSSet.map g)) ≫ modelMap X Z =
      modelMap X Y ≫ TopCat.toSSet.map (X ◁ timeMap g) := by
  dsimp only [modelMap, TripleTimeModelExtension.target]
  simp only [id_tensorHom]
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
    ← whiskerLeft_comp_assoc, timePair_natural, whiskerLeft_comp, Category.assoc]

theorem naturality (X : TopCat.{0}) {Y Z : TopCat.{0}} (g : Y ⟶ Z) (N : ℕ) :
    (𝟙 (chains X) ⊗ₘ push g).f N ≫ SingularTimeModelComparison.doublePrism X Z N =
      SingularTimeModelComparison.doublePrism X Y N ≫ (push (X ◁ timeMap g)).f (N + 2) := by
  have h := SimplicialTimeModelComparison.double_naturality
    (𝟙 (TopCat.toSSet.obj X)) (TopCat.toSSet.map g) N
  have hid : SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj X)) coeff = 𝟙 (chains X) :=
    ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map_id _
  rw [hid] at h
  have hc := congrArg (fun f => f ≫ (SSet.chainComplexMap (modelMap X Z) coeff).f (N + 2)) h
  have hm : (SSet.chainComplexMap
      (𝟙 (TopCat.toSSet.obj X) ⊗ₘ (𝟙 (Δ[1] : SSet.{0}) ⊗ₘ TopCat.toSSet.map g)) coeff).f (N + 2) ≫
      (SSet.chainComplexMap (modelMap X Z) coeff).f (N + 2) =
    (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 2) ≫ (push (X ◁ timeMap g)).f (N + 2) := by
    rw [← HomologicalComplex.comp_f, ← CategoryTheory.Functor.map_comp]
    simp only [id_tensorHom]
    rw [model_natural, CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
    rfl
  simp only [Category.assoc, hm] at hc
  exact hc

theorem scalar_zero (X : TopCat.{0}) {Y Z : TopCat.{0}} (g : Y ⟶ Z) (N : ℕ)
    (T : singularCochainGroup (ZMod 2) (X ⊗ TopCat.of (ClosedInterval × Z)) (N + 2))
    (hT : cochainPullback (X ◁ timeMap g) (N + 2) T = 0) :
    (𝟙 (chains X) ⊗ₘ push g).f N ≫ SingularTimeModelComparison.doublePrism X Z N ≫ T = 0 := by
  rw [← Category.assoc, naturality, Category.assoc]
  change SingularTimeModelComparison.doublePrism X Y N ≫ cochainPullback (X ◁ timeMap g) (N + 2) T = 0
  rw [hT, comp_zero]

end
end Finsler.SingularTimeDoubleNaturality
