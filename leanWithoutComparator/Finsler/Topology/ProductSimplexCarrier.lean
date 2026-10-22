module

public import Finsler.Topology.SimplicialCarrierLift
public import Finsler.Topology.SingularChainCross
public import Finsler.Topology.SequentialCapWitness

/-! The actual universal product of two singular simplices lies in the
whole product of their parent images. A bound on that rectangle gives
a genuine simplicial map into the prescribed subspace, on every face
and degeneracy, before choosing a shuffle path. -/

@[expose] public section
namespace Finsler.ProductSimplexCarrier

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (X Y : TopCat.{0}) {j k : ℕ}
  (σ : TopCat.toSSet.obj X _⦋j⦌) (τ : TopCat.toSSet.obj Y _⦋k⦌)

def rectangle : Set (X ⊗ Y : TopCat.{0}) :=
  Set.range (X.toSSetObjEquiv _ σ) ×ˢ Set.range (Y.toSSetObjEquiv _ τ)

def model : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj (X ⊗ Y) :=
  (SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
    Functor.LaxMonoidal.μ TopCat.toSSet X Y

theorem model_fst {n : SimplexCategoryᵒᵖ}
    (z : ((Δ[j] : SSet.{0}) ⊗ Δ[k]).obj n)
    (t : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (((X ⊗ Y).toSSetObjEquiv n ((model X Y σ τ).app n z)) t).1 =
      (X.toSSetObjEquiv n ((SSet.yonedaEquiv.symm σ).app n z.1)) t := by
  have he := congrArg (fun f : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) ⟶ TopCat.toSSet.obj X =>
      (X.toSSetObjEquiv n (f.app n
        ((SSet.yonedaEquiv.symm σ).app n z.1, (SSet.yonedaEquiv.symm τ).app n z.2))) t)
    (Functor.Monoidal.μ_fst TopCat.toSSet X Y)
  change (X.toSSetObjEquiv n
    ((TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app n
      ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n
        ((SSet.yonedaEquiv.symm σ).app n z.1, (SSet.yonedaEquiv.symm τ).app n z.2)))) t = _ at he
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
  exact he

theorem model_snd {n : SimplexCategoryᵒᵖ}
    (z : ((Δ[j] : SSet.{0}) ⊗ Δ[k]).obj n)
    (t : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (((X ⊗ Y).toSSetObjEquiv n ((model X Y σ τ).app n z)) t).2 =
      (Y.toSSetObjEquiv n ((SSet.yonedaEquiv.symm τ).app n z.2)) t := by
  have he := congrArg (fun f : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) ⟶ TopCat.toSSet.obj Y =>
      (Y.toSSetObjEquiv n (f.app n
        ((SSet.yonedaEquiv.symm σ).app n z.1, (SSet.yonedaEquiv.symm τ).app n z.2))) t)
    (Functor.Monoidal.μ_snd TopCat.toSSet X Y)
  change (Y.toSSetObjEquiv n
    ((TopCat.toSSet.map (CartesianMonoidalCategory.snd X Y)).app n
      ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n
        ((SSet.yonedaEquiv.symm σ).app n z.1, (SSet.yonedaEquiv.symm τ).app n z.2)))) t = _ at he
  rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app] at he
  exact he

theorem model_parent (n : ℕ) (z : ((Δ[j] : SSet.{0}) ⊗ Δ[k]) _⦋n⦌) :
    Set.range ((X ⊗ Y).toSSetObjEquiv _ ((model X Y σ τ).app _ z)) ⊆ rectangle X Y σ τ := by
  rintro _ ⟨t, rfl⟩
  constructor
  · rw [model_fst]
    change X.toSSetObjEquiv _
      ((TopCat.toSSet.obj X).map (SSet.stdSimplex.objEquiv z.1).op σ) t ∈ _
    exact SequentialCapWitness.simplex_map_range X _ σ ⟨t, rfl⟩
  · rw [model_snd]
    change Y.toSSetObjEquiv _
      ((TopCat.toSSet.obj Y).map (SSet.stdSimplex.objEquiv z.2).op τ) t ∈ _
    exact SequentialCapWitness.simplex_map_range Y _ τ ⟨t, rfl⟩

def lift (D : Set (X ⊗ Y : TopCat.{0})) (hD : rectangle X Y σ τ ⊆ D) :
    ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ TopCat.toSSet.obj (TopCat.of D) :=
  SimplicialCarrierLift.lift (X ⊗ Y) D (model X Y σ τ)
    (fun n z => (model_parent X Y σ τ n z).trans hD)

theorem lift_inclusion (D : Set (X ⊗ Y : TopCat.{0})) (hD : rectangle X Y σ τ ⊆ D) :
    lift X Y σ τ D hD ≫ TopCat.toSSet.map (SupportedCap.subspaceMap (X ⊗ Y) D) =
      model X Y σ τ :=
  SimplicialCarrierLift.lift_inclusion _ _ _ _

end
end Finsler.ProductSimplexCarrier
