module

public import Finsler.Topology.SimplicialTimeCylinder
public import Finsler.Topology.TimePrismNaturality
public import Finsler.Topology.OriginalSecondHalfTimeOperation
import all Finsler.Topology.OriginalSecondHalfTimeOperation

/-! Map the genuine pure simplicial time cylinders to the actual
singular cylinders using the canonical interval simplex and actual
monoidal product comparison. Both coordinate squares are literal. -/

@[expose] public section
namespace Finsler.SingularTimeCylinderMaps

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.IntervalSobolev
open Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

def intervalDown : TopCat.I.{0} ⟶ TopCat.of ClosedInterval :=
  TopCat.ofHom ⟨fun t => t.down, continuous_uliftDown⟩

def timePair (Y : TopCat.{0}) : (Δ[1] : SSet.{0}) ⊗ TopCat.toSSet.obj Y ⟶
    TopCat.toSSet.obj (TopCat.of (ClosedInterval × Y)) :=
  ((SSet.stdSimplex.toSSetObjI ≫ TopCat.toSSet.map intervalDown) ⊗ₘ 𝟙 (TopCat.toSSet.obj Y)) ≫
    CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of ClosedInterval) Y

def modelMap (X Y : TopCat.{0}) :
    Finsler.TripleTimeModelExtension.target (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ⟶
      TopCat.toSSet.obj (X ⊗ TopCat.of (ClosedInterval × Y)) :=
  (𝟙 (TopCat.toSSet.obj X) ⊗ₘ timePair Y) ≫
    CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X (TopCat.of (ClosedInterval × Y))

def slice (X Y : TopCat.{0}) (t : ClosedInterval) : X ⊗ Y ⟶ X ⊗ TopCat.of (ClosedInterval × Y) :=
  𝟙 X ⊗ₘ AnnularTimeTrim.slice Y t

def cylinder (X Y : TopCat.{0}) : TopCat.Homotopy (slice X Y 0) (slice X Y 1) where
  toFun z := (z.2.1, (z.1, z.2.2))
  continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem mu_eval (X Y : TopCat.{0}) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) (τ : (TopCat.toSSet.obj Y).obj n)
    (t : Convexity.StdSimplex ℝ (Fin (n.unop.len + 1))) :
    (X ⊗ Y).toSSetObjEquiv n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n (σ, τ)) t =
      (X.toSSetObjEquiv n σ t, Y.toSSetObjEquiv n τ t) := by
  have hf : (TopCat.toSSet.map (CartesianMonoidalCategory.fst X Y)).app n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n (σ, τ)) = σ :=
    congrArg (fun f => f.app n (σ, τ))
      (CategoryTheory.Functor.Monoidal.μ_fst (F := TopCat.toSSet) X Y)
  have hs : (TopCat.toSSet.map (CartesianMonoidalCategory.snd X Y)).app n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n (σ, τ)) = τ :=
    congrArg (fun f => f.app n (σ, τ))
      (CategoryTheory.Functor.Monoidal.μ_snd (F := TopCat.toSSet) X Y)
  apply Prod.ext
  · have he := congrArg (fun z => X.toSSetObjEquiv n z t) hf
    simpa only [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply,
      CartesianMonoidalCategory.fst_def, CartesianMonoidalCategory.snd_def,
      ConcreteCategory.comp_apply, TopCat.whiskerLeft_apply, TopCat.whiskerRight_apply,
      TopCat.rightUnitor_hom_apply, TopCat.leftUnitor_hom_apply] using he
  · have he := congrArg (fun z => Y.toSSetObjEquiv n z t) hs
    simpa only [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply,
      CartesianMonoidalCategory.fst_def, CartesianMonoidalCategory.snd_def,
      ConcreteCategory.comp_apply, TopCat.whiskerLeft_apply, TopCat.whiskerRight_apply,
      TopCat.rightUnitor_hom_apply, TopCat.leftUnitor_hom_apply] using he

theorem second_square (Y : TopCat.{0}) :
    (𝟙 (TopCat.toSSet.obj Y) ▷ (Δ[1] : SSet.{0})) ≫ (AnnularTimeTrim.cylinder Y).toSSet.h =
      (SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj Y)).h ≫ timePair Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rcases z with ⟨σ, s⟩
  apply (TopCat.toSSetObjEquiv (TopCat.of (ClosedInterval × Y)) n).injective
  apply ContinuousMap.ext
  intro t
  change (TopCat.of (ClosedInterval × Y)).toSSetObjEquiv n
    ((TopCat.toSSet.map (AnnularTimeTrim.cylinder Y).h).app n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet Y TopCat.I).app n
        (σ, SSet.stdSimplex.toSSetObjI.app n s))) t =
    (TopCat.of (ClosedInterval × Y)).toSSetObjEquiv n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of ClosedInterval) Y).app n
        ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s), σ)) t
  erw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  simp only [ContinuousMap.comp_apply, mu_eval]
  erw [mu_eval (TopCat.of ClosedInterval) Y n
    ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s)) σ t]
  simp only [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply]
  rfl

theorem product_square (X Y : TopCat.{0}) :
    (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y ▷ (Δ[1] : SSet.{0})) ≫
      (cylinder X Y).toSSet.h =
    (SimplicialTimeCylinder.productCylinder (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).h ≫
      modelMap X Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  rcases z with ⟨⟨σ, τ⟩, s⟩
  apply (TopCat.toSSetObjEquiv (X ⊗ TopCat.of (ClosedInterval × Y)) n).injective
  apply ContinuousMap.ext
  intro t
  change (X ⊗ TopCat.of (ClosedInterval × Y)).toSSetObjEquiv n
    ((TopCat.toSSet.map (cylinder X Y).h).app n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (X ⊗ Y) TopCat.I).app n
        ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y).app n (σ, τ),
          SSet.stdSimplex.toSSetObjI.app n s))) t =
    (X ⊗ TopCat.of (ClosedInterval × Y)).toSSetObjEquiv n
      ((CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X (TopCat.of (ClosedInterval × Y))).app n
        (σ, (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet (TopCat.of ClosedInterval) Y).app n
          ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s), τ))) t
  erw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
  simp only [ContinuousMap.comp_apply, mu_eval]
  erw [mu_eval (TopCat.of ClosedInterval) Y n
    ((TopCat.toSSet.map intervalDown).app n (SSet.stdSimplex.toSSetObjI.app n s)) τ t]
  simp only [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.comp_apply]
  rfl

theorem second_prism (Y : TopCat.{0}) (N : ℕ) :
    AnnularTimeTrim.prism Y N =
      ((SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj Y)).chainComplexMap coeff).hom N (N + 1) ≫
        (SSet.chainComplexMap (timePair Y) coeff).f (N + 1) := by
  have hi : SSet.chainComplexMap (𝟙 (TopCat.toSSet.obj Y)) coeff = 𝟙 (chains Y) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id]
  simpa only [hi, HomologicalComplex.id_f, Category.id_comp, AnnularTimeTrim.prism] using
    SSet.Homotopy.chainComplexMap_hom_comm
      (SimplicialTimeCylinder.secondCylinder (TopCat.toSSet.obj Y)) (AnnularTimeTrim.cylinder Y).toSSet
      (second_square Y) coeff N (N + 1)

theorem product_prism (X Y : TopCat.{0}) (N : ℕ) :
    (SSet.chainComplexMap (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y) coeff).f N ≫
      ((cylinder X Y).toSSet.chainComplexMap coeff).hom N (N + 1) =
    ((SimplicialTimeCylinder.productCylinder (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)).chainComplexMap coeff).hom
      N (N + 1) ≫ (SSet.chainComplexMap (modelMap X Y) coeff).f (N + 1) :=
  SSet.Homotopy.chainComplexMap_hom_comm
    (SimplicialTimeCylinder.productCylinder (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))
    (cylinder X Y).toSSet (product_square X Y) coeff N (N + 1)

private theorem cast_hom {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {f g f' g' : C ⟶ D} (H : Homotopy f g) (hf : f = f') (hg : g = g')
    (h : Homotopy f g = Homotopy f' g') (i j : ℕ) : (h.mp H).hom i j = H.hom i j := by
  subst f'; subst g'
  cases h
  rfl

theorem product_original {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] (N : ℕ) :
    ((cylinder (TopCat.of P) (TopCat.of Q)).toSSet.chainComplexMap coeff).hom N (N + 1) =
      (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom N (N + 1) := by
  let H := TopCat.Homotopy.comp (TopCat.Homotopy.refl (OriginalSecondHalfTimeOperation.reorder (P := P) (Q := Q)))
    (AnnularTimeTrim.cylinder (TopCat.of (P × Q)))
  have he : H.h = (cylinder (TopCat.of P) (TopCat.of Q)).h := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  have hp := TimePrismNaturality.prism_post (AnnularTimeTrim.cylinder (TopCat.of (P × Q)))
    (OriginalSecondHalfTimeOperation.reorder (P := P) (Q := Q)) N
  have hc := TimePrismNaturality.prism_congr H (cylinder (TopCat.of P) (TopCat.of Q)) he N
  have h₀ : push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 0) ≫
      push (OriginalSecondHalfTimeOperation.reorder (P := P) (Q := Q)) =
      push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 0) := by
    rw [← push_comp, OriginalSecondHalfTimeOperation.slice_reorder]
  have h₁ : push (AnnularTimeTrim.slice (TopCat.of (P × Q)) 1) ≫
      push (OriginalSecondHalfTimeOperation.reorder (P := P) (Q := Q)) =
      push (OriginalSecondHalfEndpointZero.face (P := P) (Q := Q) 1) := by
    rw [← push_comp, OriginalSecondHalfTimeOperation.slice_reorder]
  dsimp only [OriginalSecondHalfTimeOperation.prism, _root_.id]
  rw [cast_hom (hf := h₀) (hg := h₁)]
  exact (hp.trans hc).symm

end
end Finsler.SingularTimeCylinderMaps
