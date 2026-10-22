module

public import Finsler.Topology.DoubleCapSourceCollar

/-! A cochain restricting to zero on the actual collar kills its
cap after carrier-preserving source approximation. The cochain may be
nonclosed, and the lifted zero holds before any retained output. -/

@[expose] public section
namespace Finsler.SingleCapSourceCollar

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {Y Z : TopCat.{0}} {ι : Type*} (U : ι → Set Z) (A : Set Z)
  (d : ℕ) (ξ : singularCochainGroup (ZMod 2) Z d)
  (hξ : cochainPullback (SupportedCap.subspaceMap Z A) d ξ = 0)
  (f : Y ⟶ Z) (hf : ∀ y, f y ∈ A)

include hξ hf in
theorem approximation_zero (q : ℕ) :
    (push f).f (d + q) ≫ (TauCeti.singularSmallApprox coeff U).f (d + q) ≫
      absoluteChain Z d q (d + q) rfl ξ = 0 := by
  have hzero : (push (SupportedCap.subspaceMap Z A)).f (d + q) ≫
      absoluteChain Z d q (d + q) rfl ξ = 0 :=
    SupportedCap.cap_zero_on_map (SupportedCap.subspaceMap Z A) d q (d + q) rfl ξ hξ
  have hid : push (𝟙 Z) = 𝟙 (chains Z) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 Z)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  let τ := (TopCat.toSSet.map f).app _ σ
  have hσ : (TopCat.toSSet.obj Y).ιChainComplex σ ≫ (push f).f (d + q) =
      (TopCat.toSSet.obj Z).ιChainComplex τ := by
    dsimp only [τ]
    simp only [push, SSet.ι_chainComplexMap_f]
  have hparent : ∀ i, Set.MapsTo (𝟙 Z) (parentFamily.{1} τ i) A := by
    intro i
    change Set.MapsTo (id : Z → Z) (Set.range (Z.toSSetObjEquiv _ τ)) A
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨t, rfl⟩
    exact hf ((Y.toSSetObjEquiv _ σ) t)
  obtain ⟨c, hc⟩ := CarrierSubspaceFactor.push_factor (parentFamily.{1} τ) (𝟙 Z) A hparent
    (approximation_parent U τ)
  have hc' : c ≫ (push (SupportedCap.subspaceMap Z A)).f (d + q) =
      (TopCat.toSSet.obj Z).ιChainComplex τ ≫ (TauCeti.singularSmallApprox coeff U).f (d + q) := by
    simpa only [hid, HomologicalComplex.id_f, Category.comp_id] using hc
  simp only [← Category.assoc, comp_zero]
  rw [hσ, ← hc', Category.assoc, hzero, comp_zero]

include hξ hf in
theorem lift_zero (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j : E ⟶ chains Z)
    (hj : ∀ q, Mono (j.f q)) (c : ∀ q, (small Z U).X (d + q) ⟶ E.X q)
    (hc : ∀ q, c q ≫ j.f q = (inclusion Z U).f (d + q) ≫ absoluteChain Z d q (d + q) rfl ξ)
    (q : ℕ) :
    (push f).f (d + q) ≫
      (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcover).f (d + q) ≫ c q = 0 := by
  haveI : Mono (j.f q) := hj q
  apply (cancel_mono (j.f q)).mp
  rw [zero_comp]
  simp only [Category.assoc]
  rw [hc q, ← Category.assoc
    ((TauCeti.smallSingularRetraction (X := Z) coeff U hU hcover).f (d + q))]
  have hr := congrArg (fun g => g.f (d + q))
    (TauCeti.smallSingularRetraction_comp_ι (X := Z) coeff U hU hcover)
  change (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcover).f (d + q) ≫
      (inclusion Z U).f (d + q) = (TauCeti.singularSmallApprox coeff U).f (d + q) at hr
  rw [hr]
  exact approximation_zero U A d ξ hξ f hf q

end
end Finsler.SingleCapSourceCollar
