module

public import Finsler.Topology.PartialDoubleCapDomainFiltered
public import Finsler.Topology.CarrierSubspaceFactor

/-! A collar where the first cochain vanishes kills the actual two-cap
operation after arbitrary source approximation, already in the cut
domain. This supplies endpoint vanishing before any retained output
or retained-output deformation is applied. -/

@[expose] public section
namespace Finsler.DoubleCapSourceCollar

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

variable {Y Z : TopCat.{0}} {ι : Type*} (U : ι → Set Z) (A : Set Z)
  (k p : ℕ) (φ : singularCochainGroup (ZMod 2) Z k) (ψ : singularCochainGroup (ZMod 2) Z p)
  (hφ : cochainPullback (SupportedCap.subspaceMap Z A) k φ = 0)
  (f : Y ⟶ Z) (hf : ∀ y, f y ∈ A)

include hφ hf

theorem approximation_zero (q : ℕ) :
    (push f).f (k + (p + q)) ≫ (TauCeti.singularSmallApprox coeff U).f (k + (p + q)) ≫
      PartialDoubleCap.cap Z k p q φ ψ = 0 := by
  let N := k + (p + q)
  have hfirst : (push (SupportedCap.subspaceMap Z A)).f N ≫
      RelativeCapAssociativity.absoluteChain Z k (p + q) N rfl φ = 0 :=
    SupportedCap.cap_zero_on_map (SupportedCap.subspaceMap Z A) k (p + q) N rfl φ hφ
  have hzero : (push (SupportedCap.subspaceMap Z A)).f N ≫ PartialDoubleCap.cap Z k p q φ ψ = 0 := by
    rw [PartialDoubleCap.cap, ← Category.assoc, hfirst, zero_comp]
  have hid : push (𝟙 Z) = 𝟙 (chains Z) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 Z)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj Y) (R := coeff)
  intro σ
  let τ := (TopCat.toSSet.map f).app _ σ
  have hσ : (TopCat.toSSet.obj Y).ιChainComplex σ ≫ (push f).f N =
      (TopCat.toSSet.obj Z).ιChainComplex τ := by
    dsimp only [N, τ]
    simp only [push, SSet.ι_chainComplexMap_f]
  have hparent : ∀ i, Set.MapsTo (𝟙 Z) (parentFamily.{1} τ i) A := by
    intro i
    change Set.MapsTo (id : Z → Z) (Set.range (Z.toSSetObjEquiv _ τ)) A
    rw [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app]
    rintro _ ⟨t, rfl⟩
    exact hf ((Y.toSSetObjEquiv _ σ) t)
  obtain ⟨c, hc⟩ := CarrierSubspaceFactor.push_factor (parentFamily.{1} τ) (𝟙 Z) A hparent
    (approximation_parent U τ)
  have hc' : c ≫ (push (SupportedCap.subspaceMap Z A)).f N =
      (TopCat.toSSet.obj Z).ιChainComplex τ ≫ (TauCeti.singularSmallApprox coeff U).f N := by
    simpa only [hid, HomologicalComplex.id_f, Category.comp_id] using hc
  simp only [← Category.assoc, comp_zero]
  rw [hσ, ← hc', Category.assoc, hzero, comp_zero]

theorem lift_zero (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (j : E ⟶ chains Z)
    (hj : ∀ q, Mono (j.f q))
    (c : ∀ q, (small Z U).X (k + (p + q)) ⟶ E.X q)
    (hc : ∀ q, c q ≫ j.f q = (inclusion Z U).f (k + (p + q)) ≫ PartialDoubleCap.cap Z k p q φ ψ)
    (q : ℕ) :
    (push f).f (k + (p + q)) ≫
      (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcover).f (k + (p + q)) ≫ c q = 0 := by
  haveI : Mono (j.f q) := hj q
  apply (cancel_mono (j.f q)).mp
  rw [zero_comp]
  simp only [Category.assoc]
  rw [hc q, ← Category.assoc
    ((TauCeti.smallSingularRetraction (X := Z) coeff U hU hcover).f (k + (p + q)))]
  have hr := congrArg (fun g => g.f (k + (p + q)))
    (TauCeti.smallSingularRetraction_comp_ι (X := Z) coeff U hU hcover)
  change (TauCeti.smallSingularRetraction (X := Z) coeff U hU hcover).f (k + (p + q)) ≫
      (inclusion Z U).f (k + (p + q)) =
        (TauCeti.singularSmallApprox coeff U).f (k + (p + q)) at hr
  rw [hr]
  exact approximation_zero U A k p φ ψ hφ f hf q

end
end Finsler.DoubleCapSourceCollar
