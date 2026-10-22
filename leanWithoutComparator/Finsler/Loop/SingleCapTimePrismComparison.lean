module

public import Finsler.Loop.SingleCapTimeRetraction

/-! Actual time operations constructed from two closed cap lifts
agree under a real relative cover refinement in the identical target. -/

@[expose] public section
namespace Finsler.SingleCapTimePrismComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) {ι κ : Type*}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set (ClosedInterval × X))
  (r : ι → κ) (href : ∀ i, U i ⊆ V (r i))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
  (cU : DegreeLoweringHomology.Map (small (TopCat.of (ClosedInterval × X)) U) E (d + 1))
  (cV : DegreeLoweringHomology.Map (small (TopCat.of (ClosedInterval × X)) V) E (d + 1))
  (A : Set (ClosedInterval × X))
  (ξ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) (d + 1))
  (hξ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) A) (d + 1) ξ = 0)
  (j : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hj : ∀ q, Mono (j.f q))
  (hsU : ∀ q, cU.component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) U).f ((d + 1) + q) ≫
      RelativeCapAssociativity.absoluteChain (TopCat.of (ClosedInterval × X)) (d + 1) q ((d + 1) + q) rfl ξ)
  (hsV : ∀ q, cV.component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) V).f ((d + 1) + q) ≫
      RelativeCapAssociativity.absoluteChain (TopCat.of (ClosedInterval × X)) (d + 1) q ((d + 1) + q) rfl ξ)
  (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A)

theorem homology_eq
    (hc : ∀ q, (SmallRefinementComparison.refinement (X := TopCat.of (ClosedInterval × X)) U V r href).f ((d + 1) + q) ≫
      cV.component q = cU.component q) (q : ℕ) :
    (SingleCapTimePrism.operation X V hV hcV E d cV A ξ hξ j hj hsV h₀ h₁).homology q =
      (SingleCapTimePrism.operation X U hU hcU E d cU A ξ hξ j hj hsU h₀ h₁).homology q := by
  apply SingleCapTimeRetraction.homology_eq (Z := TopCat.of (ClosedInterval × X)) U V r href hU hcU hV hcV X
    (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) E d cU cV hc
    (SingleCapTimePrism.operation X V hV hcV E d cV A ξ hξ j hj hsV h₀ h₁)
    (SingleCapTimePrism.operation X U hU hcU E d cU A ξ hξ j hj hsU h₀ h₁)
  · exact SingleCapTimePrism.component_normal X V hV hcV E d cV A ξ hξ j hj hsV h₀ h₁
  · exact SingleCapTimePrism.component_normal X U hU hcU E d cU A ξ hξ j hj hsU h₀ h₁

end
end Finsler.SingleCapTimePrismComparison
