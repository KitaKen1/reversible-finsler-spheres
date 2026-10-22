module

public import Finsler.Loop.SingleCapTimePrism

/-! Genuine single-cap time descent with an explicit equality between
the geometric cap degree and the native time degree plus one. -/

@[expose] public section
namespace Finsler.RegradedSingleCapTime

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set (ClosedInterval × X))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d D : ℕ) (hD : d + 1 = D)
  (c : DegreeLoweringHomology.Map (small (TopCat.of (ClosedInterval × X)) U) E D)

def cap (q : ℕ) : (chains (TopCat.of (ClosedInterval × X))).X (d + q + 1) ⟶ E.X q :=
  eqToHom (congrArg (chains (TopCat.of (ClosedInterval × X))).X (show d + q + 1 = D + q by omega)) ≫
    (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU).f (D + q) ≫ c.component q

theorem cap_comm (q : ℕ) :
    cap X U hU hcU E d D hD c (q + 1) ≫ E.d (q + 1) q =
    (chains (TopCat.of (ClosedInterval × X))).d (d + q + 2) (d + q + 1) ≫ cap X U hU hcU E d D hD c q := by
  subst D
  simpa only [cap, SingleCapTimePrism.aligned_normal] using
    SingleCapTimePrism.aligned_comm X U hU hcU E d c q

variable (A : Set (ClosedInterval × X))
  (ξ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) D)
  (hξ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) A) D ξ = 0)
  (j : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hj : ∀ q, Mono (j.f q))
  (hc : ∀ q, c.component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) U).f (D + q) ≫
      absoluteChain (TopCat.of (ClosedInterval × X)) D q (D + q) rfl ξ)

include hξ hj hc in
theorem endpoint_zero (t : ClosedInterval) (ht : ∀ x, (t, x) ∈ A) (q : ℕ) :
    (push (AnnularTimeTrim.slice X t)).f (d + q + 1) ≫ cap X U hU hcU E d D hD c q = 0 := by
  subst D
  simpa only [cap, SingleCapTimePrism.aligned_normal] using
    SingleCapTimePrism.endpoint_zero X U hU hcU E d c A ξ hξ j hj hc t ht q

def operation (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A) :
    DegreeLoweringHomology.Map (chains X) E d :=
  TimePrismDescent.operation ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) d
    (cap X U hU hcU E d D hD c) (cap_comm X U hU hcU E d D hD c)
    (endpoint_zero X U hU hcU E d D hD c A ξ hξ j hj hc 0 h₀)
    (endpoint_zero X U hU hcU E d D hD c A ξ hξ j hj hc 1 h₁)

theorem component_normal (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A)
    (q : ℕ) :
    (operation X U hU hcU E d D hD c A ξ hξ j hj hc h₀ h₁).component q =
    AnnularTimeTrim.prism X (d + q) ≫
      eqToHom (congrArg (chains (TopCat.of (ClosedInterval × X))).X (show d + q + 1 = D + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU).f (D + q) ≫ c.component q := rfl

end
end Finsler.RegradedSingleCapTime
