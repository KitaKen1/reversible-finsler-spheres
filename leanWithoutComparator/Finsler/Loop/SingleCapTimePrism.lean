module

public import Finsler.Loop.SingleCapSourceCollar
public import Finsler.Loop.NestedCapUnpack
public import Finsler.Topology.ClosedCapDegreeTransport
public import Finsler.Topology.AnnularTimeTrim
public import Finsler.Topology.TimePrismDescent

/-! Full-time descent for a real single cap lift with local closure.
The actual source formula and collar zero supply both endpoint zeros
inside its original target, before any retained output. -/

@[expose] public section
namespace Finsler.SingleCapTimePrism

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem transport_f {K D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg K.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set (ClosedInterval × X))
  (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
  (c : DegreeLoweringHomology.Map (small (TopCat.of (ClosedInterval × X)) U) E (d + 1))

def retracted : DegreeLoweringHomology.Map (chains (TopCat.of (ClosedInterval × X))) E (d + 1) :=
  c.pre (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover)

def aligned (q : ℕ) : (chains (TopCat.of (ClosedInterval × X))).X (d + q + 1) ⟶ E.X q :=
  ClosedCapDegreeTransport.align d 0
    (NestedCapUnpack.component (d + 1) 0 (retracted X U hU hcover E d c)) q

theorem aligned_normal (q : ℕ) :
    aligned X U hU hcover E d c q =
    eqToHom (congrArg (chains (TopCat.of (ClosedInterval × X))).X
      (show d + q + 1 = (d + 1) + q by omega)) ≫
      (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover).f ((d + 1) + q) ≫
        c.component q := by
  dsimp only [aligned, ClosedCapDegreeTransport.align, NestedCapUnpack.component, retracted,
    DegreeLoweringHomology.Map.pre]
  rw [← Category.assoc, eqToHom_trans]

theorem aligned_comm (q : ℕ) :
    aligned X U hU hcover E d c (q + 1) ≫ E.d (q + 1) q =
      (chains (TopCat.of (ClosedInterval × X))).d (d + q + 2) (d + q + 1) ≫ aligned X U hU hcover E d c q :=
  ClosedCapDegreeTransport.align_comm d 0 _
    (NestedCapUnpack.comm (d + 1) 0 (retracted X U hU hcover E d c)) q

variable (A : Set (ClosedInterval × X))
  (ξ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) (d + 1))
  (hξ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) A) (d + 1) ξ = 0)
  (j : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hj : ∀ q, Mono (j.f q))
  (hc : ∀ q, c.component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) U).f ((d + 1) + q) ≫
      absoluteChain (TopCat.of (ClosedInterval × X)) (d + 1) q ((d + 1) + q) rfl ξ)

include hξ hj hc in
theorem endpoint_zero (t : ClosedInterval) (ht : ∀ x, (t, x) ∈ A) (q : ℕ) :
    (push (AnnularTimeTrim.slice X t)).f (d + q + 1) ≫ aligned X U hU hcover E d c q = 0 := by
  have hz : (push (AnnularTimeTrim.slice X t)).f ((d + 1) + q) ≫
      (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover).f ((d + 1) + q) ≫
        c.component q = 0 :=
    SingleCapSourceCollar.lift_zero (Y := X) (Z := TopCat.of (ClosedInterval × X)) U A (d + 1) ξ hξ
      (AnnularTimeTrim.slice X t) ht hU hcover E j hj c.component hc q
  have he := transport_f (push (AnnularTimeTrim.slice X t)) (d + q + 1) ((d + 1) + q) (by omega)
  rw [aligned_normal, ← Category.assoc, ← he, Category.assoc]
  change eqToHom _ ≫ ((push (AnnularTimeTrim.slice X t)).f ((d + 1) + q) ≫
    (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover).f ((d + 1) + q) ≫
      c.component q) = 0
  rw [hz, comp_zero]

def operation (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A) :
    DegreeLoweringHomology.Map (chains X) E d :=
  TimePrismDescent.operation ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) d
    (aligned X U hU hcover E d c) (aligned_comm X U hU hcover E d c)
    (endpoint_zero X U hU hcover E d c A ξ hξ j hj hc 0 h₀)
    (endpoint_zero X U hU hcover E d c A ξ hξ j hj hc 1 h₁)

theorem component_normal (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A)
    (q : ℕ) :
    (operation X U hU hcover E d c A ξ hξ j hj hc h₀ h₁).component q =
      AnnularTimeTrim.prism X (d + q) ≫
        eqToHom (congrArg (chains (TopCat.of (ClosedInterval × X))).X
          (show d + q + 1 = (d + 1) + q by omega)) ≫
          (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover).f ((d + 1) + q) ≫
            c.component q := by
  change AnnularTimeTrim.prism X (d + q) ≫ aligned X U hU hcover E d c q = _
  rw [aligned_normal]

end
end Finsler.SingleCapTimePrism
