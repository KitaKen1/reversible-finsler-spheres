module

public import Finsler.Topology.DoubleCapSourceCollar
public import Finsler.Topology.ClosedCapDegreeTransport
public import Finsler.Topology.AnnularTimeTrim
public import Finsler.Topology.TimePrismDescent

/-! Descend the time prism already to the actual cut-domain lift of
the two caps. Endpoint vanishing is proved before applying any retained
map, so every later bounded retained deformation may be postcomposed. -/

@[expose] public section
namespace Finsler.CutDomainTimePrism

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

private theorem transport_f {K D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (g : K ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg K.X h) ≫ g.f j = g.f i ≫ eqToHom (congrArg D.X h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set (ClosedInterval × X))
  (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (m p : ℕ)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) U).X ((m + 1) + (p + q)) ⟶ E.X q)

def retracted (q : ℕ) : (chains (TopCat.of (ClosedInterval × X))).X ((m + 1) + (p + q)) ⟶ E.X q :=
  (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover).f
    ((m + 1) + (p + q)) ≫ c q

theorem retracted_comm
    (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
      (small (TopCat.of (ClosedInterval × X)) U).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q) (q : ℕ) :
    retracted X U hU hcover E m p c (q + 1) ≫ E.d (q + 1) q =
      (chains (TopCat.of (ClosedInterval × X))).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ retracted X U hU hcover E m p c q := by
  dsimp only [retracted]
  rw [Category.assoc, hc q, ← Category.assoc,
    (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover).comm,
    Category.assoc]

variable (A : Set (ClosedInterval × X))
  (φ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) (m + 1))
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) p)
  (hφ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) A) (m + 1) φ = 0)
  (j : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hj : ∀ q, Mono (j.f q))
  (hi : ∀ q, c q ≫ j.f q = (inclusion (TopCat.of (ClosedInterval × X)) U).f ((m + 1) + (p + q)) ≫
    PartialDoubleCap.cap (TopCat.of (ClosedInterval × X)) (m + 1) p q φ ψ)

include hφ hj hi

theorem endpoint_zero (t : ClosedInterval) (ht : ∀ x, (t, x) ∈ A) (q : ℕ) :
    (push (AnnularTimeTrim.slice X t)).f ((m + p) + q + 1) ≫
      ClosedCapDegreeTransport.align m p (retracted X U hU hcover E m p c) q = 0 := by
  have hz := DoubleCapSourceCollar.lift_zero (Y := X) (Z := TopCat.of (ClosedInterval × X))
    U A (m + 1) p φ ψ hφ (AnnularTimeTrim.slice X t) ht hU hcover E j hj c hi q
  have he := transport_f (push (AnnularTimeTrim.slice X t)) ((m + p) + q + 1)
    ((m + 1) + (p + q)) (by omega)
  dsimp only [ClosedCapDegreeTransport.align]
  rw [← Category.assoc, ← he, Category.assoc]
  change eqToHom _ ≫
    ((push (AnnularTimeTrim.slice X t)).f ((m + 1) + (p + q)) ≫
      (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcover).f
        ((m + 1) + (p + q)) ≫ c q) = 0
  rw [hz, comp_zero]

def operation
    (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
      (small (TopCat.of (ClosedInterval × X)) U).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)
    (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ A) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ A) :
    DegreeLoweringHomology.Map (chains X) E (m + p) :=
  TimePrismDescent.operation ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff) (m + p)
    (ClosedCapDegreeTransport.align m p (retracted X U hU hcover E m p c))
    (ClosedCapDegreeTransport.align_comm m p (retracted X U hU hcover E m p c)
      (retracted_comm X U hU hcover E m p c hc))
    (endpoint_zero X U hU hcover E m p c A φ ψ hφ j hj hi 0 h₀)
    (endpoint_zero X U hU hcover E m p c A φ ψ hφ j hj hi 1 h₁)

end
end Finsler.CutDomainTimePrism
