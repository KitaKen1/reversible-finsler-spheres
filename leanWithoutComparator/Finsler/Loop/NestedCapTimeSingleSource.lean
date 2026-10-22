module

public import Finsler.Loop.RegradedSingleCapTime
public import Finsler.Loop.CapCupNested
public import Finsler.Loop.LocalizedCapCupComponentSource
public import Finsler.Topology.CutDomainTimePrism

/-! The genuine nested two-cap time has one flat cup source, including
all native degree transports. This places real rotating cap times under
the actual common-input single-source time comparison. -/

@[expose] public section
namespace Finsler.NestedCapTimeSingleSource

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.SphereGeometry Finsler.IntervalSobolev

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set (ClosedInterval × X))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (m p : ℕ)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) U).X ((m + 1) + (p + q)) ⟶ E.X q)
  (hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
    (small (TopCat.of (ClosedInterval × X)) U).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)

def cap := NestedCapHomology.operation (m + 1) p c hc

theorem aligned (q : ℕ) :
    RegradedSingleCapTime.cap X U hU hcU E (m + p) ((m + 1) + p) (by omega) (cap X U E m p c hc) q =
    ClosedCapDegreeTransport.align m p (CutDomainTimePrism.retracted X U hU hcU E m p c) q := by
  dsimp only [RegradedSingleCapTime.cap, cap, NestedCapHomology.operation,
    ClosedCapDegreeTransport.align, CutDomainTimePrism.retracted]
  have ht := LocalizedCapCupComponentSource.transport_f
    (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU)
    (((m + 1) + p) + q) ((m + 1) + (p + q)) (Nat.add_assoc (m + 1) p q)
  rw [← Category.assoc
    ((TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU).f (((m + 1) + p) + q))
    (eqToHom _), ← ht]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (eqToHom _), eqToHom_trans]

variable (C : Set (ClosedInterval × X))
  (φ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) (m + 1))
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) p)
  (hφ : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) C) (m + 1) φ = 0)
  (j : E ⟶ chains (TopCat.of (ClosedInterval × X))) (hj : ∀ q, Mono (j.f q))
  (hi : ∀ q, c q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) U).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap (TopCat.of (ClosedInterval × X)) (m + 1) p q φ ψ)

def cochain := cochainCup (m + 1) p φ ψ

include hφ in
theorem cochain_zero : cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) C) ((m + 1) + p)
    (cochain X m p φ ψ) = 0 := by
  rw [cochain, ← CupOne.cup_comparison]
  exact CupCapOrder.restriction_zero _ _ _ _ rfl _ _ (Or.inl hφ)

include hi in
theorem source (q : ℕ) : (cap X U E m p c hc).component q ≫ j.f q =
    (inclusion (TopCat.of (ClosedInterval × X)) U).f (((m + 1) + p) + q) ≫
      absoluteChain (TopCat.of (ClosedInterval × X)) ((m + 1) + p) q (((m + 1) + p) + q) rfl (cochain X m p φ ψ) := by
  change (eqToHom (congrArg (small (TopCat.of (ClosedInterval × X)) U).X (Nat.add_assoc (m + 1) p q)) ≫ c q) ≫ j.f q = _
  rw [Category.assoc, hi q, cochain, CapCupNested.flat_nested]
  have ht := LocalizedCapCupComponentSource.transport_f (inclusion (TopCat.of (ClosedInterval × X)) U)
    (((m + 1) + p) + q) ((m + 1) + (p + q)) (Nat.add_assoc (m + 1) p q)
  simpa only [Category.assoc] using congrArg (fun z => z ≫
    PartialDoubleCap.cap (TopCat.of (ClosedInterval × X)) (m + 1) p q φ ψ) ht

variable (h₀ : ∀ x, ((0 : ClosedInterval), x) ∈ C) (h₁ : ∀ x, ((1 : ClosedInterval), x) ∈ C)

theorem time_component (q : ℕ) :
    (CutDomainTimePrism.operation X U hU hcU E m p c C φ ψ hφ j hj hi hc h₀ h₁).component q =
    (RegradedSingleCapTime.operation X U hU hcU E (m + p) ((m + 1) + p) (by omega)
      (cap X U E m p c hc) C (cochain X m p φ ψ) (cochain_zero X m p C φ ψ hφ) j hj
      (source X U E m p c hc φ ψ j hi) h₀ h₁).component q := by
  change ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).hom ((m + p) + q) (((m + p) + q) + 1) ≫
    ClosedCapDegreeTransport.align m p (CutDomainTimePrism.retracted X U hU hcU E m p c) q =
    ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).hom ((m + p) + q) (((m + p) + q) + 1) ≫
      RegradedSingleCapTime.cap X U hU hcU E (m + p) ((m + 1) + p) (by omega) (cap X U E m p c hc) q
  rw [aligned]

theorem time_homology (q : ℕ) :
    (CutDomainTimePrism.operation X U hU hcU E m p c C φ ψ hφ j hj hi hc h₀ h₁).homology q =
    (RegradedSingleCapTime.operation X U hU hcU E (m + p) ((m + 1) + p) (by omega)
      (cap X U E m p c hc) C (cochain X m p φ ψ) (cochain_zero X m p C φ ψ hφ) j hj
      (source X U E m p c hc φ ψ j hi) h₀ h₁).homology q :=
  DegreeLoweringHomology.Map.homology_eq_of_components _ _
    (time_component X U hU hcU E m p c hc C φ ψ hφ j hj hi h₀ h₁) q

end
end Finsler.NestedCapTimeSingleSource
