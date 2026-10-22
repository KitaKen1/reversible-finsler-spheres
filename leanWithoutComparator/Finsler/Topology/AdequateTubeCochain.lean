module

public import Finsler.Topology.TubeCochainExtension
public import Finsler.Topology.CarrierCochainZero

/-! The supported small-chain cochain calculus with a genuinely partial
tested map. The extension is not assumed globally closed. Both its cup
coboundary and the cup-one error cap vanish on every chain carried by the
far/tube cover, including any comparison prism with that carrier bound. -/

@[expose] public section
namespace Finsler.AdequateTubeCochain

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (X : TopCat.{0}) (A O : Set X) (p q : ℕ)
  (φ : singularCochainGroup (ZMod 2) X p)
  (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
  (hA : cochainPullback (SupportedCap.subspaceMap X A) p φ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of O) q)
  (hψ : cochainCoboundary (ZMod 2) (TopCat.of O) q ψ = 0)

def gamma : singularCochainGroup (ZMod 2) X (p + q) :=
  cochainCup p q φ (TubeCochainExtension.extend X O q ψ)

include hφ hA hψ in
theorem boundary_parts_zero : ∀ b : Bool,
    cochainPullback (SupportedCap.subspaceMap X (SupportedCap.cover X A O b)) (p + q + 1)
      (cochainCoboundary (ZMod 2) X (p + q) (gamma X O p q φ ψ)) = 0 := by
  intro b
  cases b with
  | false =>
    have hz : cochainPullback (SupportedCap.subspaceMap X A) (p + q) (gamma X O p q φ ψ) = 0 := by
      rw [gamma, cochainCup_naturality, hA, cochainCup_zero_left]
    have he := ConcreteCategory.congr_hom
      ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X A).op).comm (p + q) (p + q + 1))
      (gamma X O p q φ ψ)
    change cochainCoboundary (ZMod 2) (TopCat.of A) (p + q)
      (cochainPullback (SupportedCap.subspaceMap X A) (p + q) (gamma X O p q φ ψ)) =
      cochainPullback (SupportedCap.subspaceMap X A) (p + q + 1)
        (cochainCoboundary (ZMod 2) X (p + q) (gamma X O p q φ ψ)) at he
    rw [hz] at he
    have hz0 : cochainCoboundary (ZMod 2) (TopCat.of A) (p + q) 0 = 0 := by
      change ((cochainCxZMod2 (TopCat.of A)).d (p + q) (p + q + 1)).hom 0 = 0
      exact map_zero _
    exact he.symm.trans hz0
  | true => exact TubeCochainExtension.cup_local_closed X O p q φ hφ ψ hψ

include hφ hA hψ in
theorem boundary_cap_zero (t m : ℕ) (h : (p + q + 1) + t = m)
    {c : coeff ⟶ (chains X).X m}
    (hc : c ∈ supported X (SupportedCap.cover X A O) m) :
    c ≫ absoluteChain X (p + q + 1) t m h
      (cochainCoboundary (ZMod 2) X (p + q) (gamma X O p q φ ψ)) = 0 :=
  CarrierCochainZero.cap_zero (SupportedCap.cover X A O) (p + q + 1) t m h _
    (boundary_parts_zero X A O p q φ hφ hA ψ hψ) hc

include hφ hA hψ in
theorem cupOne_error_parts_zero (r m : ℕ) (h : r + (p + q + 1) = m + 1)
    (σ : singularCochainGroup (ZMod 2) X r) : ∀ b : Bool,
    cochainPullback (SupportedCap.subspaceMap X (SupportedCap.cover X A O b)) m
      (CupOne.cupOne X r (p + q + 1) m h σ
        (cochainCoboundary (ZMod 2) X (p + q) (gamma X O p q φ ψ))) = 0 := by
  intro b
  exact CupOne.restriction_zero
    (SupportedCap.subspaceMap X (SupportedCap.cover X A O b)) r (p + q + 1) m h σ _
    (Or.inr (boundary_parts_zero X A O p q φ hφ hA ψ hψ b))

include hφ hA hψ in
theorem cupOne_error_cap_zero (r m t k : ℕ) (h : r + (p + q + 1) = m + 1) (hk : m + t = k)
    (σ : singularCochainGroup (ZMod 2) X r)
    {c : coeff ⟶ (chains X).X k}
    (hc : c ∈ supported X (SupportedCap.cover X A O) k) :
    c ≫ absoluteChain X m t k hk
      (CupOne.cupOne X r (p + q + 1) m h σ
        (cochainCoboundary (ZMod 2) X (p + q) (gamma X O p q φ ψ))) = 0 :=
  CarrierCochainZero.cap_zero (SupportedCap.cover X A O) m t k hk _
    (cupOne_error_parts_zero X A O p q φ hφ hA ψ hψ r m h σ) hc

end
end Finsler.AdequateTubeCochain
