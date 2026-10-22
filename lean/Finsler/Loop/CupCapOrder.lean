module

public import Finsler.Topology.CupOne
public import Finsler.Topology.SupportedCapNaturality

/-! Exact cup-cap associativity and support for the genuine cups
appearing in the cup-one formula, with all degree transports explicit. -/

@[expose] public section
namespace Finsler.CupCapOrder

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_cup (X : TopCat.{0}) (p r d q : ℕ) (hd : p + r = d)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X r) :
    absoluteChain X p (r + q) (d + q) (by omega) φ ≫ absoluteChain X r q (r + q) rfl ψ =
      absoluteChain X d q (d + q) rfl (CupOne.cup X p r d hd φ ψ) := by
  subst d
  exact TopCat.capChain_alexanderWhitneyDiagonal_assoc X (ZMod 2) (by omega) rfl φ ψ

theorem naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (p r d : ℕ) (hd : p + r = d)
    (φ : singularCochainGroup (ZMod 2) Y p) (ψ : singularCochainGroup (ZMod 2) Y r) :
    cochainPullback f d (CupOne.cup Y p r d hd φ ψ) =
      CupOne.cup X p r d hd (cochainPullback f p φ) (cochainPullback f r ψ) := by
  subst d
  rw [CupOne.cup_comparison, CupOne.cup_comparison, cochainCup_naturality]

theorem restriction_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (p r d : ℕ) (hd : p + r = d)
    (φ : singularCochainGroup (ZMod 2) Y p) (ψ : singularCochainGroup (ZMod 2) Y r)
    (hz : cochainPullback f p φ = 0 ∨ cochainPullback f r ψ = 0) :
    cochainPullback f d (CupOne.cup Y p r d hd φ ψ) = 0 := by
  subst d
  rw [CupOne.cup_comparison, cochainCup_naturality]
  rcases hz with h | h
  · rw [h, cochainCup_zero_left]
  · rw [h, cochainCup_zero_right]

theorem closed (X : TopCat.{0}) (p r d : ℕ) (hd : p + r = d)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) X r)
    (hφ : cochainCoboundary (ZMod 2) X p φ = 0)
    (hψ : cochainCoboundary (ZMod 2) X r ψ = 0) :
    cochainCoboundary (ZMod 2) X d (CupOne.cup X p r d hd φ ψ) = 0 := by
  subst d
  rw [CupOne.cup_comparison]
  exact cochainCupZMod2_respects_cocycles p r φ ψ hφ hψ

end
end Finsler.CupCapOrder
