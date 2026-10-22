module

public import Finsler.Loop.SupportedCapTestOrderCoupling
public import Finsler.Loop.SupportedCupOneCapCorrection
public import Finsler.Topology.RelativeCapDual

/-! ACTUAL supported-cap projection/order formula, with an explicit
primitive = original subdivision prism PLUS supported cup-one cap.
Moving a closed absolute test across the actual supported Thom cap
changes the full scalar cochain by precisely this boundary. Every
independent carrier on which the actual near-output vanishes keeps
literal primitiveZERO. No naturality of the chosen retraction is assumed. -/
@[expose] public section
namespace Finsler.SupportedCapTestOrder
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

theorem cut_carrier_zero_at_degree (X : TopCat.{0}) (A B C : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
    (hψ : cochainPullback (restriction (SupportedCap.subspaceMap X C)
      ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) N (SupportedCap.cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0 := by
  subst N
  exact SupportedCutCochainCarrierZero.subspace_cochain_zero X A B C hA hB hc p q θ hs ψ hψ

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (a b q : ℕ)
  (α : singularCochainGroup (ZMod 2) X a) (θ : singularCochainGroup (ZMod 2) X (b + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (b + 1) θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

theorem left_coupled : SupportedCupOneCapCorrection.left X A B hA hB hc a b q α θ hs ψ =
    SupportedCapTestOrderCoupling.beforeCoupled X A B hA hB hc a b q α θ hs ψ := rfl

theorem right_coupled : SupportedCupOneCapCorrection.right X A B hA hB hc a b q α θ hs ψ =
    SupportedCapTestOrderCoupling.afterCoupled X A B hA hB hc a b q α θ hs ψ := rfl

def primitive : singularCochainGroup (ZMod 2) X ((a + b) + q) :=
  SupportedCapTestOrderCoupling.primitive X A B hA hB hc a b q α θ hs ψ +
    SupportedCupOneCapCorrection.correction X A B hA hB hc a b q α θ hs ψ

theorem boundary (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (primitive X A B hA hB hc a b q α θ hs ψ) =
      SupportedCapTestOrderCoupling.before X A B hA hB hc a b q α θ hs ψ -
        SupportedCapTestOrderCoupling.after X A B hA hB hc a b q α θ hs ψ := by
  change ((cochainCxZMod2 X).d _ _).hom (_ + _) = _
  rw [map_add]
  change cochainCoboundary (ZMod 2) X ((a + b) + q)
      (SupportedCapTestOrderCoupling.primitive X A B hA hB hc a b q α θ hs ψ) +
    cochainCoboundary (ZMod 2) X ((a + b) + q)
      (SupportedCupOneCapCorrection.correction X A B hA hB hc a b q α θ hs ψ) = _
  rw [SupportedCapTestOrderCoupling.primitive_boundary X A B hA hB hc a b q α θ hs ψ hα hθ hψ,
    SupportedCupOneCapCorrection.correction_boundary X A B hA hB hc a b q α θ hs ψ hα hθ hψ,
    left_coupled, right_coupled, ← SupportedCapTestOrderCoupling.after_exact]
  unfold SupportedCapTestOrderCoupling.difference
  abel

theorem class_eq (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    CochainClass.classOf (cochainCxZMod2 X) _
      (SupportedCapTestOrderCoupling.before X A B hA hB hc a b q α θ hs ψ)
      (SupportedCapTestOrderCoupling.before_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ) =
    CochainClass.classOf (cochainCxZMod2 X) _
      (SupportedCapTestOrderCoupling.after X A B hA hB hc a b q α θ hs ψ)
      (SupportedCapTestOrderCoupling.after_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ) := by
  apply RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 X) ((a + b) + q) _
    (primitive X A B hA hB hc a b q α θ hs ψ)
  change _ - _ = cochainCoboundary (ZMod 2) X _ (primitive X A B hA hB hc a b q α θ hs ψ)
  exact (boundary X A B hA hB hc a b q α θ hs ψ hα hθ hψ).symm

theorem absolute_pullback_zero {Y : TopCat.{0}} (f : Y ⟶ X) (p q N : ℕ) (hN : p + q = N)
    (μ : singularCochainGroup (ZMod 2) X p) (ν : singularCochainGroup (ZMod 2) X q)
    (hν : cochainPullback f q ν = 0) :
    cochainPullback f N (absoluteChain X p q N hN μ ≫ ν) = 0 := by
  subst N
  rw [RelativeCapDual.absolute_chain_dual, cochainCup_naturality, hν, cochainCup_zero_right]

theorem before_carrier_zero (C : Set X)
    (hψC : cochainPullback (restriction (SupportedCap.subspaceMap X C)
      ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) _
      (SupportedCapTestOrderCoupling.before X A B hA hB hc a b q α θ hs ψ) = 0 := by
  have hz := SupportedCutCochainCarrierZero.subspace_cochain_zero X A B C hA hB hc (b + 1) q θ hs ψ hψC
  exact absolute_pullback_zero X (SupportedCap.subspaceMap X C) a ((b + 1) + q) _ (by omega) α _ hz

theorem coupled_carrier_zero (C : Set X)
    (hψC : cochainPullback (restriction (SupportedCap.subspaceMap X C)
      ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) _
      (SupportedCapTestOrderCoupling.beforeCoupled X A B hA hB hc a b q α θ hs ψ) = 0 :=
  cut_carrier_zero_at_degree X A B C hA hB hc (a + (b + 1)) q ((a + b) + q + 1) (by omega) _
    (SupportedCapTestOrderLocal.before_supported X A a (b + 1) α θ hs) ψ hψC

theorem primitive_carrier_zero (C : Set X)
    (hψC : cochainPullback (restriction (SupportedCap.subspaceMap X C)
      ((SupportedCap.subspaceMap X C) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) _ (primitive X A B hA hB hc a b q α θ hs ψ) = 0 := by
  have hd : cochainPullback (SupportedCap.subspaceMap X C) _
      (SupportedCapTestOrderCoupling.difference X A B hA hB hc a b q α θ hs ψ) = 0 := by
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X C).op).f _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((before_carrier_zero X A B hA hB hc a b q α θ hs ψ C hψC).trans
      (coupled_carrier_zero X A B hA hB hc a b q α θ hs ψ C hψC).symm)
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X C).op).f _).hom (_ + _) = 0
  rw [map_add]
  change cochainPullback _ _ (SupportedCapTestOrderCoupling.primitive X A B hA hB hc a b q α θ hs ψ) +
    cochainPullback _ _ (SupportedCupOneCapCorrection.correction X A B hA hB hc a b q α θ hs ψ) = 0
  rw [SupportedCapTestOrderCoupling.primitive_carrier_zero X A B hA hB hc a b q α θ hs ψ C hd,
    SupportedCupOneCapCorrection.correction_carrier_zero X A B hA hB hc a b q α θ hs ψ C hψC, add_zero]

end
end Finsler.SupportedCapTestOrder
