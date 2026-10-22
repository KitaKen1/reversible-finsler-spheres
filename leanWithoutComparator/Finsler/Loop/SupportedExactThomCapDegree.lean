module

public import Finsler.Loop.SupportedExactThomCap
public import Finsler.Loop.SupportedCapPullbackClass

/-! Evaluate the exact supported Thom cap in its ORIGINAL canonical
input degree (p+1)+q. Explicit degree transport of the real primitive
boundary makes this compatible with the old supported-cap API. -/
@[expose] public section
namespace Finsler.SupportedExactThomCapDegree
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (p q : ℕ) (κ : singularCochainGroup (ZMod 2) X p)
  (hs : cochainPullback (SupportedCap.subspaceMap X A) p κ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)
  (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0)

private theorem cast_cut (a b i j : ℕ) (hij : i = j) (hab : a + b = i)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : cochainPullback (SupportedCap.subspaceMap X A) a φ = 0)
    (η : singularCochainGroup (ZMod 2) (TopCat.of B) b) :
    CochainClass.cast (cochainCxZMod2 X) hij (SupportedCap.cut X A B hA hB hc a b i hab φ hφ ≫ η) =
      SupportedCap.cut X A B hA hB hc a b j (hab.trans hij) φ hφ ≫ η := by
  subst j
  rfl

def cochain : singularCochainGroup (ZMod 2) X ((p + 1) + q) :=
  SupportedCap.cut X A B hA hB hc (p + 1) q ((p + 1) + q) rfl
    (cochainCoboundary (ZMod 2) X p κ) (SupportedExactThomCap.coboundary_supported X A p κ hs) ≫ ψ

include hψ in
theorem cochain_closed : cochainCoboundary (ZMod 2) X ((p + 1) + q) (cochain X A B hA hB hc p q κ hs ψ) = 0 :=
  DegreeLoweringCochainPullback.closed
    (SupportedCapHomology.operation X A B hA hB hc (p + 1) (cochainCoboundary (ZMod 2) X p κ)
      (SupportedExactThomCap.coboundary_supported X A p κ hs)
      (CochainClass.closed_boundary (cochainCxZMod2 X) p (p + 1) κ)) q ψ hψ

include hψ in
theorem boundary_cast :
    CochainClass.cast (cochainCxZMod2 X) (show (p + q) + 1 = (p + 1) + q by omega)
      (cochainCoboundary (ZMod 2) X (p + q) (SupportedExactThomCap.correction X A B hA hB hc p κ hs q ψ)) =
      cochain X A B hA hB hc p q κ hs ψ := by
  rw [SupportedExactThomCap.correction_boundary X A B hA hB hc p κ hs q ψ hψ]
  unfold SupportedExactThomCap.cochain
  exact cast_cut X A B hA hB hc (p + 1) q (p + q + 1) ((p + 1) + q) (by omega) (by omega) _ _ ψ

include hψ in
theorem cochain_class_zero :
    CochainClass.classOf (cochainCxZMod2 X) ((p + 1) + q) (cochain X A B hA hB hc p q κ hs ψ)
      (cochain_closed X A B hA hB hc p q κ hs ψ hψ) = 0 := by
  have he := boundary_cast X A B hA hB hc p q κ hs ψ hψ
  have hz : ((cochainCxZMod2 X).d ((p + 1) + q) (((p + 1) + q) + 1)).hom
      (CochainClass.cast (cochainCxZMod2 X) (show (p + q) + 1 = (p + 1) + q by omega)
        (cochainCoboundary (ZMod 2) X (p + q) (SupportedExactThomCap.correction X A B hA hB hc p κ hs q ψ))) = 0 := by
    rw [he]
    exact cochain_closed X A B hA hB hc p q κ hs ψ hψ
  exact (CochainClass.classOf_congr (cochainCxZMod2 X) ((p + 1) + q) he.symm _ hz).trans
    (CochainClass.classOf_cast_boundary (cochainCxZMod2 X) (show (p + q) + 1 = (p + 1) + q by omega) _ hz)

end
end Finsler.SupportedExactThomCapDegree
