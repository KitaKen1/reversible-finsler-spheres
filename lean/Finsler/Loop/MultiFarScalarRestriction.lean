module

public import Finsler.Loop.MultiFarCapRestriction
public import Finsler.Loop.IntersectionCapPullback

/-! Restrict the actual multi-far supported cap only AFTER its local
output has been evaluated. This is sufficient for the scalar shortcut:
no naturality of a chosen full subdivision retraction is needed. -/
@[expose] public section
namespace Finsler.MultiFarScalarRestriction
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.MultiFarSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) {ι : Type*} (A : ι → Set X) (B : Set X)
  (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hc : (⋃ i, A i) ∪ B = Set.univ)
  (p q N : ℕ) (hN : p + q = N) (θ : singularCochainGroup (ZMod 2) X p)
  (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap X (A i)) p θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

theorem near : cochainPullback (SupportedCap.subspaceMap X B) N
    (cut X A B hA hB hc p q N hN θ hs ≫ ψ) =
    absoluteChain (TopCat.of B) p q N hN
      (cochainPullback (SupportedCap.subspaceMap X B) p θ) ≫ ψ := by
  change (push (SupportedCap.subspaceMap X B)).f N ≫
    (cut X A B hA hB hc p q N hN θ hs ≫ ψ) = _
  rw [← Category.assoc, MultiFarCapRestriction.cut_near]

theorem far (i : ι) : cochainPullback (SupportedCap.subspaceMap X (A i)) N
    (cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0 := by
  change (push (SupportedCap.subspaceMap X (A i))).f N ≫
    (cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0
  rw [← Category.assoc, MultiFarCapRestriction.cut_far, zero_comp]

theorem near_map {Y : TopCat.{0}} (g : Y ⟶ TopCat.of B) :
    cochainPullback (g ≫ SupportedCap.subspaceMap X B) N
      (cut X A B hA hB hc p q N hN θ hs ≫ ψ) =
    absoluteChain Y p q N hN
      (cochainPullback (g ≫ SupportedCap.subspaceMap X B) p θ) ≫
        cochainPullback g q ψ := by
  rw [pullback_comp, near X A B hA hB hc p q N hN θ hs ψ,
    IntersectionCapPullback.cap_scalar_pullback, ← pullback_comp]

theorem far_map (i : ι) {Y : TopCat.{0}} (g : Y ⟶ TopCat.of (A i)) :
    cochainPullback (g ≫ SupportedCap.subspaceMap X (A i)) N
      (cut X A B hA hB hc p q N hN θ hs ≫ ψ) = 0 := by
  rw [pullback_comp, far X A B hA hB hc p q N hN θ hs ψ i]
  change (push g).f N ≫ 0 = 0
  exact comp_zero

end
end Finsler.MultiFarScalarRestriction
