module

public import Finsler.Loop.SupportedThomCarrierZero
public import Finsler.Loop.MultiFarReindexedPullback

/-! Actual reindexed scalar subdivision retains a mapped carrier
where the target Thom cochain is zero. This hypothesis is independent
of the final test, which remains defined only on the original near set. -/
@[expose] public section
namespace Finsler.ReindexedThomCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.MultiFarReindexedPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable {X Y : TopCat.{0}} {ι κ : Type*} (f : X ⟶ Y) (σ : ι → κ)
  (A : ι → Set X) (B : Set X) (C : κ → Set Y) (D : Set Y)
  (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hcX : (⋃ i, A i) ∪ B = Set.univ)
  (hC : ∀ i, IsOpen (C i)) (hD : IsOpen D) (hcY : (⋃ i, C i) ∪ D = Set.univ)
  (hfA : ∀ i, Set.MapsTo f (A i) (C (σ i))) (hfB : Set.MapsTo f B D)
  (p q n : ℕ) (hN : p + q = n + 1) (θ : singularCochainGroup (ZMod 2) Y p)
  (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap Y (C i)) p θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q)

variable (S : Set X) (T : Set Y) (hfS : Set.MapsTo f S T)
  (hT : cochainPullback (SupportedCap.subspaceMap Y T) p θ = 0)

include hT hfS in
theorem difference_zero : cochainPullback (SupportedCap.subspaceMap X S) (n + 1)
    (difference f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = 0 := by
  have hsource := SupportedThomCarrierZero.multi_scalar_zero X A B hA hB hcX S p q (n + 1) hN
    (cochainPullback f p θ) (fun i => pullback_support f (A i) (C (σ i)) (hfA i) p θ (hs (σ i)))
    (pullback_support f S T hfS p θ hT) (cochainPullback (restriction f B D hfB) q ψ)
  have htarget := pullback_support f S T hfS (n + 1)
    (MultiFarSupportedCap.cut Y C D hC hD hcY p q (n + 1) hN θ hs ≫ ψ)
    (SupportedThomCarrierZero.multi_scalar_zero Y C D hC hD hcY T p q (n + 1) hN θ hs hT ψ)
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (hsource.trans htarget.symm)

include hT hfS in
theorem primitive_zero : cochainPullback (SupportedCap.subspaceMap X S) n
    (primitive f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = 0 :=
  SupportedSmallCochainComparison.primitive_support_zero (MultiFarSupportedCap.cover X A B) S n _
    (difference_zero f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ S T hfS hT)

end
end Finsler.ReindexedThomCarrier
