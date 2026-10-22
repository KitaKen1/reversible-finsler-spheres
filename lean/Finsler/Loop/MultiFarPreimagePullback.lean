module

public import Finsler.Loop.MultiFarScalarPullbackCarrier

/-! Instantiate scalar pullback on the actual inverse-image cover.
All source supports, open sets and cover witnesses are constructed.
The explicit primitive preserves the inverse image of each carrier. -/
@[expose] public section
namespace Finsler.MultiFarPreimagePullback
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem preimage_cover {X Y : TopCat.{0}} {ι : Type*} (f : X ⟶ Y)
    (A : ι → Set Y) (B : Set Y) (hc : (⋃ i, A i) ∪ B = Set.univ) :
    (⋃ i, f ⁻¹' A i) ∪ f ⁻¹' B = Set.univ := by
  rw [← Set.preimage_iUnion, ← Set.preimage_union, hc, Set.preimage_univ]

variable {X Y : TopCat.{0}} {ι : Type*} (f : X ⟶ Y) (A : ι → Set Y) (B : Set Y)
  (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hc : (⋃ i, A i) ∪ B = Set.univ)
  (p q n : ℕ) (hN : p + q = n + 1) (θ : singularCochainGroup (ZMod 2) Y p)
  (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap Y (A i)) p θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

def localValue : singularCochainGroup (ZMod 2) X (n + 1) :=
  MultiFarScalarPullback.sourceValue f (fun i => f ⁻¹' A i) (f ⁻¹' B) A B
    (fun i => (hA i).preimage f.hom.continuous) (hB.preimage f.hom.continuous)
    (preimage_cover f A B hc) (fun _ _ h => h) (fun _ h => h) p q n hN θ hs ψ

def primitive : singularCochainGroup (ZMod 2) X n :=
  MultiFarScalarPullback.primitive f (fun i => f ⁻¹' A i) (f ⁻¹' B) A B
    (fun i => (hA i).preimage f.hom.continuous) (hB.preimage f.hom.continuous)
    (preimage_cover f A B hc) hA hB hc (fun _ _ h => h) (fun _ h => h) p q n hN θ hs ψ

theorem boundary (hθ : cochainCoboundary (ZMod 2) Y p θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X n (primitive f A B hA hB hc p q n hN θ hs ψ) =
      localValue f A B hA hB hc p q n hN θ hs ψ -
        cochainPullback f (n + 1) (MultiFarSupportedCap.cut Y A B hA hB hc p q (n + 1) hN θ hs ≫ ψ) :=
  MultiFarScalarPullback.boundary f (fun i => f ⁻¹' A i) (f ⁻¹' B) A B
    (fun i => (hA i).preimage f.hom.continuous) (hB.preimage f.hom.continuous)
    (preimage_cover f A B hc) hA hB hc (fun _ _ h => h) (fun _ h => h) p q n hN θ hs ψ hθ hψ

theorem primitive_zero (T : Set Y)
    (hT : cochainPullback (restriction (SupportedCap.subspaceMap Y T)
      ((SupportedCap.subspaceMap Y T) ⁻¹' B) B (fun _ h => h)) q ψ = 0) :
    cochainPullback (SupportedCap.subspaceMap X (f ⁻¹' T)) n
      (primitive f A B hA hB hc p q n hN θ hs ψ) = 0 :=
  MultiFarScalarPullbackCarrier.primitive_zero f (fun i => f ⁻¹' A i) (f ⁻¹' B) A B
    (fun i => (hA i).preimage f.hom.continuous) (hB.preimage f.hom.continuous)
    (preimage_cover f A B hc) hA hB hc (fun _ _ h => h) (fun _ h => h) p q n hN θ hs ψ
    (f ⁻¹' T) T (fun _ h => h) hT

end
end Finsler.MultiFarPreimagePullback
