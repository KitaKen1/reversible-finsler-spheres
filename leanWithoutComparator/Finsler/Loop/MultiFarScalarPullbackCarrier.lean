module

public import Finsler.Loop.MultiFarScalarPullback

/-! The scalar pullback primitive retains actual carrier support.
Consequently the comparison also applies to chains whose boundary
factors through the specified carrier, not only to absolute cycles. -/
@[expose] public section
namespace Finsler.MultiFarScalarPullbackCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.MultiFarSupportedCap Finsler.MultiFarScalarPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem near_test_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (B S : Set X) (D T : Set Y)
    (hfB : Set.MapsTo f B D) (hfS : Set.MapsTo f S T) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q)
    (hψ : cochainPullback (restriction (SupportedCap.subspaceMap Y T)
      ((SupportedCap.subspaceMap Y T) ⁻¹' D) D (fun _ h => h)) q ψ = 0) :
    cochainPullback (restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' B) B (fun _ h => h)) q
        (cochainPullback (restriction f B D hfB) q ψ) = 0 := by
  let g : TopCat.of ((SupportedCap.subspaceMap X S) ⁻¹' B) ⟶
      TopCat.of ((SupportedCap.subspaceMap Y T) ⁻¹' D) := TopCat.ofHom
    ⟨fun z => ⟨⟨f z.val.val, hfS z.val.property⟩, hfB z.property⟩, by fun_prop⟩
  have he : restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' B) B (fun _ h => h) ≫ restriction f B D hfB =
    g ≫ restriction (SupportedCap.subspaceMap Y T)
      ((SupportedCap.subspaceMap Y T) ⁻¹' D) D (fun _ h => h) := rfl
  rw [← pullback_comp, he, pullback_comp, hψ]
  change (push g).f q ≫ 0 = 0
  exact comp_zero

variable {X Y : TopCat.{0}} {ι : Type*} (f : X ⟶ Y)
  (A : ι → Set X) (B : Set X) (C : ι → Set Y) (D : Set Y)
  (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hcX : (⋃ i, A i) ∪ B = Set.univ)
  (hC : ∀ i, IsOpen (C i)) (hD : IsOpen D) (hcY : (⋃ i, C i) ∪ D = Set.univ)
  (hfA : ∀ i, Set.MapsTo f (A i) (C i)) (hfB : Set.MapsTo f B D)
  (p q n : ℕ) (hN : p + q = n + 1) (θ : singularCochainGroup (ZMod 2) Y p)
  (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap Y (C i)) p θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q)
  (S : Set X) (T : Set Y) (hfS : Set.MapsTo f S T)
  (hS : cochainPullback (restriction (SupportedCap.subspaceMap Y T)
    ((SupportedCap.subspaceMap Y T) ⁻¹' D) D (fun _ h => h)) q ψ = 0)

include hfS hS in
theorem difference_zero : cochainPullback (SupportedCap.subspaceMap X S) (n + 1)
    (difference f A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = 0 := by
  have hsource := MultiFarSupportedCochain.subspace_zero X A B hA hB hcX S p q (n + 1) hN
    (cochainPullback f p θ) (fun i => pullback_support f (A i) (C i) (hfA i) p θ (hs i))
    (cochainPullback (restriction f B D hfB) q ψ) (near_test_zero f B S D T hfB hfS q ψ hS)
  have htarget := pullback_support f S T hfS (n + 1)
    (cut Y C D hC hD hcY p q (n + 1) hN θ hs ≫ ψ)
    (MultiFarSupportedCochain.subspace_zero Y C D hC hD hcY T p q (n + 1) hN θ hs ψ hS)
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f (n + 1)).hom
    (sourceValue f A B C D hA hB hcX hfA hfB p q n hN θ hs ψ -
      targetValue f C D hC hD hcY p q n hN θ hs ψ) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (hsource.trans htarget.symm)

include hfS hS in
theorem primitive_zero : cochainPullback (SupportedCap.subspaceMap X S) n
    (primitive f A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = 0 :=
  SupportedSmallCochainComparison.primitive_support_zero (cover X A B) S n _
    (difference_zero f A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ S T hfS hS)

include hfS hS in
theorem relative_values_eq
    (hθ : cochainCoboundary (ZMod 2) Y p θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) q ψ = 0)
    (c : coeff ⟶ (chains X).X (n + 1)) (b : coeff ⟶ (chains (TopCat.of S)).X n)
    (hc : c ≫ (chains X).d (n + 1) n = b ≫ (push (SupportedCap.subspaceMap X S)).f n) :
    c ≫ sourceValue f A B C D hA hB hcX hfA hfB p q n hN θ hs ψ =
      c ≫ targetValue f C D hC hD hcY p q n hN θ hs ψ := by
  have hb := congrArg (fun a => c ≫ a)
    (boundary f A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ hθ hψ)
  have hp : (push (SupportedCap.subspaceMap X S)).f n ≫
      primitive f A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ = 0 :=
    primitive_zero f A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ S T hfS hS
  change c ≫ ((chains X).d (n + 1) n ≫
    primitive f A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = _ at hb
  rw [← Category.assoc, hc, Category.assoc, hp, comp_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.MultiFarScalarPullbackCarrier
