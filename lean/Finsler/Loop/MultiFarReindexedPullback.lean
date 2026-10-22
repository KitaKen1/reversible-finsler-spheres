module

public import Finsler.Loop.MultiFarScalarRestriction
public import Finsler.Loop.SupportedSmallCochainComparison

/-! Scalar pullback with DIFFERENT far-index types and an actual index
map. No bijection or naturality of full retractions is required: each
source far is sent to its specified target far; the real source cover
and near-output comparison supply the subdivision primitive. -/
@[expose] public section
namespace Finsler.MultiFarReindexedPullback
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.MultiFarSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {X Y : TopCat.{0}} {ι κ : Type*} (f : X ⟶ Y) (σ : ι → κ)
  (A : ι → Set X) (B : Set X) (C : κ → Set Y) (D : Set Y)
  (hA : ∀ i, IsOpen (A i)) (hB : IsOpen B) (hcX : (⋃ i, A i) ∪ B = Set.univ)
  (hC : ∀ i, IsOpen (C i)) (hD : IsOpen D) (hcY : (⋃ i, C i) ∪ D = Set.univ)
  (hfA : ∀ i, Set.MapsTo f (A i) (C (σ i))) (hfB : Set.MapsTo f B D)
  (p q n : ℕ) (hN : p + q = n + 1) (θ : singularCochainGroup (ZMod 2) Y p)
  (hs : ∀ i, cochainPullback (SupportedCap.subspaceMap Y (C i)) p θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q)

def sourceValue : singularCochainGroup (ZMod 2) X (n + 1) :=
  cut X A B hA hB hcX p q (n + 1) hN (cochainPullback f p θ)
    (fun i => pullback_support f (A i) (C (σ i)) (hfA i) p θ (hs (σ i))) ≫
      cochainPullback (restriction f B D hfB) q ψ

def targetValue : singularCochainGroup (ZMod 2) X (n + 1) :=
  cochainPullback f (n + 1) (cut Y C D hC hD hcY p q (n + 1) hN θ hs ≫ ψ)

def difference : singularCochainGroup (ZMod 2) X (n + 1) := (sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) - (targetValue f C D hC hD hcY p q n hN θ hs ψ)

theorem near_equal : cochainPullback (SupportedCap.subspaceMap X B) (n + 1) (sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) =
    cochainPullback (SupportedCap.subspaceMap X B) (n + 1) (targetValue f C D hC hD hcY p q n hN θ hs ψ) := by
  unfold sourceValue targetValue
  rw [MultiFarScalarRestriction.near]
  symm
  simpa only [restriction_inclusion, pullback_comp] using
    (MultiFarScalarRestriction.near_map Y C D hC hD hcY p q (n + 1) hN θ hs ψ
      (restriction f B D hfB))

theorem small_zero : (inclusion X (cover X A B)).f (n + 1) ≫
    difference f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ = 0 := by
  apply CarrierCochainZero.small_zero
  intro i
  cases i with
  | none =>
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X B).op).f (n + 1)).hom ((sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) - (targetValue f C D hC hD hcY p q n hN θ hs ψ)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (near_equal f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ)
  | some i =>
    change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X (A i)).op).f (n + 1)).hom ((sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) - (targetValue f C D hC hD hcY p q n hN θ hs ψ)) = 0
    rw [map_sub]
    change cochainPullback (SupportedCap.subspaceMap X (A i)) (n + 1) (sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) -
      cochainPullback (SupportedCap.subspaceMap X (A i)) (n + 1) (targetValue f C D hC hD hcY p q n hN θ hs ψ) = 0
    unfold sourceValue targetValue
    rw [MultiFarScalarRestriction.far]
    have ht := pullback_support f (A i) (C (σ i)) (hfA i) (n + 1)
      (cut Y C D hC hD hcY p q (n + 1) hN θ hs ≫ ψ)
      (MultiFarScalarRestriction.far Y C D hC hD hcY p q (n + 1) hN θ hs ψ (σ i))
    rw [ht, sub_self]

def primitive : singularCochainGroup (ZMod 2) X n :=
  SupportedSmallCochainComparison.primitive (cover X A B) n
    (difference f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ)

variable (hθ : cochainCoboundary (ZMod 2) Y p θ = 0)
  (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) q ψ = 0)

include hθ hψ in
theorem difference_closed : cochainCoboundary (ZMod 2) X (n + 1)
    (difference f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = 0 := by
  have hsource := MultiFarSupportedCochain.scalar_closed X A B hA hB hcX p q (n + 1) hN
    (cochainPullback f p θ) (fun i => pullback_support f (A i) (C (σ i)) (hfA i) p θ (hs (σ i)))
    (pullback_closed f p θ hθ) (cochainPullback (restriction f B D hfB) q ψ)
    (pullback_closed (restriction f B D hfB) q ψ hψ)
  have htarget := pullback_closed f (n + 1)
    (cut Y C D hC hD hcY p q (n + 1) hN θ hs ≫ ψ)
    (MultiFarSupportedCochain.scalar_closed Y C D hC hD hcY p q (n + 1) hN θ hs hθ ψ hψ)
  change ((cochainCxZMod2 X).d (n + 1) (n + 2)).hom ((sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) - (targetValue f C D hC hD hcY p q n hN θ hs ψ)) = 0
  rw [map_sub]
  change cochainCoboundary (ZMod 2) X (n + 1) (sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) - cochainCoboundary (ZMod 2) X (n + 1) (targetValue f C D hC hD hcY p q n hN θ hs ψ) = 0
  exact sub_eq_zero.mpr (hsource.trans htarget.symm)

include hθ hψ in
theorem boundary : cochainCoboundary (ZMod 2) X n
    (primitive f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = (sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) - (targetValue f C D hC hD hcY p q n hN θ hs ψ) :=
  SupportedSmallCochainComparison.primitive_boundary (cover X A B)
    (cover_open X A B hA hB) (cover_univ X A B hcX) n _
    (difference_closed f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ hθ hψ)
    (small_zero f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ)

include hθ hψ in
theorem cycle_values_eq (c : coeff ⟶ (chains X).X (n + 1))
    (hc : c ≫ (chains X).d (n + 1) n = 0) : c ≫ (sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) = c ≫ (targetValue f C D hC hD hcY p q n hN θ hs ψ) := by
  have hb := congrArg (fun a => c ≫ a)
    (boundary f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ hθ hψ)
  change c ≫ ((chains X).d (n + 1) n ≫
    primitive f σ A B C D hA hB hcX hC hD hcY hfA hfB p q n hN θ hs ψ) = c ≫ ((sourceValue f σ A B C D hA hB hcX hfA hfB p q n hN θ hs ψ) - (targetValue f C D hC hD hcY p q n hN θ hs ψ)) at hb
  rw [← Category.assoc, hc, zero_comp, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.MultiFarReindexedPullback
