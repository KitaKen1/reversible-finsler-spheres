module

public import Finsler.Loop.OriginalDoubleCapCarrier
public import Finsler.Topology.RelativeCapDual

/-! Genuine intersection swap and actual scalar cap pullback. These
retain the local output test when the two ORIGINAL near sets change
order; no new global extension of that test is introduced. -/
@[expose] public section
namespace Finsler.IntersectionCapPullback
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem cochain_identity (X : TopCat.{0}) (q : ℕ) (ψ : singularCochainGroup (ZMod 2) X q) :
    cochainPullback (𝟙 X) q ψ = ψ :=
  congrArg (fun f => (f.f q).hom ψ) (singularCochainComplexZMod2.map_id (Opposite.op X))

theorem cap_scalar_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) (p q N : ℕ) (hN : p + q = N)
    (θ : singularCochainGroup (ZMod 2) Y p) (ψ : singularCochainGroup (ZMod 2) Y q) :
    cochainPullback f N (absoluteChain Y p q N hN θ ≫ ψ) =
      absoluteChain X p q N hN (cochainPullback f p θ) ≫ cochainPullback f q ψ := by
  subst N
  rw [RelativeCapDual.absolute_chain_dual, RelativeCapDual.absolute_chain_dual, cochainCup_naturality]

def swap (X : TopCat.{0}) (B D : Set X) : TopCat.of (B ∩ D : Set X) ⟶ TopCat.of (D ∩ B : Set X) :=
  TopCat.ofHom ⟨fun z => ⟨z.val, z.property.2, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

theorem swap_inclusion (X : TopCat.{0}) (B D : Set X) :
    swap X B D ≫ SupportedCap.subspaceMap X (D ∩ B) = SupportedCap.subspaceMap X (B ∩ D) := rfl

theorem swap_roundtrip (X : TopCat.{0}) (B D : Set X) :
    swap X B D ≫ swap X D B = 𝟙 (TopCat.of (B ∩ D : Set X)) := by
  ext z : 1
  rfl

theorem swap_test_identity (X : TopCat.{0}) (B D : Set X) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (B ∩ D : Set X)) q) :
    cochainPullback (swap X B D) q (cochainPullback (swap X D B) q ψ) = ψ := by
  rw [← pullback_comp, swap_roundtrip, cochain_identity]

theorem swap_test_support (X : TopCat.{0}) (B D S : Set X) (q : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (B ∩ D : Set X)) q)
    (hψ : cochainPullback (restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' (B ∩ D)) (B ∩ D) (fun _ h => h)) q ψ = 0) :
    cochainPullback (restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' (D ∩ B)) (D ∩ B) (fun _ h => h)) q
      (cochainPullback (swap X D B) q ψ) = 0 := by
  let f := restriction (SupportedCap.subspaceMap X S)
    ((SupportedCap.subspaceMap X S) ⁻¹' (D ∩ B)) (D ∩ B) (fun _ h => h)
  let g : TopCat.of ((SupportedCap.subspaceMap X S) ⁻¹' (D ∩ B)) ⟶
      TopCat.of ((SupportedCap.subspaceMap X S) ⁻¹' (B ∩ D)) := TopCat.ofHom
    ⟨fun z => ⟨z.val, z.property.2, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  have he : f ≫ swap X D B = g ≫ restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' (B ∩ D)) (B ∩ D) (fun _ h => h) := rfl
  change cochainPullback f q (cochainPullback (swap X D B) q ψ) = 0
  rw [← pullback_comp, he, pullback_comp, hψ]
  change (push g).f q ≫ 0 = 0
  exact comp_zero

end
end Finsler.IntersectionCapPullback
