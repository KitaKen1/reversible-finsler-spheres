module

public import Finsler.Topology.TubeCochainExtension

/-! Extension from the genuine full subspace preserves closedness.
This does not assert global closure for extensions from proper tubes. -/

@[expose] public section
namespace Finsler.UnivCochainExtension

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

private theorem pullback_id (X : TopCat.{0}) (N : ℕ) (φ : singularCochainGroup (ZMod 2) X N) :
    cochainPullback (𝟙 X) N φ = φ := by
  exact congrArg (fun f => (f.f N).hom φ) (singularCochainComplexZMod2.map_id (Opposite.op X))

def lift (X : TopCat.{0}) : X ⟶ TopCat.of (Set.univ : Set X) :=
  TopCat.ofHom ⟨fun x => ⟨x, Set.mem_univ x⟩, continuous_id.subtype_mk _⟩

theorem lift_inclusion (X : TopCat.{0}) :
    lift X ≫ SupportedCap.subspaceMap X Set.univ = 𝟙 X := by ext x : 1; rfl

theorem pullback_injective (X : TopCat.{0}) (N : ℕ) :
    Function.Injective (cochainPullback (SupportedCap.subspaceMap X Set.univ) N :
      singularCochainGroup (ZMod 2) X N → singularCochainGroup (ZMod 2) (TopCat.of (Set.univ : Set X)) N) := by
  intro φ ψ he
  have hh := congrArg (cochainPullback (lift X) N) he
  rw [← pullback_comp, ← pullback_comp, lift_inclusion] at hh
  simpa only [pullback_id] using hh

theorem extend_closed (X : TopCat.{0}) (N : ℕ)
    (ψ : singularCochainGroup (ZMod 2) (TopCat.of (Set.univ : Set X)) N)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of (Set.univ : Set X)) N ψ = 0) :
    cochainCoboundary (ZMod 2) X N (TubeCochainExtension.extend X Set.univ N ψ) = 0 := by
  apply pullback_injective X (N + 1)
  rw [TubeCochainExtension.local_closed X Set.univ N ψ hψ]
  simp only [cochainPullback, map_zero]

theorem extend_pullback {X Y : TopCat.{0}} (e : TopCat.of (Set.univ : Set X) ⟶ Y)
    (N : ℕ) (φ : singularCochainGroup (ZMod 2) Y N) :
    TubeCochainExtension.extend X Set.univ N (cochainPullback e N φ) =
      cochainPullback (lift X ≫ e) N φ := by
  apply pullback_injective X N
  rw [TubeCochainExtension.restriction, pullback_comp, ← pullback_comp]
  have he : SupportedCap.subspaceMap X Set.univ ≫ lift X = 𝟙 (TopCat.of (Set.univ : Set X)) := by
    ext x : 1
    rfl
  rw [he]
  rw [pullback_id]

end
end Finsler.UnivCochainExtension
