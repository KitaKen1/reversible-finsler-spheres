module

public import Finsler.Topology.DiagonalCutSwap
public import Finsler.Topology.NormalizedThomComparison

/-! The actual far-supported normalized diagonal representative induces
exactly the specified diagonal Thom cut in the genuine neighborhood
homology. The comparison primitive itself is supported on the same far
set, so its correction cap stays in that neighborhood. -/

@[expose] public section
namespace Finsler.FarNormalizedDiagonalCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem cochain_identity {Y : TopCat.{0}} (k : ℕ) (φ : singularCochainGroup (ZMod 2) Y k) :
    cochainPullback (𝟙 Y) k φ = φ := by
  have hi : singularCochainComplexZMod2.map (𝟙 Y).op = 𝟙 (cochainCxZMod2 Y) :=
    CategoryTheory.Functor.map_id _ _
  change ((singularCochainComplexZMod2.map (𝟙 Y).op).f k).hom φ = φ
  rw [hi, HomologicalComplex.id_f]
  rfl

theorem dim_pos (m : ℕ) : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)

variable (m : ℕ) {X : TopCat.{0}} (f g : X ⟶ BorelEvaluation.sphere (m + 1))
  {ρ : ℝ} (hρ : 0 < ρ)

def cocycle : singularCochainGroup (ZMod 2) X (m + 1) :=
  cochainPullback (DiagonalPullbackCut.pairEvaluation f g) (m + 1)
    (NormalizedDiagonalCocycle.ambient (m + 1) (dim_pos m) hρ)

theorem cocycle_closed : cochainCoboundary (ZMod 2) X (m + 1) (cocycle m f g hρ) = 0 :=
  pullback_closed _ _ _ (NormalizedDiagonalCocycle.ambient_closed (m + 1) (dim_pos m) hρ)

variable (hm : 1 ≤ m) (hρ2 : ρ ≤ 2)

def primitive : singularCochainGroup (ZMod 2) X m :=
  cochainPullback (DiagonalPullbackCut.pairEvaluation f g) m
    (NormalizedThomComparison.ambientPrimitive (m + 1) (Nat.succ_le_succ hm) hρ hρ2)

theorem primitive_boundary : cochainCoboundary (ZMod 2) X m (primitive m f g hρ hm hρ2) =
    cocycle m f g hρ - DiagonalPullbackCut.cocycle (dim_pos m) f g := by
  rw [primitive, DiagonalCutSwap.pullback_coboundary]
  have hb : cochainCoboundary (ZMod 2) (DiagonalCohomology.product (m + 1)) m
      (NormalizedThomComparison.ambientPrimitive (m + 1) (Nat.succ_le_succ hm) hρ hρ2) =
      NormalizedDiagonalCocycle.ambient (m + 1) (dim_pos m) hρ -
        DiagonalCocycle.ambientCocycle (m + 1) (dim_pos m) :=
    NormalizedThomComparison.ambientPrimitive_boundary (m + 1) (Nat.succ_le_succ hm) hρ hρ2
  rw [hb, DiagonalCutSwap.pullback_sub, ← DiagonalPullbackCut.cocycle_comparison]
  rfl

variable (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
  (hf : Set.MapsTo (DiagonalPullbackCut.pairEvaluation f g) A (DiagonalAvoidanceCocycle.far (m + 1) ρ))

include hρ hf in
theorem far_exclusion : A ⊆ DiagonalPullbackCut.exclusion f g := by
  intro x hx
  exact DiagonalAvoidanceCocycle.far_subset_deleted (m + 1) hρ (hf hx)

include hf in
theorem cocycle_supported : cochainPullback (SupportedCap.subspaceMap X A) (m + 1) (cocycle m f g hρ) = 0 :=
  pullback_support (DiagonalPullbackCut.pairEvaluation f g) A (DiagonalAvoidanceCocycle.far (m + 1) ρ) hf
    (m + 1) _ (NormalizedDiagonalCocycle.far_supported (m + 1) (dim_pos m) hρ)

include hρ hf in
theorem specified_supported : cochainPullback (SupportedCap.subspaceMap X A) (m + 1)
    (DiagonalPullbackCut.cocycle (dim_pos m) f g) = 0 := by
  have he := pullback_support (𝟙 X) A (DiagonalPullbackCut.exclusion f g)
    (far_exclusion m f g hρ A hf) (m + 1) _ (DiagonalPullbackCut.cocycle_supported (dim_pos m) f g)
  simpa only [cochain_identity] using he

include hf in
theorem primitive_supported : cochainPullback (SupportedCap.subspaceMap X A) m (primitive m f g hρ hm hρ2) = 0 :=
  pullback_support (DiagonalPullbackCut.pairEvaluation f g) A (DiagonalAvoidanceCocycle.far (m + 1) ρ) hf
    m _ (NormalizedThomComparison.ambientPrimitive_supported (m + 1) (Nat.succ_le_succ hm) hρ hρ2)

def operation := SupportedCapHomology.operation X A B hA hB hc (m + 1)
  (cocycle m f g hρ) (cocycle_supported m f g hρ A hf) (cocycle_closed m f g hρ)

include hm hρ2 in
theorem representative_homology (q : ℕ) : (operation m f g hρ A B hA hB hc hf).homology q =
    (SupportedCapHomology.operation X A B hA hB hc (m + 1)
      (DiagonalPullbackCut.cocycle (dim_pos m) f g) (specified_supported m f g hρ A hf)
      (DiagonalPullbackCut.cocycle_closed (dim_pos m) f g)).homology q :=
  SupportedCapRepresentative.homology_eq X A B hA hB hc m q _ _
    (cocycle_supported m f g hρ A hf) (specified_supported m f g hρ A hf)
    (cocycle_closed m f g hρ) (DiagonalPullbackCut.cocycle_closed (dim_pos m) f g)
    (primitive m f g hρ hm hρ2) (primitive_supported m f g hρ hm hρ2 A hf)
    (primitive_boundary m f g hρ hm hρ2)

end
end Finsler.FarNormalizedDiagonalCap
