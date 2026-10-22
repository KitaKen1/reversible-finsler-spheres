module

public import Finsler.Loop.AvoidanceNormalizedSymmetry
public import Finsler.Loop.NormalizedComplementCapNaturality
public import Finsler.Loop.FilteredGlobalThomTime

/-! A concrete complement primitive for the ORIGINAL normalized Thom
cochain, supported away from far points AND zero on the entire actual
diagonal carrier. In particular both original cut-time faces vanish. -/
@[expose] public section
namespace Finsler.ComplementThomEndpointPrimitive
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCap
open Finsler.SupportedCapNaturality Finsler.WholeSelfCutComplement
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

variable (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 2)

def primitive : singularCochainGroup (ZMod 2) (parameters (m + 1)) m :=
  cochainPullback (selfEvaluation (m + 1)) m
    (AvoidanceNormalizedSymmetry.ambientPrimitive (m + 1) (by omega) hρ hρ2)

theorem supported :
    cochainPullback (subspaceMap (parameters (m + 1)) (exterior (m + 1) ρ)) m
      (primitive m hm hρ hρ2) = 0 := by
  rw [primitive, ← pullback_comp]
  apply AvoidanceNormalizedSymmetry.primitive_range_zero (m + 1) (by omega) hρ hρ2
  intro z
  refine Set.mem_iUnion.mpr ⟨false, ?_⟩
  change ρ ≤ distance (m + 1) z.val
  exact z.property.le

theorem diagonal_zero {X : TopCat.{0}} (f : X ⟶ parameters (m + 1))
    (hf : ∀ x, f x ∈ FilteredGlobalThomTime.endpointCarrier (m + 1)) :
    cochainPullback f m (primitive m hm hρ hρ2) = 0 := by
  rw [primitive, ← pullback_comp]
  apply AvoidanceNormalizedSymmetry.primitive_range_zero (m + 1) (by omega) hρ hρ2
  intro x
  exact Set.mem_iUnion.mpr ⟨true, hf x⟩

theorem carrier_zero :
    cochainPullback (subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))) m
      (primitive m hm hρ hρ2) = 0 :=
  diagonal_zero m hm hρ hρ2 _ (fun z => z.property)

theorem endpoint_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (atTime (m + 1) t) m (primitive m hm hρ hρ2) = 0 := by
  apply diagonal_zero m hm hρ hρ2
  rcases ht with rfl | rfl
  · exact fun _ => rfl
  · exact fun u => (sphereRepresentative_endpoints u).symm

def swapped : singularCochainGroup (ZMod 2) (parameters (m + 1)) (m + 1) :=
  cochainPullback (complement (m + 1)) (m + 1) (NormalizedSelfCut.cocycle (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) hρ)

theorem swapped_supported :
    cochainPullback (subspaceMap (parameters (m + 1)) (exterior (m + 1) ρ)) (m + 1)
      (swapped m hρ) = 0 :=
  pullback_support (complement (m + 1)) _ _ (exterior_mapsTo (m + 1) ρ) _ _
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)

theorem swapped_closed : cochainCoboundary (ZMod 2) (parameters (m + 1)) (m + 1) (swapped m hρ) = 0 :=
  pullback_closed (complement (m + 1)) _ _ (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ)

theorem boundary : cochainCoboundary (ZMod 2) (parameters (m + 1)) m (primitive m hm hρ hρ2) =
    swapped m hρ - NormalizedSelfCut.cocycle (m + 1) (by omega) hρ := by
  rw [primitive, DiagonalCutSwap.pullback_coboundary]
  have hb := AvoidanceNormalizedSymmetry.primitive_boundary (m + 1) (by omega) hρ hρ2
  change cochainCoboundary (ZMod 2) (DiagonalCohomology.product (m + 1)) m
    (AvoidanceNormalizedSymmetry.ambientPrimitive (m + 1) (by omega) hρ hρ2) = _ at hb
  rw [hb, DiagonalCutSwap.pullback_sub, ← pullback_comp, ← selfEvaluation_exchange, pullback_comp]
  rfl

include hm hρ2 in
theorem swapped_carrier_zero :
    cochainPullback (subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))) (m + 1)
      (swapped m hρ) = 0 := by
  have he := congrArg (cochainPullback
    (subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))) (m + 1))
    (boundary m hm hρ hρ2)
  rw [← DiagonalCutSwap.pullback_coboundary, carrier_zero,
    DiagonalCutSwap.pullback_sub, FilteredGlobalThomTime.cocycle_endpoint, sub_zero] at he
  have hz : cochainCoboundary (ZMod 2) (TopCat.of (FilteredGlobalThomTime.endpointCarrier (m + 1))) m 0 = 0 := map_zero _
  rw [hz] at he
  exact he.symm

end
end Finsler.ComplementThomEndpointPrimitive
