module

public import Finsler.Loop.NormalizedRadiusRelativeComparison
public import Finsler.Loop.FilteredGlobalThomTime

/-! Pull the genuine normalized Thom comparison primitive to the
GLOBAL self-cut cylinder. Both the actual far support and the actual
diagonal endpoint carrier are retained before time integration. -/

@[expose] public section
namespace Finsler.GlobalRadiusCochains
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem cocycle_far_outer (m : ℕ) {ρ H : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) :
    cochainPullback (SupportedCap.subspaceMap (parameters (m + 1)) (SupportedSelfCut.exterior (m + 1) H))
      (m + 1) (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) = 0 := by
  rw [NormalizedSelfCut.cocycle, ← pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_far (by omega) hρ
  intro z
  exact hρH.trans z.property.le

variable (m : ℕ) (hm : 1 ≤ m) {ρ₀ ρ₁ H : ℝ} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
  (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H) (hH : 0 < H) (hH2 : H ≤ 2)

def primitive := cochainPullback (selfEvaluation (m + 1)) m
  (NormalizedRadiusRelativeComparison.primitive (m + 1) (by omega) h₀ h₁ h₀H h₁H hH hH2)

theorem boundary : cochainCoboundary (ZMod 2) (parameters (m + 1)) m
    (primitive m hm h₀ h₁ h₀H h₁H hH hH2) =
    NormalizedSelfCut.cocycle (m + 1) (by omega) h₀ - NormalizedSelfCut.cocycle (m + 1) (by omega) h₁ := by
  rw [primitive, DiagonalCutSwap.pullback_coboundary]
  have h := NormalizedRadiusRelativeComparison.primitive_boundary (m + 1) (by omega) h₀ h₁ h₀H h₁H hH hH2
  change cochainCoboundary (ZMod 2) (DiagonalCohomology.product (m + 1)) m
    (NormalizedRadiusRelativeComparison.primitive (m + 1) (by omega) h₀ h₁ h₀H h₁H hH hH2) =
      NormalizedDiagonalCocycle.ambient (m + 1) (by omega) h₀ -
        NormalizedDiagonalCocycle.ambient (m + 1) (by omega) h₁ at h
  rw [h, DiagonalCutSwap.pullback_sub]
  rfl

theorem far_zero : cochainPullback
    (SupportedCap.subspaceMap (parameters (m + 1)) (SupportedSelfCut.exterior (m + 1) H)) m
      (primitive m hm h₀ h₁ h₀H h₁H hH hH2) = 0 := by
  rw [primitive, ← pullback_comp]
  apply NormalizedRadiusRelativeComparison.primitive_pullback_zero
  intro z
  apply Set.mem_iUnion.mpr
  refine ⟨false, ?_⟩
  change H ≤ SupportedSelfCut.distance (m + 1) z.val
  exact z.property.le

theorem endpoint_zero : cochainPullback
    (SupportedCap.subspaceMap (parameters (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))) m
      (primitive m hm h₀ h₁ h₀H h₁H hH hH2) = 0 := by
  rw [primitive, ← pullback_comp]
  apply NormalizedRadiusRelativeComparison.primitive_pullback_zero
  intro z
  exact Set.mem_iUnion.mpr ⟨true, z.property⟩

end
end Finsler.GlobalRadiusCochains
