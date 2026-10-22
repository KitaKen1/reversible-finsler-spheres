module

public import Finsler.Loop.NormalizedRadiusRelativeComparison
public import Finsler.Topology.FilteredPrismSelfCut
public import Finsler.Topology.DiagonalCutSwap

/-! The genuine two-radius primitive pulled to the actual filtered
self-cut cylinder. It has literal normalized-minus-normalized boundary,
common far support and zero on the diagonal endpoint carrier. -/

@[expose] public section
namespace Finsler.FilteredRadiusCochains

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SelfCutThomCocycle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable (m : ℕ) (F : ReversibleMetric (m + 1)) (a : ℝ)

def evaluation := FilteredPrismSelfCut.forget F a ≫ selfEvaluation (m + 1)

theorem cocycle_eq {ρ : ℝ} (hρ : 0 < ρ) :
    FilteredPrismSelfCut.cocycle (by omega) F a hρ =
    cochainPullback (evaluation m F a) (m + 1) (NormalizedDiagonalCocycle.ambient (m + 1) (by omega) hρ) := by
  rw [FilteredPrismSelfCut.cocycle, NormalizedSelfCut.cocycle, ← pullback_comp]
  rfl

def endpointCarrier : Set (FilteredPrismSelfCut.domain F a) := (evaluation m F a) ⁻¹' DiagonalAvoidanceCocycle.diagonal (m + 1)

theorem cocycle_endpoint {ρ : ℝ} (hρ : 0 < ρ) :
    cochainPullback (SupportedCap.subspaceMap (FilteredPrismSelfCut.domain F a) (endpointCarrier m F a)) (m + 1)
      (FilteredPrismSelfCut.cocycle (by omega) F a hρ) = 0 := by
  rw [cocycle_eq, ← pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_diagonal (by omega) hρ
  intro z
  exact z.property

theorem time_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (u : SelfCutOscillation.short F a) :
    FilteredPrismSelfCut.atTimeBelow F a t u ∈ endpointCarrier m F a := by
  rcases ht with rfl | rfl
  · rfl
  · exact (sphereRepresentative_endpoints u.val).symm

theorem cocycle_far_outer {ρ H : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) :
    cochainPullback (SupportedCap.subspaceMap (FilteredPrismSelfCut.domain F a) (FilteredPrismSelfCut.far F a H)) (m + 1)
      (FilteredPrismSelfCut.cocycle (by omega) F a hρ) = 0 := by
  rw [cocycle_eq, ← pullback_comp]
  apply NormalizedDiagonalCocycle.pullback_zero_of_far (by omega) hρ
  intro z
  exact hρH.trans z.property.le

variable (hm : 1 ≤ m) {ρ₀ ρ₁ H : ℝ} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
  (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H) (hH : 0 < H) (hH2 : H ≤ 2)

def primitive := cochainPullback (evaluation m F a) m
  (NormalizedRadiusRelativeComparison.primitive (m + 1) (by omega) h₀ h₁ h₀H h₁H hH hH2)

theorem boundary : cochainCoboundary (ZMod 2) (FilteredPrismSelfCut.domain F a) m
    (primitive m F a hm h₀ h₁ h₀H h₁H hH hH2) =
    FilteredPrismSelfCut.cocycle (by omega) F a h₀ - FilteredPrismSelfCut.cocycle (by omega) F a h₁ := by
  rw [primitive, DiagonalCutSwap.pullback_coboundary]
  have he := NormalizedRadiusRelativeComparison.primitive_boundary (m + 1) (by omega) h₀ h₁ h₀H h₁H hH hH2
  change cochainCoboundary (ZMod 2) (DiagonalCohomology.product (m + 1)) m
      (NormalizedRadiusRelativeComparison.primitive (m + 1) (by omega) h₀ h₁ h₀H h₁H hH hH2) =
    NormalizedDiagonalCocycle.ambient (m + 1) (by omega) h₀ - NormalizedDiagonalCocycle.ambient (m + 1) (by omega) h₁ at he
  rw [he, DiagonalCutSwap.pullback_sub, cocycle_eq, cocycle_eq]

theorem far_zero :
    cochainPullback (SupportedCap.subspaceMap (FilteredPrismSelfCut.domain F a) (FilteredPrismSelfCut.far F a H)) m
      (primitive m F a hm h₀ h₁ h₀H h₁H hH hH2) = 0 := by
  rw [primitive, ← pullback_comp]
  apply NormalizedRadiusRelativeComparison.primitive_pullback_zero
  intro z
  refine Set.mem_iUnion.mpr ⟨false, ?_⟩
  change H ≤ SupportedSelfCut.distance (m + 1) (FilteredPrismSelfCut.forget F a z.val)
  exact z.property.le

theorem endpoint_zero :
    cochainPullback (SupportedCap.subspaceMap (FilteredPrismSelfCut.domain F a) (endpointCarrier m F a)) m
      (primitive m F a hm h₀ h₁ h₀H h₁H hH hH2) = 0 := by
  rw [primitive, ← pullback_comp]
  apply NormalizedRadiusRelativeComparison.primitive_pullback_zero
  intro z
  exact Set.mem_iUnion.mpr ⟨true, z.property⟩

end
end Finsler.FilteredRadiusCochains
