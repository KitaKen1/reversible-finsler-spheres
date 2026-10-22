module

public import Finsler.Loop.FilteredRadiusCochains
public import Finsler.Loop.SupportedThomTimeRepresentative
public import Finsler.Loop.SupportedThomTimeRefinement

/-! Radius independence of the genuine first Thom time operation in
one actual filtered near target. Rebase the far cover by a real relative
time refinement, then integrate the actual endpoint-zero primitive. -/

@[expose] public section
namespace Finsler.FilteredThomSupportRadius

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable (m : ℕ) (F : ReversibleMetric (m + 1)) (a : ℝ)

def rebased {ρ H S : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) (hHS : H < S) :=
  SupportedThomTime.operation (FilteredPrismSelfCut.domain F a)
    (FilteredPrismSelfCut.far F a H) (FilteredPrismSelfCut.near F a S)
    (FilteredPrismSelfCut.far_open F a H) (FilteredPrismSelfCut.near_open F a S) (FilteredPrismSelfCut.cover F a hHS)
    m (FilteredPrismSelfCut.cocycle (by omega) F a hρ)
    (FilteredRadiusCochains.cocycle_far_outer m F a hρ hρH) (FilteredPrismSelfCut.cocycle_closed (by omega) F a hρ)
    (FilteredPrismSelfCut.atTimeBelow F a 0) (FilteredPrismSelfCut.atTimeBelow F a 1)
    ((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff)
    (FilteredRadiusCochains.endpointCarrier m F a) (FilteredRadiusCochains.endpointCarrier m F a)
    (FilteredRadiusCochains.cocycle_endpoint m F a hρ) (FilteredRadiusCochains.cocycle_endpoint m F a hρ)
    (FilteredRadiusCochains.time_endpoint m F a 0 (Or.inl rfl))
    (FilteredRadiusCochains.time_endpoint m F a 1 (Or.inr rfl))

def operation {ρ S : ℝ} (hρ : 0 < ρ) (hρS : ρ < S) := rebased m F a hρ le_rfl hρS

theorem rebase {ρ H S : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) (hHS : H < S) (q : ℕ) :
    (operation m F a hρ (hρH.trans_lt hHS)).homology q = (rebased m F a hρ hρH hHS).homology q := by
  exact SupportedThomTimeRefinement.homology_eq (FilteredPrismSelfCut.domain F a)
    (FilteredPrismSelfCut.far F a ρ) (FilteredPrismSelfCut.near F a S) (FilteredPrismSelfCut.far F a H)
    (fun _ hz => lt_of_le_of_lt hρH hz)
    (FilteredPrismSelfCut.far_open F a ρ) (FilteredPrismSelfCut.far_open F a H)
    (FilteredPrismSelfCut.near_open F a S)
    (FilteredPrismSelfCut.cover F a (hρH.trans_lt hHS)) (FilteredPrismSelfCut.cover F a hHS)
    m (FilteredPrismSelfCut.cocycle (by omega) F a hρ)
    (FilteredRadiusCochains.cocycle_far_outer m F a hρ le_rfl)
    (FilteredRadiusCochains.cocycle_far_outer m F a hρ hρH) (FilteredPrismSelfCut.cocycle_closed (by omega) F a hρ)
    (FilteredPrismSelfCut.atTimeBelow F a 0) (FilteredPrismSelfCut.atTimeBelow F a 1)
    ((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff) (FilteredRadiusCochains.endpointCarrier m F a)
    (FilteredRadiusCochains.cocycle_endpoint m F a hρ)
    (FilteredRadiusCochains.time_endpoint m F a 0 (Or.inl rfl))
    (FilteredRadiusCochains.time_endpoint m F a 1 (Or.inr rfl)) q

theorem rebased_homology (hm : 1 ≤ m) {ρ₀ ρ₁ H S : ℝ} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H) (hH : 0 < H) (hH2 : H ≤ 2) (hHS : H < S) (q : ℕ) :
    (rebased m F a h₀ h₀H hHS).homology q = (rebased m F a h₁ h₁H hHS).homology q := by
  exact SupportedThomTimeRepresentative.homology_eq (FilteredPrismSelfCut.domain F a)
    (FilteredPrismSelfCut.far F a H) (FilteredPrismSelfCut.near F a S)
    (FilteredPrismSelfCut.far_open F a H) (FilteredPrismSelfCut.near_open F a S) (FilteredPrismSelfCut.cover F a hHS)
    m _ _ (FilteredRadiusCochains.cocycle_far_outer m F a h₀ h₀H) (FilteredRadiusCochains.cocycle_far_outer m F a h₁ h₁H)
    (FilteredPrismSelfCut.cocycle_closed (by omega) F a h₀) (FilteredPrismSelfCut.cocycle_closed (by omega) F a h₁)
    (FilteredRadiusCochains.primitive m F a hm h₀ h₁ h₀H h₁H hH hH2)
    (FilteredRadiusCochains.far_zero m F a hm h₀ h₁ h₀H h₁H hH hH2)
    (FilteredRadiusCochains.boundary m F a hm h₀ h₁ h₀H h₁H hH hH2)
    (FilteredPrismSelfCut.atTimeBelow F a 0) (FilteredPrismSelfCut.atTimeBelow F a 1)
    ((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff) (FilteredRadiusCochains.endpointCarrier m F a)
    (FilteredRadiusCochains.cocycle_endpoint m F a h₀) (FilteredRadiusCochains.cocycle_endpoint m F a h₁)
    (FilteredRadiusCochains.endpoint_zero m F a hm h₀ h₁ h₀H h₁H hH hH2)
    (FilteredRadiusCochains.time_endpoint m F a 0 (Or.inl rfl))
    (FilteredRadiusCochains.time_endpoint m F a 1 (Or.inr rfl)) q

theorem homology_eq (hm : 1 ≤ m) {ρ₀ ρ₁ H S : ℝ} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H) (hH : 0 < H) (hH2 : H ≤ 2) (hHS : H < S) (q : ℕ) :
    (operation m F a h₀ (h₀H.trans_lt hHS)).homology q =
    (operation m F a h₁ (h₁H.trans_lt hHS)).homology q :=
  (rebase m F a h₀ h₀H hHS q).trans
    ((rebased_homology m F a hm h₀ h₁ h₀H h₁H hH hH2 hHS q).trans
      (rebase m F a h₁ h₁H hHS q).symm)

end
end Finsler.FilteredThomSupportRadius
