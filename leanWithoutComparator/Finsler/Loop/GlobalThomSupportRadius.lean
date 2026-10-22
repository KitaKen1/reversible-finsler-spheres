module

public import Finsler.Loop.GlobalRadiusCochains
public import Finsler.Loop.SupportedThomTimeRepresentative
public import Finsler.Loop.SupportedThomTimeRefinement

/-! Remove the auxiliary Thom support radius in the GLOBAL first-Thom
TIME operation, in its actual fixed near target. A genuine relative
primitive has both endpoint restrictions zero before integrating time. -/

@[expose] public section
namespace Finsler.GlobalThomSupportRadius
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

def rebased (m : ℕ) {ρ H S : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) (hHS : H < S) :=
  SupportedThomTime.operation (parameters (m + 1))
    (SupportedSelfCut.exterior (m + 1) H) (SupportedSelfCut.neighborhood (m + 1) S)
    (SupportedSelfCut.exterior_open (m + 1) H) (SupportedSelfCut.neighborhood_open (m + 1) S)
    (SupportedSelfCut.cover (m + 1) hHS) m (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (GlobalRadiusCochains.cocycle_far_outer m hρ hρH)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ)
    (atTime (m + 1) 0) (atTime (m + 1) 1) (SelfCutTimePrism.chainHomotopy (m + 1))
    (FilteredGlobalThomTime.endpointCarrier (m + 1)) (FilteredGlobalThomTime.endpointCarrier (m + 1))
    (FilteredGlobalThomTime.cocycle_endpoint m hρ) (FilteredGlobalThomTime.cocycle_endpoint m hρ)
    (fun _ => rfl) (fun u => (sphereRepresentative_endpoints u).symm)

theorem rebase (m : ℕ) {ρ H S : ℝ} (hρ : 0 < ρ) (hρH : ρ ≤ H) (hHS : H < S) (q : ℕ) :
    (GlobalThomTime.operation m hρ (hρH.trans_lt hHS)).homology q =
      (rebased m hρ hρH hHS).homology q := by
  exact SupportedThomTimeRefinement.homology_eq (parameters (m + 1))
    (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) S)
    (SupportedSelfCut.exterior (m + 1) H) (fun _ hz => lt_of_le_of_lt hρH hz)
    (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.exterior_open (m + 1) H)
    (SupportedSelfCut.neighborhood_open (m + 1) S)
    (SupportedSelfCut.cover (m + 1) (hρH.trans_lt hHS)) (SupportedSelfCut.cover (m + 1) hHS)
    m (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (GlobalRadiusCochains.cocycle_far_outer m hρ le_rfl)
    (GlobalRadiusCochains.cocycle_far_outer m hρ hρH)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ)
    (atTime (m + 1) 0) (atTime (m + 1) 1) (SelfCutTimePrism.chainHomotopy (m + 1))
    (FilteredGlobalThomTime.endpointCarrier (m + 1))
    (FilteredGlobalThomTime.cocycle_endpoint m hρ)
    (fun _ => rfl) (fun u => (sphereRepresentative_endpoints u).symm) q

theorem rebased_homology (m : ℕ) (hm : 1 ≤ m) {ρ₀ ρ₁ H S : ℝ}
    (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H)
    (hH : 0 < H) (hH2 : H ≤ 2) (hHS : H < S) (q : ℕ) :
    (rebased m h₀ h₀H hHS).homology q = (rebased m h₁ h₁H hHS).homology q := by
  exact SupportedThomTimeRepresentative.homology_eq (parameters (m + 1))
    (SupportedSelfCut.exterior (m + 1) H) (SupportedSelfCut.neighborhood (m + 1) S)
    (SupportedSelfCut.exterior_open (m + 1) H) (SupportedSelfCut.neighborhood_open (m + 1) S)
    (SupportedSelfCut.cover (m + 1) hHS) m _ _
    (GlobalRadiusCochains.cocycle_far_outer m h₀ h₀H) (GlobalRadiusCochains.cocycle_far_outer m h₁ h₁H)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) h₀)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) h₁)
    (GlobalRadiusCochains.primitive m hm h₀ h₁ h₀H h₁H hH hH2)
    (GlobalRadiusCochains.far_zero m hm h₀ h₁ h₀H h₁H hH hH2)
    (GlobalRadiusCochains.boundary m hm h₀ h₁ h₀H h₁H hH hH2)
    (atTime (m + 1) 0) (atTime (m + 1) 1) (SelfCutTimePrism.chainHomotopy (m + 1))
    (FilteredGlobalThomTime.endpointCarrier (m + 1))
    (FilteredGlobalThomTime.cocycle_endpoint m h₀) (FilteredGlobalThomTime.cocycle_endpoint m h₁)
    (GlobalRadiusCochains.endpoint_zero m hm h₀ h₁ h₀H h₁H hH hH2)
    (fun _ => rfl) (fun u => (sphereRepresentative_endpoints u).symm) q

theorem homology_eq (m : ℕ) (hm : 1 ≤ m) {ρ₀ ρ₁ H S : ℝ}
    (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H)
    (hH : 0 < H) (hH2 : H ≤ 2) (hHS : H < S) (q : ℕ) :
    (GlobalThomTime.operation m h₀ (h₀H.trans_lt hHS)).homology q =
      (GlobalThomTime.operation m h₁ (h₁H.trans_lt hHS)).homology q :=
  (rebase m h₀ h₀H hHS q).trans
    ((rebased_homology m hm h₀ h₁ h₀H h₁H hH hH2 hHS q).trans (rebase m h₁ h₁H hHS q).symm)

theorem homology_eq_max (m : ℕ) (hm : 1 ≤ m) {ρ₀ ρ₁ S : ℝ}
    (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀S : ρ₀ < S) (h₁S : ρ₁ < S) (hS : S ≤ 1) (q : ℕ) :
    (GlobalThomTime.operation m h₀ h₀S).homology q = (GlobalThomTime.operation m h₁ h₁S).homology q :=
  homology_eq m hm h₀ h₁ (le_max_left _ _) (le_max_right _ _)
    (h₀.trans_le (le_max_left _ _)) (le_trans (le_of_lt (max_lt h₀S h₁S)) (by linarith))
    (max_lt h₀S h₁S) q

end
end Finsler.GlobalThomSupportRadius
