module

public import Finsler.Loop.SupportedThomTimeNearInclusion
public import Finsler.Loop.FilteredGlobalThomTime

/-! Genuine near-radius inclusion squares for both cut loops, and
actual GLOBAL first-Thom TIME naturality in the same larger near target. -/

@[expose] public section
namespace Finsler.GlobalThomNearRadius
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def nearMap (n : ℕ) {r s : ℝ} (hrs : r ≤ s) :
    TopCat.of (SupportedSelfCut.neighborhood n r) ⟶ TopCat.of (SupportedSelfCut.neighborhood n s) :=
  SupportedThomTimeNearInclusion.nearMap (parameters n) _ _ (fun _ hz => hz.trans_le hrs)

theorem tested_square (n : ℕ) {r s : ℝ} (hrs : r ≤ s) (hr : r ≤ 1) (hs : s ≤ 1) :
    nearMap n hrs ≫ TopCat.ofHom (SupportedSelfCut.tested n hs) =
      TopCat.ofHom (SupportedSelfCut.tested n hr) := by
  ext z : 1
  rfl

theorem retained_square (n : ℕ) {r s : ℝ} (hrs : r ≤ s) (hr : r ≤ 1) (hs : s ≤ 1) :
    nearMap n hrs ≫ TopCat.ofHom (SupportedSelfCut.retained n hs) =
      TopCat.ofHom (SupportedSelfCut.retained n hr) := by
  ext z : 1
  rfl

theorem homology (m : ℕ) {ρ r s : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hrs : r ≤ s) (q : ℕ) :
    (GlobalThomTime.operation m hρ hρr).homology q ≫
      HomologicalComplex.homologyMap (push (nearMap (m + 1) hrs)) q =
    (GlobalThomTime.operation m hρ (hρr.trans_le hrs)).homology q := by
  exact SupportedThomTimeNearInclusion.homology (parameters (m + 1))
    (SupportedSelfCut.exterior (m + 1) ρ) (SupportedSelfCut.neighborhood (m + 1) r)
    (SupportedSelfCut.neighborhood (m + 1) s) (fun _ hz => hz.trans_le hrs)
    (SupportedSelfCut.exterior_open (m + 1) ρ) (SupportedSelfCut.neighborhood_open (m + 1) r)
    (SupportedSelfCut.neighborhood_open (m + 1) s)
    (SupportedSelfCut.cover (m + 1) hρr) (SupportedSelfCut.cover (m + 1) (hρr.trans_le hrs))
    m (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_supported (m + 1) (by omega) hρ)
    (NormalizedSelfCut.cocycle_closed (m + 1) (by omega) hρ)
    (atTime (m + 1) 0) (atTime (m + 1) 1) (SelfCutTimePrism.chainHomotopy (m + 1))
    (FilteredGlobalThomTime.endpointCarrier (m + 1)) (FilteredGlobalThomTime.cocycle_endpoint m hρ)
    (fun _ => rfl) (fun u => (sphereRepresentative_endpoints u).symm) q

end
end Finsler.GlobalThomNearRadius
