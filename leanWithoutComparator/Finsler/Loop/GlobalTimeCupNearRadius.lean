module

public import Finsler.Loop.GlobalThomNearRadius
public import Finsler.Loop.DegreeLoweringCohomologyNaturality
public import Finsler.Loop.GlobalTimeCupCohomology

/-! The genuine global time-cup cohomology operation is unchanged by
enlarging the near radius. The actual split-map inclusion squares,
ordinary cup naturality and first-Thom TIME comparison are all proved. -/

@[expose] public section
namespace Finsler.GlobalTimeCupNearRadius
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem product_eq (m p q : ℕ) {ρ r s : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (hrs : r ≤ s) (hr : r ≤ 1) (hs : s ≤ 1)
    (a : cohomologyZMod2 (TopCat.of (SphereLoop (m + 1))) p)
    (b : cohomologyZMod2 (TopCat.of (SphereLoop (m + 1))) q) :
    GlobalTimeCupCohomology.product m hρ hρr hr p q a b =
      GlobalTimeCupCohomology.product m hρ (hρr.trans_le hrs) hs p q a b := by
  let i := GlobalThomNearRadius.nearMap (m + 1) hrs
  have hh : ((GlobalThomTime.operation m hρ hρr).post (push i)).homology (p + q) =
      (GlobalThomTime.operation m hρ (hρr.trans_le hrs)).homology (p + q) := by
    rw [DegreeLoweringHomology.Map.post_homology]
    exact GlobalThomNearRadius.homology m hρ hρr hrs (p + q)
  have h := DegreeLoweringCohomologyPullback.map_eq_of_homology_eq
    ((GlobalThomTime.operation m hρ hρr).post (push i)) (p + q)
    (GlobalThomTime.operation m hρ (hρr.trans_le hrs)) hh
  rw [GlobalTimeCupCohomology.product, GlobalTimeCupCohomology.product, ← h,
    DegreeLoweringCohomologyNaturality.post, cohPullback_cupZMod2,
    ← Cup.pullback_comp, ← Cup.pullback_comp,
    GlobalThomNearRadius.tested_square (m + 1) hrs hr hs,
    GlobalThomNearRadius.retained_square (m + 1) hrs hr hs]

end
end Finsler.GlobalTimeCupNearRadius
