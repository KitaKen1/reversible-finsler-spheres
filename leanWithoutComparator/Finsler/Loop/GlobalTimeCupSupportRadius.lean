module

public import Finsler.Loop.GlobalThomSupportRadius
public import Finsler.Loop.GlobalSelfCutTimeFactor
public import Finsler.Loop.RelativeTimeCup

/-! Actual global and high-degree relative time-cup operations do not
depend on the auxiliary Thom SUPPORT radius, at a fixed near radius.
The genuine primitive/time comparison precedes both tested cochains. -/

@[expose] public section
namespace Finsler.GlobalTimeCupSupportRadius
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

variable (m : ℕ) (hm : 1 ≤ m) {ρ₀ ρ₁ r : ℝ}
  (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀r : ρ₀ < r) (h₁r : ρ₁ < r) (hr : r ≤ 1) (p q : ℕ)

include hm

theorem prism_homology
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0) :
    (PrismSelfCut.operation m p h₀ h₀r hr T hT).homology q =
      (PrismSelfCut.operation m p h₁ h₁r hr T hT).homology q := by
  rw [← GlobalSelfCutTimeFactor.homology m p h₀ h₀r hr T hT q,
    ← GlobalSelfCutTimeFactor.homology m p h₁ h₁r hr T hT q]
  simp only [GlobalSelfCutTimeFactor.composed, DegreeLoweringComposition.homology]
  rw [GlobalThomSupportRadius.homology_eq_max m hm h₀ h₁ h₀r h₁r hr (p + q)]

theorem product_eq (a : cohomologyZMod2 (Loops (m + 1)) p)
    (b : cohomologyZMod2 (Loops (m + 1)) q) :
    GlobalTimeCupCohomology.product m h₀ h₀r hr p q a b =
      GlobalTimeCupCohomology.product m h₁ h₁r hr p q a b := by
  have h := DegreeLoweringCohomologyPullback.map_eq_of_homology_eq
    (GlobalThomTime.operation m h₀ h₀r) (p + q) (GlobalThomTime.operation m h₁ h₁r)
    (GlobalThomSupportRadius.homology_eq_max m hm h₀ h₁ h₀r h₁r hr (p + q))
  simp only [GlobalTimeCupCohomology.product, h]

theorem relative_ofAbsolute_eq (hk : (m + 1) + 1 < (m + p) + q)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    RelativeTimeCup.ofAbsolute m p q h₀ h₀r hr hk a b =
      RelativeTimeCup.ofAbsolute m p q h₁ h₁r hr hk a b := by
  rw [RelativeTimeCup.ofAbsolute, RelativeTimeCup.ofAbsolute,
    product_eq m hm h₀ h₁ h₀r h₁r hr p q a b]

theorem relative_product_eq (hk : (m + 1) + 1 < (m + p) + q)
    (a : RelativeCup.cohomology (fullPair (m + 1)) p)
    (b : RelativeCup.cohomology (fullPair (m + 1)) q) :
    RelativeTimeCup.product m p q h₀ h₀r hr hk a b =
      RelativeTimeCup.product m p q h₁ h₁r hr hk a b := by
  exact relative_ofAbsolute_eq m hm h₀ h₁ h₀r h₁r hr p q hk _ _

end
end Finsler.GlobalTimeCupSupportRadius
