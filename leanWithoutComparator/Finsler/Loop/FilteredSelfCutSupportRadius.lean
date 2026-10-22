module

public import Finsler.Loop.FilteredSelfCutTimeFactor

/-! Actual support-radius independence of the full filtered self-cut
time in the same literal short output. Compare first Thom time before
composing the existing closed tested cap; all real bounds are allowed. -/

@[expose] public section
namespace Finsler.FilteredSelfCutSupportRadius

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable (m p : ℕ) (F : ReversibleMetric (m + 1)) (hm : 1 ≤ m)
  {ρ₀ ρ₁ H S ε a L : ℝ} (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
  (h₀H : ρ₀ ≤ H) (h₁H : ρ₁ ≤ H) (hH : 0 < H) (hH2 : H ≤ 2) (hHS : H < S)
  (hS : S ≤ 1) (hε : 0 < ε) (hSS : S ≤ SelfCutLengthControl.radius F hε)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0)

include hm hH hH2 in
theorem homology_eq (q : ℕ) :
    (FilteredPrismSelfCut.operation m p F h₀ (h₀H.trans_lt hHS) hS hε hSS T hT hshort (a := a)).homology q =
    (FilteredPrismSelfCut.operation m p F h₁ (h₁H.trans_lt hHS) hS hε hSS T hT hshort (a := a)).homology q := by
  rw [← FilteredSelfCutTimeFactor.homology m p F h₀ (h₀H.trans_lt hHS) hS hε hSS T hT hshort q,
    ← FilteredSelfCutTimeFactor.homology m p F h₁ (h₁H.trans_lt hHS) hS hε hSS T hT hshort q,
    FilteredSelfCutTimeFactor.composed, FilteredSelfCutTimeFactor.composed,
    DegreeLoweringComposition.homology, DegreeLoweringComposition.homology,
    FilteredThomSupportRadius.homology_eq m F a hm h₀ h₁ h₀H h₁H hH hH2 hHS (p + q)]

include hm in
theorem canonical {ρ : ℝ} (hρ : 0 < ρ) (hρS : ρ < SelfCutLengthControl.radius F hε) (q : ℕ) :
    (FilteredPrismSelfCut.operation m p F hρ hρS (SelfCutLengthControl.radius_spec F hε).2.1 hε le_rfl
      T hT hshort (a := a)).homology q =
    (FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort (a := a)).homology q := by
  let S := SelfCutLengthControl.radius F hε
  have hSp : 0 < S := (SelfCutLengthControl.radius_spec F hε).1
  have hS1 : S ≤ 1 := (SelfCutLengthControl.radius_spec F hε).2.1
  have hHS : max ρ (S / 2) < S := max_lt hρS (half_lt_self hSp)
  have hH : 0 < max ρ (S / 2) := hρ.trans_le (le_max_left _ _)
  have hH2 : max ρ (S / 2) ≤ 2 := hHS.le.trans (by linarith)
  exact homology_eq m p F hm hρ (half_pos hSp) (le_max_left _ _) (le_max_right _ _)
    hH hH2 hHS hS1 hε le_rfl T hT hshort q

end
end Finsler.FilteredSelfCutSupportRadius
