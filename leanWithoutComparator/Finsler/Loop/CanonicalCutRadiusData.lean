module

public import Finsler.Topology.FilteredPrismSelfCut

/-! An actual admissible proper-cut radius inside the canonical near
tube, with the same canonical Thom support radius. This arithmetic
choice supplies the common-cover comparison, not radius independence. -/

@[expose] public section
namespace Finsler.CanonicalCutRadiusData

open Finsler.Geometry

set_option autoImplicit false

theorem spec {n : ℕ} (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    let R := SelfCutLengthControl.radius F hε
    (0 < R / 4 ∧ R / 4 ≤ 1 ∧ R / 4 < R / 2) ∧
    R / 2 < 3 * R / 4 ∧ 3 * R / 4 < 1 ∧ 3 * R / 4 < R ∧
    R / 2 ≤ 2 ∧ R ≤ 1 := by
  dsimp only
  have hp := (SelfCutLengthControl.radius_spec F hε).1
  have hR := (SelfCutLengthControl.radius_spec F hε).2.1
  refine ⟨⟨by linarith, by linarith, by linarith⟩, by linarith, by linarith,
    by linarith, by linarith, hR⟩

end Finsler.CanonicalCutRadiusData
