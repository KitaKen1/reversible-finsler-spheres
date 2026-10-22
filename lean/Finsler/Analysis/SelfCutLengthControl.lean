module

public import Finsler.Analysis.H1SelfCutNeighborhood

/-! The pointwise length saving of the actual short-arc self-cut. The
whole-parent conclusion for a nonzero cocycle face still requires adequate
subdivision and oscillation control; it is not an input silently assumed here. -/

@[expose] public section
namespace Finsler.SelfCutLengthControl

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevLength
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

def radius (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) : ℝ :=
  (exists_length_control F hε).choose

theorem radius_spec (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    0 < radius F hε ∧ radius F hε ≤ 1 ∧ ∀ z : tube n,
      ‖(endpoint z.val : Ambient n) - (point z.val.2 : Ambient n)‖ < radius F hε →
        length F (left z) + length F (right z) < length F z.val.2 + 2 * ε :=
  (exists_length_control F hε).choose_spec

theorem retained_lt (F : ReversibleMetric n) {ε L : ℝ} (hε : 0 < ε) (z : tube n)
    (hz : ‖(endpoint z.val : Ambient n) - (point z.val.2 : Ambient n)‖ < radius F hε)
    (htest : L ≤ length F (left z)) :
    length F (right z) < length F z.val.2 - L + 2 * ε := by
  have h := (radius_spec F hε).2.2 z hz
  linarith

theorem filtered_retained_lt (F : ReversibleMetric n) {ε a L : ℝ} (hε : 0 < ε)
    (z : tube n)
    (hz : ‖(endpoint z.val : Ambient n) - (point z.val.2 : Ambient n)‖ < radius F hε)
    (ha : length F z.val.2 < a) (htest : L - ε ≤ length F (left z)) :
    length F (right z) < a - L + 3 * ε := by
  have h := retained_lt F hε z hz htest
  linarith

theorem no_surviving_if_nonpos (F : ReversibleMetric n) {ε a L : ℝ} (hε : 0 < ε)
    (hbound : a - L + 3 * ε ≤ 0) (z : tube n)
    (hz : ‖(endpoint z.val : Ambient n) - (point z.val.2 : Ambient n)‖ < radius F hε)
    (ha : length F z.val.2 < a) (htest : L - ε ≤ length F (left z)) : False := by
  have h := filtered_retained_lt F hε z hz ha htest
  have h0 := length_nonneg F (right z)
  linarith

def surviving (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) (a L : ℝ) : Set (tube n) :=
  {z | ‖(endpoint z.val : Ambient n) - (point z.val.2 : Ambient n)‖ < radius F hε ∧
    length F z.val.2 < a ∧ L - ε ≤ length F (left z)}

def retainedMap (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) (a L : ℝ) :
    C(surviving F hε a L, {u : SphereLoop n | length F u < a - L + 3 * ε}) :=
  ⟨fun z => ⟨right z.val, filtered_retained_lt F hε z.val
    z.property.1 z.property.2.1 z.property.2.2⟩,
    (continuous_right.comp continuous_subtype_val).subtype_mk _⟩

end
end Finsler.SelfCutLengthControl
