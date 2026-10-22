module

public import Finsler.Analysis.H1RightPadding
public import Finsler.Analysis.FilteredPaddingHomotopy

/-! Terminal constant-interval removal stays in the original p+q cut. -/

@[expose] public section

namespace Finsler.FilteredRightPaddingHomotopy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1RightPadding Finsler.H1LoopJoin Finsler.H1FiberBase Finsler.BorelLoop
open Finsler.FilteredPaddingHomotopy
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

theorem complement_split {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    1 - split q p = split p q := by
  unfold split
  rw [add_comm q p]
  field_simp [(add_pos hp hq).ne'] <;> ring

def start {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    C(lev F p, lev F (p + q)) := by
  have hc : Continuous (fun u : lev F p =>
      H1RightPadding.padded (split q p) (split_pos hq hp).le (split_lt_one hq hp) u.val) := by
    have he : Continuous (fun u : lev F p =>
        ((⟨split q p, (split_pos hq hp).le, split_lt_one hq hp⟩ : H1PaddingContinuity.Parameters), u.val)) :=
      continuous_const.prodMk continuous_subtype_val
    exact H1RightPadding.continuous_padded.comp he
  exact ⟨fun u => ⟨H1RightPadding.padded (split q p) (split_pos hq hp).le (split_lt_one hq hp) u.val,
    H1RightPadding.padded_mem_cut F hp hq (split_pos hq hp).le le_rfl u.val u.property⟩,
    hc.subtype_mk _⟩

def inclusion {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    C(lev F p, lev F (p + q)) :=
  ⟨fun u => ⟨u.val, lev_mono F (by linarith) u.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def homotopy {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (start F hp hq).Homotopy (inclusion F hp hq) where
  toFun z := ⟨H1RightPadding.padded (parameter hq hp z.1) (parameter hq hp z.1).property.1
    (parameter hq hp z.1).property.2 z.2.val,
    H1RightPadding.padded_mem_cut F hp hq (parameter hq hp z.1).property.1
      (parameter_le hq hp z.1) z.2.val z.2.property⟩
  continuous_toFun := by
    have he : Continuous (fun z : _root_.unitInterval × lev F p =>
        (parameter hq hp z.1, z.2.val)) :=
      ((parameter hq hp).continuous.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (H1RightPadding.continuous_padded.comp he).subtype_mk _
  map_zero_left u := by
    apply Subtype.ext
    simp [parameter, start]
  map_one_left u := by
    apply Subtype.ext
    simp [parameter, inclusion, H1RightPadding.padded_zero]

theorem start_join {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (u : lev F p) :
    (start F hp hq u).val = join (split p q) (split_pos hp hq) (split_lt_one hp hq)
      u.val (constantSphereLoop (point u.val)) (H1ConstantPadding.constant_matches u.val).symm :=
  H1RightPadding.padded_join_at (split p q) (split q p) (split_pos hq hp) (split_lt_one hq hp)
    (split_pos hp hq) (split_lt_one hp hq) (complement_split hp hq) u.val

end
end Finsler.FilteredRightPaddingHomotopy
