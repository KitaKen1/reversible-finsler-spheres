module

public import Finsler.Analysis.H1PaddingContinuity
public import Mathlib.Topology.Homotopy.Basic

/-! Remove the actual constant interval in strong H1, staying in the original p+q cut. -/

@[expose] public section

namespace Finsler.FilteredPaddingHomotopy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1ConstantPadding Finsler.H1PaddingContinuity Finsler.H1LoopJoin
open Finsler.H1FiberBase Finsler.BorelLoop Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

def split (p q : ℝ) : ℝ := p / (p + q)

theorem split_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < split p q :=
  div_pos hp (add_pos hp hq)

theorem split_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : split p q < 1 :=
  (div_lt_one (add_pos hp hq)).mpr (by linarith)

def parameter {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : C(_root_.unitInterval, Parameters) :=
  ⟨fun s => ⟨(1 - (s : ℝ)) * split p q, by
    have hs := s.property
    constructor
    · exact mul_nonneg (by linarith [hs.2]) (split_pos hp hq).le
    · have hl : (1 - (s : ℝ)) * split p q ≤ split p q := by
        nlinarith [mul_nonneg hs.1 (split_pos hp hq).le]
      exact hl.trans_lt (split_lt_one hp hq)⟩, by fun_prop⟩

theorem parameter_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (s : _root_.unitInterval) :
    (parameter hp hq s : ℝ) ≤ p / (p + q) := by
  change (1 - (s : ℝ)) * split p q ≤ split p q
  nlinarith [mul_nonneg s.property.1 (split_pos hp hq).le]

def start {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    C(lev F q, lev F (p + q)) :=
  ⟨fun u => ⟨padded (split p q) (split_pos hp hq).le (split_lt_one hp hq) u.val,
    padded_mem_cut F hp hq (split_pos hp hq).le le_rfl u.val u.property⟩,
    ((continuous_padded_fixed (n := n) (split_pos hp hq) (split_lt_one hp hq)).comp
      continuous_subtype_val).subtype_mk _⟩

def inclusion {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    C(lev F q, lev F (p + q)) :=
  ⟨fun u => ⟨u.val, lev_mono F (by linarith) u.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def homotopy {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (start F hp hq).Homotopy (inclusion F hp hq) where
  toFun z := ⟨padded (parameter hp hq z.1) (parameter hp hq z.1).property.1
    (parameter hp hq z.1).property.2 z.2.val,
    padded_mem_cut F hp hq (parameter hp hq z.1).property.1
      (parameter_le hp hq z.1) z.2.val z.2.property⟩
  continuous_toFun := by
    have he : Continuous (fun z : _root_.unitInterval × lev F q =>
        (parameter hp hq z.1, z.2.val)) :=
      ((parameter hp hq).continuous.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact (continuous_padded.comp he).subtype_mk _
  map_zero_left u := by
    apply Subtype.ext
    simp [parameter, start]
  map_one_left u := by
    apply Subtype.ext
    simp [parameter, inclusion, padded_zero]

theorem start_join {n : ℕ} (F : ReversibleMetric n) {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (u : lev F q) :
    (start F hp hq u).val = join (split p q) (split_pos hp hq) (split_lt_one hp hq)
      (constantSphereLoop (point u.val)) u.val (constant_matches u.val) :=
  padded_pos (split_pos hp hq) (split_lt_one hp hq) u.val

end
end Finsler.FilteredPaddingHomotopy

