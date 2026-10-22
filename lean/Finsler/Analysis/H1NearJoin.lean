module

public import Finsler.Analysis.H1OrthogonalEnergy
public import Finsler.Analysis.H1JoinContinuity
public import Finsler.Analysis.H1FiberBase

/-! A genuine continuous near-diagonal join with arbitrarily small additive
cut loss, and its relative correction homotopy. No Thom or cut-chain map is assumed. -/

@[expose] public section

namespace Finsler.H1NearJoin

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy Finsler.H1FiberBase
open Finsler.H1JoinContinuity Finsler.H1OrthogonalEnergy Finsler.BorelLoop Set
open scoped Topology

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

def radius (F : ReversibleMetric n) {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) : ℝ :=
  (exists_homotopy_cut_radius F hq hε).choose

theorem radius_spec (F : ReversibleMetric n) {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    0 < radius F hq hε ∧ radius F hq hε ≤ 1 ∧
      ∀ u : SphereLoop n, u ∈ lev F q → ∀ y : Sphere n,
        dist (y : Ambient n) (basepoint u) < radius F hq hε →
          ∀ s : _root_.unitInterval, hom s u y ∈ lev F (q + ε) :=
  (exists_homotopy_cut_radius F hq hε).choose_spec

def tube (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    Set (lev F p × lev F q) :=
  {z | dist (basepoint z.2.val) (basepoint z.1.val) < radius F hq hε}

def alignmentInput (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : C(tube F p hq hε, nearLoops n) := by
  have hmem (z : tube F p hq hε) : (z.val.2.val, point z.val.1.val) ∈ nearLoops n := by
    change dist (basepoint z.val.1.val) (basepoint z.val.2.val) < 1
    rw [dist_comm]
    exact z.property.trans_le (radius_spec F hq hε).2.1
  refine ⟨fun z => ⟨(z.val.2.val, point z.val.1.val), hmem z⟩, ?_⟩
  have hu : Continuous (fun z : tube F p hq hε => z.val.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hw : Continuous (fun z : tube F p hq hε => z.val.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  exact (hw.prodMk (continuous_point.comp hu)).subtype_mk _

def correctedSecond (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : C(tube F p hq hε, lev F (q + ε)) := by
  have hmem (z : tube F p hq hε) : align z.val.2.val (point z.val.1.val) ∈ lev F (q + ε) := by
    have hd : dist (point z.val.1.val : Ambient n) (basepoint z.val.2.val) < radius F hq hε := by
      change dist (basepoint z.val.1.val) (basepoint z.val.2.val) < _
      rw [dist_comm]
      exact z.property
    simpa only [hom_one] using
      (radius_spec F hq hε).2.2 z.val.2.val z.val.2.property (point z.val.1.val) hd 1
  refine ⟨fun z => ⟨align z.val.2.val (point z.val.1.val), hmem z⟩, ?_⟩
  exact (((alignedMap (n := n)).continuous.comp (alignmentInput F p hq hε).continuous).congr
    (fun z => rfl)).subtype_mk _

theorem corrected_basepoint (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : tube F p hq hε) :
    basepoint ((correctedSecond F p hq hε z).val) = basepoint z.val.1.val :=
  basepoint_align z.val.2.val (point z.val.1.val)

theorem correction_fixed (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : tube F p hq hε)
    (h : basepoint z.val.1.val = basepoint z.val.2.val) :
    (correctedSecond F p hq hε z).val = z.val.2.val := by
  change align z.val.2.val (point z.val.1.val) = z.val.2.val
  simpa only [hom_one] using hom_fixed 1 z.val.2.val (point z.val.1.val) h

def correctedPair (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    C(tube F p hq hε, filteredPair F p (q + ε)) := by
  refine ⟨fun z => ⟨(z.val.1, correctedSecond F p hq hε z),
    (corrected_basepoint F p hq hε z).symm⟩, ?_⟩
  exact ((continuous_fst.comp continuous_subtype_val).prodMk
    (correctedSecond F p hq hε).continuous).subtype_mk _

def nearJoin (F : ReversibleMetric n) {p q ε : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    C(tube F p hq hε, lev F (p + (q + ε))) :=
  (filteredJoin F hp (add_pos hq hε)).comp (correctedPair F p hq hε)

def originalSecond (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) : C(tube F p hq hε, lev F (q + ε)) :=
  ⟨fun z => ⟨z.val.2.val, lev_mono F (le_add_of_nonneg_right hε.le) z.val.2.property⟩,
    (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

def correctionHomotopy (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    (originalSecond F p hq hε).Homotopy (correctedSecond F p hq hε) where
  toFun z := ⟨hom z.1 z.2.val.2.val (point z.2.val.1.val), by
    have hd : dist (point z.2.val.1.val : Ambient n) (basepoint z.2.val.2.val) < radius F hq hε := by
      change dist (basepoint z.2.val.1.val) (basepoint z.2.val.2.val) < _
      rw [dist_comm]
      exact z.2.property
    exact (radius_spec F hq hε).2.2 z.2.val.2.val z.2.val.2.property (point z.2.val.1.val) hd z.1⟩
  continuous_toFun := by
    have hp : Continuous (fun z : _root_.unitInterval × tube F p hq hε =>
        (z.1, alignmentInput F p hq hε z.2)) :=
      continuous_fst.prodMk ((alignmentInput F p hq hε).continuous.comp continuous_snd)
    exact (continuous_hom.comp hp).subtype_mk _
  map_zero_left z := Subtype.ext (hom_zero z.val.2.val (point z.val.1.val))
  map_one_left z := Subtype.ext (hom_one z.val.2.val (point z.val.1.val))

theorem correctionHomotopy_fixed (F : ReversibleMetric n) (p : ℝ) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) (z : tube F p hq hε)
    (h : basepoint z.val.1.val = basepoint z.val.2.val) (s : _root_.unitInterval) :
    (correctionHomotopy F p hq hε (s, z)).val = z.val.2.val :=
  hom_fixed s z.val.2.val (point z.val.1.val) h


end
end Finsler.H1NearJoin
