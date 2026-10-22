module

public import Finsler.Loop.CompactZeroTubeControl
public import Finsler.Loop.OrthogonalSelfCutDistance
public import Finsler.Analysis.H1AlignmentHomotopy
public import Finsler.Analysis.SelfCutOscillation

/-! On a compact closed proper cut tube, both actual cut-loop lengths
vary uniformly little under every sufficiently small partial basepoint
correction. Only continuity of the canonical cut maps and exact round
distance preservation are needed; no short-arc equivariance is assumed. -/

@[expose] public section
namespace Finsler.CompactRotatedCutData

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.H1FiberBase Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy
open Finsler.H1OrthogonalLength Finsler.H1SelfCutNeighborhood Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

local instance (n : ℕ) : CompactSpace (Sphere n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient n) 1)

variable {P : Type} [PseudoMetricSpace P] {n : ℕ} (α : C(P, SphereLoop n)) (r : ℝ)

def source : Set (ClosedInterval × P) := {z | distance n (z.1, α z.2) ≤ r}

theorem source_compactSpace [CompactSpace P] : CompactSpace (source α r) := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  exact isClosed_le ((continuous_distance n).comp (continuous_fst.prodMk (α.continuous.comp continuous_snd))) continuous_const

attribute [local instance] source_compactSpace

def data : Set (_root_.unitInterval × (source α r × Sphere n)) :=
  {z | dist (z.2.2 : Ambient n) (basepoint (α z.2.1.val.2)) ≤ 1 / 2}

theorem data_compactSpace [CompactSpace P] : CompactSpace (data α r) := by
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  have hf : Continuous (fun z : _root_.unitInterval × (source α r × Sphere n) => α z.2.1.val.2) := by fun_prop
  have hy : Continuous (fun z : _root_.unitInterval × (source α r × Sphere n) => (z.2.2 : Ambient n)) := by fun_prop
  exact isClosed_le (hy.dist (basepoint_continuous.comp hf)) continuous_const

attribute [local instance] data_compactSpace

def nearData : C(data α r, H1AlignmentHomotopy.nearLoops n) := by
  let f : C(data α r, SphereLoop n) := ⟨fun z => α z.val.2.1.val.2, by fun_prop⟩
  let g : C(data α r, Sphere n) := ⟨fun z => z.val.2.2, by fun_prop⟩
  have hn (z : data α r) : (f z, g z) ∈ H1AlignmentHomotopy.nearLoops n := by
    change dist (z.val.2.2 : Ambient n) (basepoint (α z.val.2.1.val.2)) < 1
    exact z.property.trans_lt (by norm_num)
  exact ⟨fun z => ⟨(f z, g z), hn z⟩, (f.continuous.prodMk g.continuous).subtype_mk hn⟩

def rotatingLoop : C(data α r, SphereLoop n) :=
  (H1AlignmentHomotopy.alignmentHomotopy (n := n)).toContinuousMap.comp
    (show C(data α r, _root_.unitInterval × H1AlignmentHomotopy.nearLoops n) from
      ⟨fun z => (z.val.1, nearData α r z), by
        exact (show Continuous (fun z : data α r => z.val.1) by fun_prop).prodMk (nearData α r).continuous⟩)

def originalCut (hr : r < 1) : C(data α r, H1SelfCutNeighborhood.tube n) := by
  have ht : Continuous (fun z : data α r => z.val.2.1.val.1) := by fun_prop
  have hf : Continuous (fun z : data α r => α z.val.2.1.val.2) := by fun_prop
  have hmem (z : data α r) : (z.val.2.1.val.1, α z.val.2.1.val.2) ∈ H1SelfCutNeighborhood.tube n :=
    z.val.2.1.property.trans_lt hr
  exact ⟨fun z => ⟨(z.val.2.1.val.1, α z.val.2.1.val.2), hmem z⟩, (ht.prodMk hf).subtype_mk hmem⟩

def rotatingCut (hr : r < 1) : C(data α r, H1SelfCutNeighborhood.tube n) := by
  have ht : Continuous (fun z : data α r => z.val.2.1.val.1) := by fun_prop
  have hmem (z : data α r) : (z.val.2.1.val.1, rotatingLoop α r z) ∈ H1SelfCutNeighborhood.tube n := by
    change distance n (z.val.2.1.val.1, rotatingLoop α r z) < 1
    change distance n (z.val.2.1.val.1,
      rotateLoop (RotorHomotopy.path z.val.1 (basepoint (α z.val.2.1.val.2)) z.val.2.2) (α z.val.2.1.val.2)) < 1
    rw [OrthogonalSelfCutDistance.distance]
    exact z.val.2.1.property.trans_lt hr
  exact ⟨fun z => ⟨(z.val.2.1.val.1, rotatingLoop α r z), hmem z⟩,
    (ht.prodMk (rotatingLoop α r).continuous).subtype_mk hmem⟩

def gap (z : data α r) : ℝ := dist (z.val.2.2 : Ambient n) (basepoint (α z.val.2.1.val.2))

theorem continuous_gap : Continuous (gap α r) := by
  have hf : Continuous (fun z : data α r => α z.val.2.1.val.2) := by fun_prop
  have hy : Continuous (fun z : data α r => (z.val.2.2 : Ambient n)) := by fun_prop
  exact hy.dist (basepoint_continuous.comp hf)

theorem cut_eq_of_gap_zero (hr : r < 1) (z : data α r) (hz : gap α r z = 0) :
    rotatingCut α r hr z = originalCut α r hr z := by
  have hy : (z.val.2.2 : Ambient n) = basepoint (α z.val.2.1.val.2) := dist_eq_zero.mp hz
  have he : rotatingLoop α r z = α z.val.2.1.val.2 := H1AlignmentHomotopy.hom_fixed _ _ _ hy
  apply Subtype.ext
  exact Prod.ext rfl he

def discrepancy (hr : r < 1) (F : ReversibleMetric n) (z : data α r) : ℝ :=
  max |SobolevLength.length F (left (rotatingCut α r hr z)) - SobolevLength.length F (left (originalCut α r hr z))|
      |SobolevLength.length F (right (rotatingCut α r hr z)) - SobolevLength.length F (right (originalCut α r hr z))|

theorem continuous_discrepancy (hr : r < 1) (F : ReversibleMetric n) : Continuous (discrepancy α r hr F) := by
  have hrot₁ := (SelfCutOscillation.continuous_length F).comp (continuous_left.comp (rotatingCut α r hr).continuous)
  have horig₁ := (SelfCutOscillation.continuous_length F).comp (continuous_left.comp (originalCut α r hr).continuous)
  have hrot₂ := (SelfCutOscillation.continuous_length F).comp (continuous_right.comp (rotatingCut α r hr).continuous)
  have horig₂ := (SelfCutOscillation.continuous_length F).comp (continuous_right.comp (originalCut α r hr).continuous)
  exact (hrot₁.sub horig₁).abs.max ((hrot₂.sub horig₂).abs)

theorem discrepancy_zero (hr : r < 1) (F : ReversibleMetric n) (z : data α r) (hz : gap α r z = 0) :
    discrepancy α r hr F z = 0 := by
  rw [discrepancy, cut_eq_of_gap_zero α r hr z hz, sub_self, sub_self, abs_zero, max_self]

theorem exists_cut_length_control [CompactSpace P] (hr : r < 1) (F : ReversibleMetric n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ 1 / 2 ∧ ∀ z : data α r, gap α r z < ρ →
      |SobolevLength.length F (left (rotatingCut α r hr z)) - SobolevLength.length F (left (originalCut α r hr z))| < ε ∧
      |SobolevLength.length F (right (rotatingCut α r hr z)) - SobolevLength.length F (right (originalCut α r hr z))| < ε := by
  obtain ⟨ρ, hρ, hbound⟩ := CompactZeroTubeControl.exists_radius (gap α r) (discrepancy α r hr F)
    (continuous_gap α r) (continuous_discrepancy α r hr F) (fun z => dist_nonneg)
    (discrepancy_zero α r hr F) hε
  refine ⟨min ρ (1 / 2), lt_min hρ (by norm_num), min_le_right _ _, ?_⟩
  intro z hz
  have hb := hbound z (hz.trans_le (min_le_left _ _))
  have hm : discrepancy α r hr F z < ε := (le_abs_self _).trans_lt hb
  exact ⟨(le_max_left _ _).trans_lt hm, (le_max_right _ _).trans_lt hm⟩

end
end Finsler.CompactRotatedCutData
