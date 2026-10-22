module

public import Finsler.Analysis.H1BasepointAlignment
public import Finsler.Analysis.H1OrthogonalContinuity

/-! A concrete path from identity to the nearby basepoint rotor.
The smallness radius is uniform in time and in both sphere points. -/

@[expose] public section

namespace Finsler.RotorHomotopy

open Finsler.SphereGeometry Finsler.NearbyRotor
open Set Metric
open scoped Topology RealInnerProductSpace

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def blend (s : _root_.unitInterval) (x y : Ambient n) : Ambient n :=
  (1 - (s : ℝ)) • x + (s : ℝ) • y

theorem blend_self (s : _root_.unitInterval) (x : Ambient n) : blend s x x = x := by
  simp only [blend, ← add_smul, sub_add_cancel, one_smul]

theorem blend_sub (s : _root_.unitInterval) (x y : Ambient n) :
    blend s x y - x = (s : ℝ) • (y - x) := by
  simp only [blend, sub_smul, one_smul, smul_sub]
  abel

theorem blend_dist_le (s : _root_.unitInterval) (x y : Ambient n) :
    dist (blend s x y) x ≤ dist y x := by
  rw [dist_eq_norm, blend_sub, norm_smul,
    Real.norm_of_nonneg s.property.1, dist_eq_norm]
  exact mul_le_of_le_one_left (norm_nonneg _) s.property.2

theorem axis_nonzero (s : _root_.unitInterval) {x y : Ambient n}
    (hx : ‖x‖ = 1) (hxy : dist y x ≤ 1) : x + blend s x y ≠ 0 := by
  have hdist := blend_dist_le s x y
  have hx2 : ‖x + x‖ = 2 := by
    rw [← two_smul ℝ x, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hx, mul_one]
  have ht := norm_add_le (x + blend s x y) (x - blend s x y)
  have he : (x + blend s x y) + (x - blend s x y) = x + x := by abel
  rw [he, hx2] at ht
  have hd : ‖x - blend s x y‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact hdist.trans hxy
  intro h
  rw [h, norm_zero, zero_add] at ht
  linarith

def path (s : _root_.unitInterval) (x y : Ambient n) : Ambient n ≃ₗᵢ[ℝ] Ambient n :=
  rotor x (blend s x y)

theorem path_zero (x y : Ambient n) :
    path 0 x y = LinearIsometryEquiv.refl ℝ (Ambient n) := by
  simpa only [path, blend, show ((0 : _root_.unitInterval) : ℝ) = 0 from rfl, sub_zero, one_smul, zero_smul,
    add_zero] using rotor_self x

theorem path_one (x y : Ambient n) : path 1 x y = rotor x y := by
  simp only [path, blend, show ((1 : _root_.unitInterval) : ℝ) = 1 from rfl,
    sub_self, zero_smul, one_smul, zero_add]

theorem path_self (s : _root_.unitInterval) (x : Ambient n) :
    path s x x = LinearIsometryEquiv.refl ℝ (Ambient n) := by
  rw [path, blend_self, rotor_self]

def nearPathData (n : ℕ) : Set (_root_.unitInterval × (Ambient n × Ambient n)) :=
  {p | ‖p.2.1‖ = 1 ∧ ‖p.2.2‖ = 1 ∧ dist p.2.2 p.2.1 ≤ 1}

theorem nearPathData_compact (n : ℕ) : IsCompact (nearPathData n) := by
  have hc : IsClosed {p : _root_.unitInterval × (Ambient n × Ambient n) |
      dist p.2.2 p.2.1 ≤ 1} := isClosed_le
    ((continuous_snd.comp continuous_snd).dist (continuous_fst.comp continuous_snd))
    continuous_const
  convert (isCompact_univ.prod ((isCompact_sphere (0 : Ambient n) 1).prod
    (isCompact_sphere (0 : Ambient n) 1))).inter_right hc using 1
  ext p
  simp [nearPathData, and_assoc]

theorem path_operator_continuousOn : ContinuousOn
    (fun p : _root_.unitInterval × (Ambient n × Ambient n) =>
      (path p.1 p.2.1 p.2.2).toContinuousLinearMap) (nearPathData n) := by
  have hs : Continuous (fun p : _root_.unitInterval × (Ambient n × Ambient n) =>
      (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun p : _root_.unitInterval × (Ambient n × Ambient n) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hy : Continuous (fun p : _root_.unitInterval × (Ambient n × Ambient n) => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hb : Continuous (fun p : _root_.unitInterval × (Ambient n × Ambient n) =>
      blend p.1 p.2.1 p.2.2) :=
    ((continuous_const.sub hs).smul hx).add (hs.smul hy)
  intro p hp
  have hnonzero : p.2.1 ≠ 0 := by
    intro h
    have he := hp.1
    simp [h] at he
  have h := (rotor_continuousAt hnonzero (axis_nonzero p.1 hp.1 hp.2.2)).comp
    (f := fun q : _root_.unitInterval × (Ambient n × Ambient n) =>
      (q.2.1, blend q.1 q.2.1 q.2.2)) (x := p)
    (hx.prodMk hb).continuousAt
  exact (h.congr (Filter.Eventually.of_forall fun q => rfl)).continuousWithinAt

/-- One radius controls the whole path, uniformly over every sphere point. -/
theorem exists_uniform_path_radius {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : Ambient n, ‖x‖ = 1 → ‖y‖ = 1 → dist y x < ρ →
      ∀ s : _root_.unitInterval,
        ‖(path s x y).toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ := by
  have hu := (nearPathData_compact n).uniformContinuousOn_of_continuous
    path_operator_continuousOn
  obtain ⟨r, hr, hd⟩ := Metric.uniformContinuousOn_iff.mp hu δ hδ
  refine ⟨min 1 r, lt_min zero_lt_one hr, fun x y hx hy hxy s => ?_⟩
  have hp : (s, (x, y)) ∈ nearPathData n :=
    ⟨hx, hy, (hxy.trans_le (min_le_left 1 r)).le⟩
  have hdiag : (s, (x, x)) ∈ nearPathData n := ⟨hx, hx, by simp⟩
  have hdist : dist (s, (x, y)) (s, (x, x)) < r := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist y x),
      max_eq_right (dist_nonneg : 0 ≤ dist y x)] using
      hxy.trans_le (min_le_right 1 r)
  have he := hd _ hp _ hdiag hdist
  have hid : (path s x x).toContinuousLinearMap = ContinuousLinearMap.id ℝ (Ambient n) := by
    rw [path_self]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  simpa only [hid, dist_eq_norm] using he


end
end Finsler.RotorHomotopy
