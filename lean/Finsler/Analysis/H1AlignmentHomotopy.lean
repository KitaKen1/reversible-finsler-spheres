module

public import Finsler.Geometry.RotorHomotopy
public import Finsler.Analysis.CompactH1Alignment
public import Mathlib.Topology.Homotopy.Basic

/-! A relative basepoint-correction homotopy on the actual strong H¹ loop space.
The entire homotopy has arbitrarily small additive length cost on a fixed
bounded family. Loops already based at the target remain fixed. -/

@[expose] public section

namespace Finsler.H1AlignmentHomotopy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.NearbyRotor Finsler.RotorHomotopy Finsler.CompactH1Alignment
open Finsler.H1OrthogonalLength Finsler.H1OrthogonalContinuity Finsler.SobolevLength
open Set
open scoped Topology

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem basepoint_continuous : Continuous (basepoint : SphereLoop n → Ambient n) := by
  exact (traceL n ⟨0, by norm_num⟩).continuous.comp (sphereLoop_data_isometry n).continuous

def hom (s : _root_.unitInterval) (u : SphereLoop n) (y : Sphere n) : SphereLoop n :=
  rotateLoop (path s (basepoint u) (y : Ambient n)) u

theorem hom_zero (u : SphereLoop n) (y : Sphere n) : hom 0 u y = u := by
  rw [hom, path_zero, rotateLoop_refl]

theorem hom_one (u : SphereLoop n) (y : Sphere n) : hom 1 u y = align u y := by
  rw [hom, path_one]
  rfl

theorem hom_fixed (s : _root_.unitInterval) (u : SphereLoop n) (y : Sphere n)
    (hy : (y : Ambient n) = basepoint u) : hom s u y = u := by
  rw [hom, hy, path_self, rotateLoop_refl]

theorem hom_end_basepoint (u : SphereLoop n) (y : Sphere n) :
    basepoint (hom 1 u y) = (y : Ambient n) := by
  change continuousRepresentative
    (rotateData (path 1 (basepoint u) (y : Ambient n)) (u.data : Space n)) 0 = _
  rw [representative_rotateData _ _ (by norm_num : (0 : ℝ) ∈ Icc 0 1), path_one]
  have hy : ‖(y : Ambient n)‖ = 1 := by simpa using y.property
  exact rotor_map ((u.sphere_constraint ⟨0, by norm_num⟩).trans hy.symm)

def nearLoops (n : ℕ) : Set (SphereLoop n × Sphere n) :=
  {p | dist (p.2 : Ambient n) (basepoint p.1) < 1}

theorem continuous_hom : Continuous (fun p : _root_.unitInterval × nearLoops n =>
    hom p.1 p.2.val.1 p.2.val.2) := by
  have hu : Continuous (fun p : _root_.unitInterval × nearLoops n => p.2.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  have hy : Continuous (fun p : _root_.unitInterval × nearLoops n =>
      (p.2.val.2 : Ambient n)) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
  have hb : Continuous (fun p : _root_.unitInterval × nearLoops n =>
      basepoint p.2.val.1) := basepoint_continuous.comp hu
  have ht : Continuous (fun p : _root_.unitInterval × nearLoops n => p.1) := continuous_fst
  have hp : Continuous (fun p : _root_.unitInterval × nearLoops n =>
      (p.1, (basepoint p.2.val.1, (p.2.val.2 : Ambient n)))) := by
    exact ht.prodMk (hb.prodMk hy)
  have hA : Continuous (fun p : _root_.unitInterval × nearLoops n =>
      (path p.1 (basepoint p.2.val.1) (p.2.val.2 : Ambient n)).toContinuousLinearMap) := by
    have hc : ContinuousOn (fun q : _root_.unitInterval × (Ambient n × Ambient n) =>
        (path q.1 q.2.1 q.2.2).toContinuousLinearMap) (nearPathData n) :=
      path_operator_continuousOn (n := n)
    have hmem : ∀ p : _root_.unitInterval × nearLoops n,
        (p.1, (basepoint p.2.val.1, (p.2.val.2 : Ambient n))) ∈ nearPathData n := by
      intro p
      exact ⟨p.2.val.1.sphere_constraint ⟨0, by norm_num⟩,
        by simpa using p.2.val.2.property, p.2.property.le⟩
    exact (hc.comp_continuous hp hmem).congr (fun p => rfl)
  exact continuous_rotateLoop_family
    (fun p : _root_.unitInterval × nearLoops n =>
      path p.1 (basepoint p.2.val.1) (p.2.val.2 : Ambient n)) hA
    (fun p => p.2.val.1) hu

def initialMap : C(nearLoops n, SphereLoop n) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

def alignedMap : C(nearLoops n, SphereLoop n) :=
  ⟨fun p => align p.val.1 p.val.2, by
    have h := continuous_hom.comp
      ((continuous_const : Continuous (fun _ : nearLoops n => (1 : _root_.unitInterval))).prodMk
        (continuous_id : Continuous (fun p : nearLoops n => p)))
    exact h.congr (fun p => hom_one p.val.1 p.val.2)⟩

/-- An actual continuous-map homotopy, stationary wherever correction is unnecessary. -/
def alignmentHomotopy : (initialMap (n := n)).Homotopy alignedMap where
  toFun p := hom p.1 p.2.val.1 p.2.val.2
  continuous_toFun := continuous_hom
  map_zero_left p := hom_zero p.val.1 p.val.2
  map_one_left p := hom_one p.val.1 p.val.2

/-- The same radius controls every intermediate loop, after M is fixed. -/
theorem exists_length_control (F : ReversibleMetric n) (M : ℝ) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ (u : SphereLoop n) (y : Sphere n),
      dist (y : Ambient n) (basepoint u) < ρ → length F u ≤ M →
      ∀ s : _root_.unitInterval, |length F (hom s u y) - length F u| < ε := by
  obtain ⟨δ, hδ, hd⟩ := exists_additive_length_control F M hM hε
  obtain ⟨ρ, hρ, hrot⟩ := exists_uniform_path_radius (n := n) hδ
  refine ⟨min 1 ρ, lt_min zero_lt_one hρ, min_le_left 1 ρ,
    fun u y hy hlen s => ?_⟩
  apply hd _ ?_ u hlen
  exact hrot _ _ (u.sphere_constraint ⟨0, by norm_num⟩)
    (by simpa using y.property) (hy.trans_le (min_le_right 1 ρ)) s

/-- Compact-family bounds are chosen before the common homotopy radius. -/
theorem exists_compact_control (F : ReversibleMetric n) {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (u : X → SphereLoop n) (hu : ContinuousOn u K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x ∈ K, length F (u x) ≤ M) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x ∈ K, ∀ y : Sphere n,
        dist (y : Ambient n) (basepoint (u x)) < ρ →
        ∀ s : _root_.unitInterval, |length F (hom s (u x) y) - length F (u x)| < ε := by
  obtain ⟨M, hM, hb⟩ := exists_length_bound F hK u hu
  obtain ⟨ρ, hρ, hρ1, hd⟩ := exists_length_control F M hM hε
  exact ⟨M, hM, hb, ρ, hρ, hρ1, fun x hx y hy => hd (u x) y hy (hb x hx)⟩


end
end Finsler.H1AlignmentHomotopy
