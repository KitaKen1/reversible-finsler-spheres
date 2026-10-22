module

public import Finsler.Analysis.H1NearJoin
public import Finsler.Analysis.H1PathLength

/-! Compare correction of the second input with correction of the first
input by a genuine global rotation of the joined loop. The split is fixed
in (0,1); changing that split to the paper's half-time join is separate. -/

@[expose] public section
namespace Finsler.JoinDirectionComparison

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy Finsler.H1FiberBase
open Finsler.H1OrthogonalLength Finsler.H1OrthogonalContinuity Finsler.NearbyRotor
open Finsler.H1LoopJoin Finsler.H1JoinContinuity Finsler.SobolevConcat Finsler.SobolevEnergy
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000

variable {n : ℕ}

theorem basepoint_rotate (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u : SphereLoop n) :
    basepoint (rotateLoop A u) = A (basepoint u) :=
  representative_rotateData A (u.data : Space n) (by norm_num : (0 : ℝ) ∈ Icc 0 1)

theorem rotate_join (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (u v : SphereLoop n) (h : basepoint u = basepoint v) :
    rotateLoop A (join a ha0 ha1 u v h) =
      join a ha0 ha1 (rotateLoop A u) (rotateLoop A v)
        (by rw [basepoint_rotate, basepoint_rotate, h]) := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (rotateData A (concat (u.data : Space n) (v.data : Space n) ha0 ha1)) t =
    continuousRepresentative (concat (rotateData A (u.data : Space n))
      (rotateData A (v.data : Space n)) ha0 ha1) t
  rw [representative_rotateData A _ t.property]
  by_cases ht : (t : ℝ) ≤ a
  · rw [representative_concat_left _ _ ha0 ha1 ⟨t.property.1, ht⟩,
      representative_concat_left _ _ ha0 ha1 ⟨t.property.1, ht⟩]
    exact (representative_rotateData A (u.data : Space n)
      (H1ConcatContinuity.left_time_mem ha0 t.property ht)).symm
  · have hge : a ≤ (t : ℝ) := (lt_of_not_ge ht).le
    have hm : continuousRepresentative (rotateData A (u.data : Space n)) 1 =
        continuousRepresentative (rotateData A (v.data : Space n)) 0 := by
      exact (representative_rotateData A (u.data : Space n) (by norm_num : (1 : ℝ) ∈ Icc 0 1)).trans
        ((congrArg A (end_match u v h)).trans
          (representative_rotateData A (v.data : Space n) (by norm_num : (0 : ℝ) ∈ Icc 0 1)).symm)
    rw [representative_concat_right _ _ ha0 ha1 (end_match u v h) ⟨hge, t.property.2⟩,
      representative_concat_right _ _ ha0 ha1 hm ⟨hge, t.property.2⟩]
    exact (representative_rotateData A (v.data : Space n)
      (H1ConcatContinuity.right_time_mem ha1 t.property hge)).symm

def secondJoin (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (u v : SphereLoop n) : SphereLoop n :=
  join a ha0 ha1 u (align v (point u)) (basepoint_align v (point u)).symm

def firstJoin (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (u v : SphereLoop n) : SphereLoop n :=
  join a ha0 ha1 (align u (point v)) v (basepoint_align u (point v))

theorem basepoint_secondJoin (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (u v : SphereLoop n) :
    basepoint (secondJoin a ha0 ha1 u v) = basepoint u :=
  basepoint_join a ha0 ha1 u (align v (point u)) _

theorem align_secondJoin (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (u v : SphereLoop n) :
    align (secondJoin a ha0 ha1 u v) (point v) = firstJoin a ha0 ha1 u v := by
  change rotateLoop (rotor (basepoint (secondJoin a ha0 ha1 u v)) (point v : Ambient n))
    (join a ha0 ha1 u (align v (point u)) _) = _
  rw [basepoint_secondJoin, rotate_join]
  have he : rotateLoop (rotor (basepoint u) (point v : Ambient n)) (align v (point u)) = v := by
    have h := align_reverse v (point u)
    change rotateLoop (rotor (basepoint (align v (point u))) (point v : Ambient n))
      (align v (point u)) = v at h
    rw [basepoint_align] at h
    exact h
  simp only [he]
  rfl

def nearPairs (n : ℕ) : Set (SphereLoop n × SphereLoop n) :=
  {z | dist (basepoint z.1) (basepoint z.2) < 1}

def secondPair : C(nearPairs n, composable n) :=
  ⟨fun z => ⟨(z.val.1, align z.val.2 (point z.val.1)), by
    change basepoint z.val.1 = basepoint (align z.val.2 (point z.val.1))
    exact (basepoint_align z.val.2 (point z.val.1)).symm⟩, by
    have hi : Continuous (fun z : nearPairs n =>
        (⟨(z.val.2, point z.val.1), z.property⟩ : nearLoops n)) :=
      ((continuous_snd.comp continuous_subtype_val).prodMk
        (continuous_point.comp (continuous_fst.comp continuous_subtype_val))).subtype_mk _
    exact (((continuous_fst.comp continuous_subtype_val).prodMk
      ((alignedMap (n := n)).continuous.comp hi)).congr (fun z => rfl)).subtype_mk _⟩

def secondMap (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : C(nearPairs n, SphereLoop n) :=
  ⟨fun z => secondJoin a ha0 ha1 z.val.1 z.val.2, by
    exact (((joinMap a ha0 ha1).comp secondPair).continuous).congr (fun z => rfl)⟩

def firstPair : C(nearPairs n, composable n) :=
  ⟨fun z => ⟨(align z.val.1 (point z.val.2), z.val.2), by
    change basepoint (align z.val.1 (point z.val.2)) = basepoint z.val.2
    exact basepoint_align z.val.1 (point z.val.2)⟩, by
    have hi : Continuous (fun z : nearPairs n =>
        (⟨(z.val.1, point z.val.2), by
          change dist (basepoint z.val.2) (basepoint z.val.1) < 1
          rw [dist_comm]
          exact z.property⟩ : nearLoops n)) :=
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_point.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
    exact ((((alignedMap (n := n)).continuous.comp hi).prodMk
      (continuous_snd.comp continuous_subtype_val)).congr (fun z => rfl)).subtype_mk _⟩

def firstMap (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) : C(nearPairs n, SphereLoop n) :=
  ⟨fun z => firstJoin a ha0 ha1 z.val.1 z.val.2, by
    exact (((joinMap a ha0 ha1).comp firstPair).continuous).congr (fun z => rfl)⟩

def comparison (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (secondMap (n := n) a ha0 ha1).Homotopy (firstMap a ha0 ha1) where
  toFun z := hom z.1 (secondMap a ha0 ha1 z.2) (point z.2.val.2)
  continuous_toFun := by
    have hi : Continuous (fun z : nearPairs n =>
        (⟨(secondMap a ha0 ha1 z, point z.val.2), by
          change dist (basepoint z.val.2) (basepoint (secondJoin a ha0 ha1 z.val.1 z.val.2)) < 1
          rw [basepoint_secondJoin, dist_comm]
          exact z.property⟩ : nearLoops n)) :=
      ((secondMap a ha0 ha1).continuous.prodMk
        (continuous_point.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
    have hp : Continuous (fun z : _root_.unitInterval × nearPairs n =>
        (z.1, (⟨(secondMap a ha0 ha1 z.2, point z.2.val.2), by
          change dist (basepoint z.2.val.2)
            (basepoint (secondJoin a ha0 ha1 z.2.val.1 z.2.val.2)) < 1
          rw [basepoint_secondJoin, dist_comm]
          exact z.2.property⟩ : nearLoops n))) :=
      continuous_fst.prodMk (hi.comp continuous_snd)
    exact (continuous_hom.comp hp).congr (fun z => rfl)
  map_zero_left z := by
    change hom 0 (secondJoin a ha0 ha1 z.val.1 z.val.2) (point z.val.2) = _
    exact hom_zero _ _
  map_one_left z := by
    change hom 1 (secondJoin a ha0 ha1 z.val.1 z.val.2) (point z.val.2) = _
    exact (hom_one _ _).trans (align_secondJoin a ha0 ha1 z.val.1 z.val.2)

theorem exists_comparison_length_radius (F : ReversibleMetric n) (M : ℝ) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (z : nearPairs n),
      dist (basepoint z.val.1) (basepoint z.val.2) < ρ →
      SobolevLength.length F (secondJoin a ha0 ha1 z.val.1 z.val.2) ≤ M →
      ∀ s : _root_.unitInterval,
        |SobolevLength.length F (comparison a ha0 ha1 (s, z)) -
          SobolevLength.length F (secondJoin a ha0 ha1 z.val.1 z.val.2)| < ε := by
  obtain ⟨ρ, hρ, hρ1, hbound⟩ := H1AlignmentHomotopy.exists_length_control F M hM hε
  refine ⟨ρ, hρ, hρ1, fun a ha0 ha1 z hz hlen s => ?_⟩
  apply hbound (secondJoin a ha0 ha1 z.val.1 z.val.2) (point z.val.2) _ hlen s
  change dist (basepoint z.val.2) (basepoint (secondJoin a ha0 ha1 z.val.1 z.val.2)) < ρ
  rw [basepoint_secondJoin, dist_comm]
  exact hz

end
end Finsler.JoinDirectionComparison
