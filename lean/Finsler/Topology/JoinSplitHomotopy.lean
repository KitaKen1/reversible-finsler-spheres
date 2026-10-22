module

public import Finsler.Topology.VariableJoinContinuity

/-! The actual fixed-split join is homotopic to the half-time join.
Every intermediate loop has exactly the sum of the input lengths, so this
is also an actual homotopy on the original H1 length sublevels. -/

@[expose] public section
namespace Finsler.JoinSplitHomotopy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1JoinContinuity
open Finsler.VariableJoinContinuity
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

variable {n : ℕ}

def interpolate (a b : Splits) (s : _root_.unitInterval) : Splits :=
  ⟨(1 - (s : ℝ)) * a + (s : ℝ) * b, by
    simpa only [smul_eq_mul] using (convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1)
      a.property b.property (sub_nonneg.mpr s.property.2) s.property.1
      (sub_add_cancel 1 (s : ℝ))⟩

theorem interpolate_zero (a b : Splits) : interpolate a b 0 = a := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) * a + (0 : ℝ) * b = a
  simp

theorem interpolate_one (a b : Splits) : interpolate a b 1 = b := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) * a + (1 : ℝ) * b = b
  simp

theorem continuous_interpolate (a b : Splits) : Continuous (interpolate a b) :=
  (((continuous_const.sub continuous_subtype_val).mul continuous_const).add
    (continuous_subtype_val.mul continuous_const)).subtype_mk _

def homotopy (a b : Splits) :
    (joinMap (n := n) a a.property.1 a.property.2).Homotopy
      (joinMap b b.property.1 b.property.2) where
  toFun z := value (interpolate a b z.1, z.2)
  continuous_toFun := continuous_value.comp
    (((continuous_interpolate a b).comp continuous_fst).prodMk continuous_snd)
  map_zero_left z := congrArg (fun c : Splits => value (c, z)) (interpolate_zero a b)
  map_one_left z := congrArg (fun c : Splits => value (c, z)) (interpolate_one a b)

theorem length_value (F : ReversibleMetric n) (z : Splits × composable n) :
    SobolevLength.length F (value z) =
      SobolevLength.length F z.2.val.1 + SobolevLength.length F z.2.val.2 :=
  H1PathLength.length_concat F (z.2.val.1.data : Space n) (z.2.val.2.data : Space n)
    z.1.property.1 z.1.property.2 (SobolevSpherePath.sphereLoop_mem z.2.val.1)
    (SobolevSpherePath.sphereLoop_mem z.2.val.2) (end_match z.2.val.1 z.2.val.2 z.2.property)

theorem homotopy_length (F : ReversibleMetric n) (a b : Splits)
    (s : _root_.unitInterval) (z : composable n) :
    SobolevLength.length F (homotopy a b (s, z)) =
      SobolevLength.length F z.val.1 + SobolevLength.length F z.val.2 :=
  length_value F (interpolate a b s, z)

def lengthPairs (F : ReversibleMetric n) (p q : ℝ) : Set (composable n) :=
  {z | SobolevLength.length F z.val.1 < p ∧ SobolevLength.length F z.val.2 < q}

def lengthTarget (F : ReversibleMetric n) (p q : ℝ) : Set (SphereLoop n) :=
  {u | SobolevLength.length F u < p + q}

def filteredMap (F : ReversibleMetric n) (p q : ℝ) (a : Splits) :
    C(lengthPairs F p q, lengthTarget F p q) :=
  ⟨fun z => ⟨value (a, z.val), by
      change SobolevLength.length F (value (a, z.val)) < p + q
      rw [length_value]
      exact add_lt_add z.property.1 z.property.2⟩, by
    have h : Continuous (fun z : lengthPairs F p q => value (a, z.val)) :=
      continuous_value.comp (continuous_const.prodMk continuous_subtype_val)
    exact h.subtype_mk _⟩

def filteredHomotopy (F : ReversibleMetric n) (p q : ℝ) (a b : Splits) :
    (filteredMap F p q a).Homotopy (filteredMap F p q b) where
  toFun z := ⟨homotopy a b (z.1, z.2.val), by
    change SobolevLength.length F (homotopy a b (z.1, z.2.val)) < p + q
    rw [homotopy_length]
    exact add_lt_add z.2.property.1 z.2.property.2⟩
  continuous_toFun := by
    have h : Continuous (fun z : _root_.unitInterval × lengthPairs F p q =>
        homotopy a b (z.1, z.2.val)) := (homotopy a b).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_mk _
  map_zero_left z := Subtype.ext ((homotopy a b).map_zero_left z.val)
  map_one_left z := Subtype.ext ((homotopy a b).map_one_left z.val)

def half : Splits := ⟨1 / 2, by norm_num⟩

def toHalf (a : Splits) := homotopy (n := n) a half

def filteredToHalf (F : ReversibleMetric n) (p q : ℝ) (a : Splits) :=
  filteredHomotopy F p q a half

end
end Finsler.JoinSplitHomotopy
