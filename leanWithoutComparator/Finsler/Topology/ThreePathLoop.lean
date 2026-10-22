module

public import Finsler.Topology.VariablePathConcat
public import Finsler.Topology.JoinSplitHomotopy

/-! The actual closed H1 loop made from three matching sphere paths.
Both binary splits vary continuously in (0,1), and its length is exactly
the sum of the three path lengths throughout the split homotopy. -/

@[expose] public section
namespace Finsler.ThreePathLoop

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevConcat Finsler.SobolevSpherePath Finsler.CompactH1Alignment
open Finsler.VariableJoinContinuity
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {n : ℕ}

def Data (n : ℕ) : Set (Space n × Space n × Space n) :=
  {z | z.1 ∈ SpherePath n ∧ z.2.1 ∈ SpherePath n ∧ z.2.2 ∈ SpherePath n ∧
    continuousRepresentative z.1 1 = continuousRepresentative z.2.1 0 ∧
    continuousRepresentative z.2.1 1 = continuousRepresentative z.2.2 0 ∧
    continuousRepresentative z.2.2 1 = continuousRepresentative z.1 0}

def firstPair (z : Data n) : VariablePathConcat.Pairs n :=
  ⟨(z.val.1, z.val.2.1), z.property.1, z.property.2.1, z.property.2.2.2.1⟩

theorem continuous_firstPair : Continuous (firstPair (n := n)) :=
  ((continuous_fst.comp continuous_subtype_val).prodMk
    (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

def secondPair (z : Splits × Data n) : VariablePathConcat.Pairs n :=
  ⟨(VariablePathConcat.value (z.1, firstPair z.2), z.2.val.2.2),
    VariablePathConcat.value_mem _, z.2.property.2.2.1,
    (representative_concat_one z.2.val.1 z.2.val.2.1 z.1.property.1 z.1.property.2
      z.2.property.2.2.2.1).trans z.2.property.2.2.2.2.1⟩

theorem continuous_secondPair : Continuous (secondPair (n := n)) := by
  have hu : Continuous (fun z : Splits × Data n => VariablePathConcat.value (z.1, firstPair z.2)) :=
    VariablePathConcat.continuous_value.comp
      (continuous_fst.prodMk (continuous_firstPair.comp continuous_snd))
  have hw : Continuous (fun z : Splits × Data n => z.2.val.2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
  exact (hu.prodMk hw).subtype_mk _

def value (z : (Splits × Splits) × Data n) : Space n :=
  VariablePathConcat.value (z.1.2, secondPair (z.1.1, z.2))

theorem value_mem (z : (Splits × Splits) × Data n) : value z ∈ SpherePath n :=
  VariablePathConcat.value_mem _

theorem continuous_value : Continuous (value (n := n)) :=
  VariablePathConcat.continuous_value.comp
    ((continuous_snd.comp continuous_fst).prodMk
      (continuous_secondPair.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))

theorem value_zero (z : (Splits × Splits) × Data n) :
    continuousRepresentative (value z) 0 = continuousRepresentative z.2.val.1 0 := by
  change continuousRepresentative
    (concat (VariablePathConcat.value (z.1.1, firstPair z.2)) z.2.val.2.2 z.1.2.property.1 z.1.2.property.2) 0 = _
  rw [representative_concat_zero]
  exact representative_concat_zero z.2.val.1 z.2.val.2.1 z.1.1.property.1 z.1.1.property.2

theorem value_one (z : (Splits × Splits) × Data n) :
    continuousRepresentative (value z) 1 = continuousRepresentative z.2.val.2.2 1 :=
  representative_concat_one _ _ z.1.2.property.1 z.1.2.property.2 (secondPair (z.1.1, z.2)).property.2.2

def loop (z : (Splits × Splits) × Data n) : SphereLoop n :=
  ⟨⟨value z, (mem_periodicSubmodule_iff _).mpr
    ((value_one z).trans (z.2.property.2.2.2.2.2.trans (value_zero z).symm))⟩,
    fun t => value_mem z t t.property⟩

theorem loop_zero (z : (Splits × Splits) × Data n) :
    (sphereRepresentative (loop z) 0 : Ambient n) = continuousRepresentative z.2.val.1 0 :=
  value_zero z

theorem continuous_loop : Continuous (loop (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact sphereLoop_tendsto_iff.mpr continuous_value.continuousAt

theorem length_value (F : ReversibleMetric n) (z : (Splits × Splits) × Data n) :
    H1PathLength.length F (value z) = H1PathLength.length F z.2.val.1 +
      H1PathLength.length F z.2.val.2.1 + H1PathLength.length F z.2.val.2.2 := by
  have ho := VariablePathConcat.length_value F (z.1.2, secondPair (z.1.1, z.2))
  have hi := VariablePathConcat.length_value F (z.1.1, firstPair z.2)
  exact ho.trans (congrArg (fun x => x + H1PathLength.length F z.2.val.2.2) hi)

theorem length_loop (F : ReversibleMetric n) (z : (Splits × Splits) × Data n) :
    SobolevLength.length F (loop z) = H1PathLength.length F z.2.val.1 +
      H1PathLength.length F z.2.val.2.1 + H1PathLength.length F z.2.val.2.2 :=
  length_value F z

def loopMap (a b : Splits) : C(Data n, SphereLoop n) :=
  ⟨fun z => loop ((a, b), z), continuous_loop.comp (continuous_const.prodMk continuous_id)⟩

def homotopy (a₀ a₁ b₀ b₁ : Splits) :
    (loopMap (n := n) a₀ b₀).Homotopy (loopMap a₁ b₁) where
  toFun z := loop ((JoinSplitHomotopy.interpolate a₀ a₁ z.1,
    JoinSplitHomotopy.interpolate b₀ b₁ z.1), z.2)
  continuous_toFun := continuous_loop.comp
    ((((JoinSplitHomotopy.continuous_interpolate a₀ a₁).comp continuous_fst).prodMk
      ((JoinSplitHomotopy.continuous_interpolate b₀ b₁).comp continuous_fst)).prodMk continuous_snd)
  map_zero_left z := by
    change loop ((JoinSplitHomotopy.interpolate a₀ a₁ 0, JoinSplitHomotopy.interpolate b₀ b₁ 0), z) = _
    rw [JoinSplitHomotopy.interpolate_zero, JoinSplitHomotopy.interpolate_zero]
    rfl
  map_one_left z := by
    change loop ((JoinSplitHomotopy.interpolate a₀ a₁ 1, JoinSplitHomotopy.interpolate b₀ b₁ 1), z) = _
    rw [JoinSplitHomotopy.interpolate_one, JoinSplitHomotopy.interpolate_one]
    rfl

theorem homotopy_length (F : ReversibleMetric n) (a₀ a₁ b₀ b₁ : Splits)
    (s : _root_.unitInterval) (z : Data n) :
    SobolevLength.length F (homotopy a₀ a₁ b₀ b₁ (s, z)) =
      H1PathLength.length F z.val.1 + H1PathLength.length F z.val.2.1 + H1PathLength.length F z.val.2.2 :=
  length_loop F _

end
end Finsler.ThreePathLoop
