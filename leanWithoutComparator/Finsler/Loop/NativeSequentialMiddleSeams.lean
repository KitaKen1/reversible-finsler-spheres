module

public import Finsler.Loop.NativeSequentialCutParameters
public import Finsler.Loop.NativeOrderedDoubleCutDiagonal

/-! The two excluded middle-timing seams are NOT discarded. On the
FULL seam families BOTH original middle cuts and common middle loops
pull back the SAME Stage94 genuine GH-power cochains to LITERAL ZERO.
This does not yet supply collar/subdivision gluing across the seams. -/
@[expose] public section
namespace Finsler.NativeSequentialMiddleSeams
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.H1FiberBase
open Finsler.H1SelfCutNeighborhood Finsler.NativeSelfCutSegmentClocks Finsler.NativeSequentialCutParameters
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev radius := NativeClosingArcPowerVanishing.radius m hm F

def prefixSeam : Set (prefixDomain (m + 1) (radius m hm F)) := {z | (z.val.2 : ℝ) = 1}
def suffixSeam : Set (suffixDomain (m + 1) (radius m hm F)) := {z | (z.val.2 : ℝ) = 0}

def prefixArc : TopCat.of (prefixSeam m hm F) ⟶ NativeClosingArcPowerVanishing.domain m hm F :=
  TopCat.ofHom ⟨fun z => (⟨z.val.val.1, z.val.property.1⟩, 0), by fun_prop⟩

def suffixArc : TopCat.of (suffixSeam m hm F) ⟶ NativeClosingArcPowerVanishing.domain m hm F :=
  TopCat.ofHom ⟨fun z => (⟨z.val.val.1, z.val.property.1⟩, 1), by fun_prop⟩

def prefixOriginal : TopCat.of (prefixSeam m hm F) ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => right (prefixInner (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z.val),
    (continuous_right (n := m + 1)).comp ((continuous_prefixInner _).comp continuous_subtype_val)⟩

def suffixOriginal : TopCat.of (suffixSeam m hm F) ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => left (suffixInner (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) z.val),
    (continuous_left (n := m + 1)).comp ((continuous_suffixInner _).comp continuous_subtype_val)⟩

theorem prefix_arc_factor : prefixArc m hm F ≫ NativeClosingArcPowerVanishing.leftRetained m hm F =
    prefixOriginal m hm F := by
  apply TopCat.ext
  intro z
  apply congrArg right
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (1 + (0 : ℝ)) / 2 = (z.val.val.2 : ℝ) / 2
    rw [z.property]
    norm_num
  · rfl

theorem suffix_arc_factor : suffixArc m hm F ≫ NativeClosingArcPowerVanishing.rightTested m hm F =
    suffixOriginal m hm F := by
  apply TopCat.ext
  intro z
  apply congrArg left
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    change (1 : ℝ) / 2 = (1 + (z.val.val.2 : ℝ)) / 2
    rw [z.property]
    norm_num
  · rfl

theorem prefix_original_zero (r : ℕ) : cochainPullback (prefixOriginal m hm F) (NativeGHPowers.degree m r)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) = 0 := by
  rw [← prefix_arc_factor, pullback_comp, NativeClosingArcPowerVanishing.left_literal_zero]
  change (push (prefixArc m hm F)).f _ ≫ 0 = 0
  exact comp_zero

theorem suffix_original_zero (r : ℕ) : cochainPullback (suffixOriginal m hm F) (NativeGHPowers.degree m r)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) = 0 := by
  rw [← suffix_arc_factor, pullback_comp, NativeClosingArcPowerVanishing.right_literal_zero]
  change (push (suffixArc m hm F)).f _ ≫ 0 = 0
  exact comp_zero

theorem prefix_mem_diagonal (z : prefixSeam m hm F) : prefixCommon z.val ∈
    NativeOrderedDoubleCutDiagonal.diagonal (m + 1) (radius m hm F) := by
  apply Subtype.ext
  change (z.val.val.1.val.1 : ℝ) * z.val.val.2 = (z.val.val.1.val.1 : ℝ)
  rw [z.property, mul_one]

theorem suffix_mem_diagonal (z : suffixSeam m hm F) : suffixCommon z.val ∈
    NativeOrderedDoubleCutDiagonal.diagonal (m + 1) (radius m hm F) := by
  apply Subtype.ext
  change (z.val.val.1.val.1 : ℝ) = (z.val.val.1.val.1 : ℝ) + (1 - z.val.val.1.val.1) * z.val.val.2
  rw [z.property, mul_zero, add_zero]

def prefixDiagonal : TopCat.of (prefixSeam m hm F) ⟶
    NativeOrderedDoubleCutDiagonal.diagonalDomain (m + 1) (radius m hm F) := TopCat.ofHom
  ⟨fun z => ⟨prefixCommon z.val, prefix_mem_diagonal m hm F z⟩, by
    have h : Continuous (fun z : prefixSeam m hm F => prefixCommon z.val) :=
      (continuous_prefixCommon (n := m + 1) (r := radius m hm F)).comp continuous_subtype_val
    exact h.subtype_mk _⟩

def suffixDiagonal : TopCat.of (suffixSeam m hm F) ⟶
    NativeOrderedDoubleCutDiagonal.diagonalDomain (m + 1) (radius m hm F) := TopCat.ofHom
  ⟨fun z => ⟨suffixCommon z.val, suffix_mem_diagonal m hm F z⟩, by
    have h : Continuous (fun z : suffixSeam m hm F => suffixCommon z.val) :=
      (continuous_suffixCommon (n := m + 1) (r := radius m hm F)).comp continuous_subtype_val
    exact h.subtype_mk _⟩

def prefixCommonMiddle : TopCat.of (prefixSeam m hm F) ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => NativeOrderedDoubleCutGeometry.middle (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) (prefixCommon z.val),
    (NativeOrderedDoubleCutGeometry.continuous_middle _).comp
      (continuous_prefixCommon.comp continuous_subtype_val)⟩

def suffixCommonMiddle : TopCat.of (suffixSeam m hm F) ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => NativeOrderedDoubleCutGeometry.middle (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) (suffixCommon z.val),
    (NativeOrderedDoubleCutGeometry.continuous_middle _).comp
      (continuous_suffixCommon.comp continuous_subtype_val)⟩

theorem prefix_diagonal_factor : prefixDiagonal m hm F ≫
    NativeOrderedDoubleCutDiagonal.inclusion (m + 1) (radius m hm F) ≫
      NativeOrderedDoubleCutDiagonal.middleMap m hm F = prefixCommonMiddle m hm F := rfl

theorem suffix_diagonal_factor : suffixDiagonal m hm F ≫
    NativeOrderedDoubleCutDiagonal.inclusion (m + 1) (radius m hm F) ≫
      NativeOrderedDoubleCutDiagonal.middleMap m hm F = suffixCommonMiddle m hm F := rfl

theorem prefix_common_zero (r : ℕ) : cochainPullback (prefixCommonMiddle m hm F) (NativeGHPowers.degree m r)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) = 0 := by
  rw [← prefix_diagonal_factor, pullback_comp, NativeOrderedDoubleCutDiagonal.middle_literal_zero]
  change (push (prefixDiagonal m hm F)).f _ ≫ 0 = 0
  exact comp_zero

theorem suffix_common_zero (r : ℕ) : cochainPullback (suffixCommonMiddle m hm F) (NativeGHPowers.degree m r)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) = 0 := by
  rw [← suffix_diagonal_factor, pullback_comp, NativeOrderedDoubleCutDiagonal.middle_literal_zero]
  change (push (suffixDiagonal m hm F)).f _ ≫ 0 = 0
  exact comp_zero

end
end Finsler.NativeSequentialMiddleSeams
