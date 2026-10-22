module

public import Finsler.Loop.UniversalTimeTriangle

/-! Ordered raw-segment clocks 0<=s<=t<=1. The two nested
clocks are (tu,t) and (s,s+(1-s)u). Explicit homotopies to the min/max
folds keep EVERY boundary point fixed. Collapsed diagonal pieces
are retained. Identification with the original closed cut loops,
including their closing arcs, is NOT asserted here. -/
@[expose] public section
namespace Finsler.OrderedDoubleCutTimes
open CategoryTheory Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

abbrev square : TopCat.{0} := TopCat.of (TopCat.I.{0} × TopCat.I.{0})
abbrev space : TopCat.{0} := TopCat.of {z : TopCat.I.{0} × TopCat.I.{0} | z.1.down ≤ z.2.down}

def leftClock : square ⟶ space := TopCat.ofHom
  ⟨fun z => ⟨(ULift.up ⟨(z.1.down : ℝ) * z.2.down, ⟨mul_nonneg z.1.down.property.1 z.2.down.property.1,
    (mul_le_of_le_one_right z.1.down.property.1 z.2.down.property.2).trans z.1.down.property.2⟩⟩, z.1),
      mul_le_of_le_one_right z.1.down.property.1 z.2.down.property.2⟩, by fun_prop⟩

def rightClock : square ⟶ space := TopCat.ofHom
  ⟨fun z => ⟨(z.1, ULift.up ⟨(z.1.down : ℝ) + (1 - z.1.down) * z.2.down, by
      have hw : 0 ≤ 1 - (z.1.down : ℝ) := sub_nonneg.mpr z.1.down.property.2
      constructor
      · exact add_nonneg z.1.down.property.1 (mul_nonneg hw z.2.down.property.1)
      · have h := mul_le_of_le_one_right hw z.2.down.property.2; linarith⟩), by
      change (z.1.down : ℝ) ≤ z.1.down + (1 - z.1.down) * z.2.down
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr z.1.down.property.2) z.2.down.property.1)⟩,
    by fun_prop⟩

def leftAffine : square ⟶ space := TopCat.ofHom
  ⟨fun z => ⟨(ULift.up ⟨min (z.1.down : ℝ) z.2.down,
    ⟨le_min z.1.down.property.1 z.2.down.property.1,
      (min_le_left _ _).trans z.1.down.property.2⟩⟩, z.1), by
        change min (z.1.down : ℝ) z.2.down ≤ (z.1.down : ℝ)
        exact min_le_left _ _⟩, by
    have ht : Continuous (fun z : square => (z.1.down : ℝ)) := by fun_prop
    have hu : Continuous (fun z : square => (z.2.down : ℝ)) := by fun_prop
    exact (((continuous_uliftUp.comp ((ht.min hu).subtype_mk _)).prodMk
      continuous_fst).subtype_mk _)⟩

def rightAffine : square ⟶ space := TopCat.ofHom
  ⟨fun z => ⟨(z.1, ULift.up ⟨max (z.1.down : ℝ) z.2.down,
    ⟨z.1.down.property.1.trans (le_max_left _ _),
      max_le z.1.down.property.2 z.2.down.property.2⟩⟩), by
        change (z.1.down : ℝ) ≤ max (z.1.down : ℝ) z.2.down
        exact le_max_left _ _⟩, by
    have ht : Continuous (fun z : square => (z.1.down : ℝ)) := by fun_prop
    have hu : Continuous (fun z : square => (z.2.down : ℝ)) := by fun_prop
    exact ((continuous_fst.prodMk
      (continuous_uliftUp.comp ((ht.max hu).subtype_mk _))).subtype_mk _)⟩

def blendI (v : _root_.unitInterval) (a b : TopCat.I.{0}) : TopCat.I := ULift.up
  ⟨(1 - (v : ℝ)) * a.down + (v : ℝ) * b.down, by
    have hw : 0 ≤ 1 - (v : ℝ) := sub_nonneg.mpr v.property.2
    constructor
    · exact add_nonneg (mul_nonneg hw a.down.property.1) (mul_nonneg v.property.1 b.down.property.1)
    · have h := add_le_add (mul_le_of_le_one_right hw a.down.property.2)
        (mul_le_of_le_one_right v.property.1 b.down.property.2)
      linarith⟩

def mix (v : _root_.unitInterval) (a b : space) : space :=
  ⟨(blendI v a.val.1 b.val.1, blendI v a.val.2 b.val.2),
    add_le_add (mul_le_mul_of_nonneg_left a.property (sub_nonneg.mpr v.property.2))
      (mul_le_mul_of_nonneg_left b.property v.property.1)⟩

theorem continuous_mix : Continuous (fun z : _root_.unitInterval × (space × space) => mix z.1 z.2.1 z.2.2) := by
  dsimp only [mix, blendI]
  fun_prop

theorem mix_zero (a b : space) : mix 0 a b = a := by
  apply Subtype.ext
  apply Prod.ext <;> apply ULift.ext <;> apply Subtype.ext <;> simp [mix, blendI]

theorem mix_one (a b : space) : mix 1 a b = b := by
  apply Subtype.ext
  apply Prod.ext <;> apply ULift.ext <;> apply Subtype.ext <;> simp [mix, blendI]

theorem mix_self (v : _root_.unitInterval) (a : space) : mix v a a = a := by
  apply Subtype.ext
  apply Prod.ext <;> apply ULift.ext <;> apply Subtype.ext <;> dsimp only [mix, blendI] <;> ring

def leftHomotopy : TopCat.Homotopy leftClock leftAffine where
  toFun z := mix z.1 (leftClock z.2) (leftAffine z.2)
  continuous_toFun := continuous_mix.comp (continuous_fst.prodMk
    (((leftClock.hom.continuous).comp continuous_snd).prodMk
      ((leftAffine.hom.continuous).comp continuous_snd)))
  map_zero_left _z := mix_zero _ _
  map_one_left _z := mix_one _ _

def rightHomotopy : TopCat.Homotopy rightClock rightAffine where
  toFun z := mix z.1 (rightClock z.2) (rightAffine z.2)
  continuous_toFun := continuous_mix.comp (continuous_fst.prodMk
    (((rightClock.hom.continuous).comp continuous_snd).prodMk
      ((rightAffine.hom.continuous).comp continuous_snd)))
  map_zero_left _z := mix_zero _ _
  map_one_left _z := mix_one _ _

def boundary : Set square := {z | (z.1.down : ℝ) = 0 ∨ (z.1.down : ℝ) = 1 ∨
  (z.2.down : ℝ) = 0 ∨ (z.2.down : ℝ) = 1}

theorem left_boundary_agree (z : square) (hz : z ∈ boundary) : leftClock z = leftAffine z := by
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change (z.1.down : ℝ) * z.2.down = min (z.1.down : ℝ) z.2.down
    rcases hz with h | h | h | h
    · rw [h, zero_mul, min_eq_left z.2.down.property.1]
    · rw [h, one_mul, min_eq_right z.2.down.property.2]
    · rw [h, mul_zero, min_eq_right z.1.down.property.1]
    · rw [h, mul_one, min_eq_left z.1.down.property.2]
  · rfl

theorem right_boundary_agree (z : square) (hz : z ∈ boundary) : rightClock z = rightAffine z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply Subtype.ext
    change (z.1.down : ℝ) + (1 - z.1.down) * z.2.down = max (z.1.down : ℝ) z.2.down
    rcases hz with h | h | h | h
    · rw [h, max_eq_right z.2.down.property.1]; ring
    · rw [h, max_eq_left z.2.down.property.2]; ring
    · rw [h, max_eq_left z.1.down.property.1]; ring
    · rw [h, max_eq_right z.1.down.property.2]; ring

theorem left_boundary_fixed (v : _root_.unitInterval) (z : square) (hz : z ∈ boundary) :
    leftHomotopy (v, z) = leftClock z := by
  change mix v (leftClock z) (leftAffine z) = leftClock z
  rw [← left_boundary_agree z hz, mix_self]

theorem right_boundary_fixed (v : _root_.unitInterval) (z : square) (hz : z ∈ boundary) :
    rightHomotopy (v, z) = rightClock z := by
  change mix v (rightClock z) (rightAffine z) = rightClock z
  rw [← right_boundary_agree z hz, mix_self]

end
end Finsler.OrderedDoubleCutTimes
