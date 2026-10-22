module

public import Finsler.Loop.OrderedDoubleCutTimes
public import Finsler.Loop.UniversalTimeTriangleChain

/-! The two affine halves of the time square map to the SAME ordered
triangle. The other two halves map to the ACTUAL diagonal. These are
literal continuous-map identities, before any cap or quotient. -/
@[expose] public section
namespace Finsler.OrderedDoubleCutTriangle
open CategoryTheory Topology Convexity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

abbrev triangle := UniversalTimeTriangle.space

def early : triangle ⟶ TopCat.I.{0} := TopCat.ofHom
  ⟨fun z => ULift.up ⟨z.weights 2, z.weights_nonneg 2, z.weights_apply_le_one 2⟩, by fun_prop⟩

def late : triangle ⟶ TopCat.I.{0} := TopCat.ofHom
  ⟨fun z => ULift.up ⟨z.weights 1 + z.weights 2, by
    constructor
    · exact add_nonneg (z.weights_nonneg 1) (z.weights_nonneg 2)
    · have ht := z.total_of_fintype
      rw [Fin.sum_univ_three] at ht
      have h₀ := z.weights_nonneg 0
      linarith⟩, by fun_prop⟩

theorem early_le_late (z : triangle) : (early z).down ≤ (late z).down := by
  change z.weights 2 ≤ z.weights 1 + z.weights 2
  exact le_add_of_nonneg_left (z.weights_nonneg 1)

def lower : triangle ⟶ OrderedDoubleCutTimes.square := TopCat.ofHom
  ⟨fun z => (late z, early z), late.hom.continuous.prodMk early.hom.continuous⟩

def upper : triangle ⟶ OrderedDoubleCutTimes.square := TopCat.ofHom
  ⟨fun z => (early z, late z), early.hom.continuous.prodMk late.hom.continuous⟩

def triangleMap : triangle ⟶ OrderedDoubleCutTimes.space := TopCat.ofHom
  ⟨fun z => ⟨(early z, late z), early_le_late z⟩,
    (early.hom.continuous.prodMk late.hom.continuous).subtype_mk _⟩

def diagonal : TopCat.I.{0} ⟶ OrderedDoubleCutTimes.space := TopCat.ofHom
  ⟨fun t => ⟨(t, t), by change (t.down : ℝ) ≤ (t.down : ℝ); exact le_refl _⟩,
    by fun_prop⟩

theorem lower_left : lower ≫ OrderedDoubleCutTimes.leftAffine = triangleMap := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change min ((late z).down : ℝ) (early z).down = ((early z).down : ℝ)
    exact min_eq_right (early_le_late z)
  · rfl

theorem upper_right : upper ≫ OrderedDoubleCutTimes.rightAffine = triangleMap := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply Subtype.ext
    change max ((early z).down : ℝ) (late z).down = ((late z).down : ℝ)
    exact max_eq_right (early_le_late z)

theorem upper_left_diagonal :
    upper ≫ OrderedDoubleCutTimes.leftAffine = early ≫ diagonal := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · apply ULift.ext
    apply Subtype.ext
    change min ((early z).down : ℝ) (late z).down = ((early z).down : ℝ)
    exact min_eq_left (early_le_late z)
  · rfl

theorem lower_right_diagonal :
    lower ≫ OrderedDoubleCutTimes.rightAffine = late ≫ diagonal := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ULift.ext
    apply Subtype.ext
    change max ((late z).down : ℝ) (early z).down = ((late z).down : ℝ)
    exact max_eq_left (early_le_late z)

end
end Finsler.OrderedDoubleCutTriangle
