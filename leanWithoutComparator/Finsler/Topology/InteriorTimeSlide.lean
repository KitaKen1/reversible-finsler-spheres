module

public import Finsler.Topology.AnnularCollarCut

/-! The actual full-to-interior time map and its continuous slide on a
genuine H1 loop family. This constructs the geometry; the capped double-prism
comparison and its length control are separate obligations. -/

@[expose] public section
namespace Finsler.InteriorTimeSlide

open CategoryTheory
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SelfCutThomCocycle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def trimTime (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) : C(ClosedInterval, ClosedInterval) where
  toFun t := ⟨a + (1 - 2 * a) * t, by
    have hb : 0 ≤ 1 - 2 * a := by linarith
    constructor
    · exact add_nonneg ha (mul_nonneg hb t.property.1)
    · have h := mul_le_of_le_one_right hb t.property.2
      linarith⟩
  continuous_toFun := by fun_prop

theorem trimTime_range (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (t : ClosedInterval) :
    a ≤ (trimTime a ha ha1 t : ℝ) ∧ (trimTime a ha ha1 t : ℝ) ≤ 1 - a := by
  have hb : 0 ≤ 1 - 2 * a := by linarith
  change a ≤ a + (1 - 2 * a) * t ∧ a + (1 - 2 * a) * t ≤ 1 - a
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg hb t.property.1)
  · have h := mul_le_of_le_one_right hb t.property.2
    linarith

def slide (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    C(ClosedInterval × ClosedInterval, ClosedInterval) where
  toFun z := ⟨(1 - (z.1 : ℝ)) * z.2 + (z.1 : ℝ) * trimTime a ha ha1 z.2, by
    have hs : 0 ≤ 1 - (z.1 : ℝ) := sub_nonneg.mpr z.1.property.2
    constructor
    · exact add_nonneg (mul_nonneg hs z.2.property.1)
        (mul_nonneg z.1.property.1 (trimTime a ha ha1 z.2).property.1)
    · have hl := mul_le_of_le_one_right hs z.2.property.2
      have hr := mul_le_of_le_one_right z.1.property.1 (trimTime a ha ha1 z.2).property.2
      linarith⟩
  continuous_toFun := by fun_prop

theorem slide_zero (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (t : ClosedInterval) :
    slide a ha ha1 (0, t) = t := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) * t + 0 * (trimTime a ha ha1 t : ℝ) = (t : ℝ)
  ring

theorem slide_one (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (t : ClosedInterval) :
    slide a ha ha1 (1, t) = trimTime a ha ha1 t := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) * t + 1 * (trimTime a ha ha1 t : ℝ) = (trimTime a ha ha1 t : ℝ)
  ring

theorem slide_left (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (s : ClosedInterval) :
    (slide a ha ha1 (s, 0) : ℝ) = (s : ℝ) * a := by
  change (1 - (s : ℝ)) * 0 + (s : ℝ) * (a + (1 - 2 * a) * 0) = _
  ring

theorem slide_right (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (s : ClosedInterval) :
    (slide a ha ha1 (s, 1) : ℝ) = 1 - (s : ℝ) * a := by
  change (1 - (s : ℝ)) * 1 + (s : ℝ) * (a + (1 - 2 * a) * 1) = _
  ring

def trimmedMap {X : Type} [TopologicalSpace X] {n : ℕ}
    (u : C(X, SphereLoop n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    TopCat.of (ClosedInterval × X) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (trimTime a ha ha1 z.1, u z.2),
    ((trimTime a ha ha1).continuous.comp continuous_fst).prodMk
      (u.continuous.comp continuous_snd)⟩

def homotopy {X : Type} [TopologicalSpace X] {n : ℕ}
    (u : C(X, SphereLoop n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    TopCat.Homotopy (AnnularSelfCut.familyMap u) (trimmedMap u a ha ha1) where
  toFun z := (slide a ha ha1 (z.1, z.2.1), u z.2.2)
  continuous_toFun := ((slide a ha ha1).continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (u.continuous.comp (continuous_snd.comp continuous_snd))
  map_zero_left z := Prod.ext (slide_zero a ha ha1 z.1) rfl
  map_one_left z := Prod.ext (slide_one a ha ha1 z.1) rfl

theorem slide_ends_in_collar (a b : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hab : a < b) (s : ClosedInterval) :
    (slide a ha ha1 (s, 0) : ℝ) < b ∧ 1 - b < (slide a ha ha1 (s, 1) : ℝ) := by
  rw [slide_left, slide_right]
  have hs : (s : ℝ) * a ≤ a := mul_le_of_le_one_left ha s.property.2
  constructor <;> linarith

theorem family_slide_sides_small {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    {n : ℕ} (u : C(X, SphereLoop n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      (∀ (s : ClosedInterval) (x : X), SupportedSelfCut.distance n
        (homotopy u a ha.le ha1.le (s, (0, x))) ≤ δ) ∧
      (∀ (s : ClosedInterval) (x : X), SupportedSelfCut.distance n
        (homotopy u a ha.le ha1.le (s, (1, x))) ≤ δ) := by
  obtain ⟨b, hb, hb1, hbound⟩ := UniformSelfCutCollar.exists_collar u hδ
  let a := b / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 / 2 := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  refine ⟨a, ha, ha1, ?_, ?_⟩
  · intro s x
    exact hbound (slide a ha.le ha1.le (s, 0)) x
      (Or.inl (slide_ends_in_collar a b ha.le ha1.le hab s).1)
  · intro s x
    exact hbound (slide a ha.le ha1.le (s, 1)) x
      (Or.inr (slide_ends_in_collar a b ha.le ha1.le hab s).2)

end
end Finsler.InteriorTimeSlide
