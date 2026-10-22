module

public import Finsler.Topology.InteriorTimeSlide

/-! A single slide collar for both original compact loop families,
chosen before any near-pair tube or rotation correction. -/

@[expose] public section
namespace Finsler.OriginalPairSlideCollar

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SelfCutThomCocycle
open Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem exists_pair {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {n : ℕ}
    (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      (∀ (s : ClosedInterval) (x : P),
        distance n (InteriorTimeSlide.slide a ha.le ha1.le (s, 0), α x) ≤ δ) ∧
      (∀ (s : ClosedInterval) (x : P),
        distance n (InteriorTimeSlide.slide a ha.le ha1.le (s, 1), α x) ≤ δ) ∧
      (∀ (s : ClosedInterval) (y : Q),
        distance n (InteriorTimeSlide.slide a ha.le ha1.le (s, 0), β y) ≤ δ) ∧
      (∀ (s : ClosedInterval) (y : Q),
        distance n (InteriorTimeSlide.slide a ha.le ha1.le (s, 1), β y) ≤ δ) := by
  obtain ⟨b₀, hb₀, hb₀1, hα⟩ := UniformSelfCutCollar.exists_collar α hδ
  obtain ⟨b₁, hb₁, hb₁1, hβ⟩ := UniformSelfCutCollar.exists_collar β hδ
  let b := min b₀ b₁
  have hb : 0 < b := lt_min hb₀ hb₁
  let a := b / 2
  have ha : 0 < a := div_pos hb (by norm_num)
  have hab : a < b := by dsimp only [a]; linarith
  have ha₀ : a < b₀ := hab.trans_le (min_le_left _ _)
  have ha₁ : a < b₁ := hab.trans_le (min_le_right _ _)
  have ha1 : a < 1 / 2 := ha₀.trans hb₀1
  refine ⟨a, ha, ha1, ?_, ?_, ?_, ?_⟩
  · intro s x
    exact hα _ x (Or.inl (InteriorTimeSlide.slide_ends_in_collar a b₀ ha.le ha1.le ha₀ s).1)
  · intro s x
    exact hα _ x (Or.inr (InteriorTimeSlide.slide_ends_in_collar a b₀ ha.le ha1.le ha₀ s).2)
  · intro s y
    exact hβ _ y (Or.inl (InteriorTimeSlide.slide_ends_in_collar a b₁ ha.le ha1.le ha₁ s).1)
  · intro s y
    exact hβ _ y (Or.inr (InteriorTimeSlide.slide_ends_in_collar a b₁ ha.le ha1.le ha₁ s).2)

end
end Finsler.OriginalPairSlideCollar
