module

public import Finsler.Loop.CompactRectangleCoverRefinement

/-! Refine a mapped product cover and two independently specified
factor covers by the same positive metric scale before any cochains. -/

@[expose] public section
namespace Finsler.CompactFactorCoverRefinement

open Set
set_option autoImplicit false

theorem exists_factor {P : Type} [PseudoMetricSpace P] [CompactSpace P] {ι : Type*}
    (U : ι → Set P) (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = univ) {b : ℝ} (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧ ∃ r : P → ι, ∀ c, PairDistanceCover.cover id η c ⊆ U (r c) := by
  classical
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU
    (show (univ : Set P) ⊆ ⋃ i, U i by rw [hcU])
  have hi : ∀ c : P, ∃ i, Metric.ball c δ ⊆ U i := fun c => hball c (mem_univ c)
  choose r hr using hi
  refine ⟨min δ b, lt_min hδ hb, min_le_right _ _, r, ?_⟩
  intro c z hz
  have hdist : dist z c < min δ b := hz
  exact hr c (hdist.trans_le (min_le_left _ _))

theorem exists_simultaneous {P Q Z : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [TopologicalSpace Z] [CompactSpace P] [CompactSpace Q] {ι κ μ : Type*}
    (U : ι → Set P) (V : κ → Set Q) (W : μ → Set Z)
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = univ)
    (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = univ)
    (hW : ∀ i, IsOpen (W i)) (hcW : ⋃ i, W i = univ)
    (f : C(P × Q, Z)) {b : ℝ} (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧ ∃ (r : P × Q → μ) (s : P → ι) (t : Q → κ),
      (∀ c, MapsTo f (PairDistanceCover.cover id η c.1 ×ˢ PairDistanceCover.cover id η c.2) (W (r c))) ∧
      (∀ c, PairDistanceCover.cover id η c ⊆ U (s c)) ∧
      (∀ c, PairDistanceCover.cover id η c ⊆ V (t c)) := by
  obtain ⟨η₀, hη₀, hη₀b, r, hr⟩ := CompactRectangleCoverRefinement.exists_refinement W hW hcW f hb
  obtain ⟨η₁, hη₁, hη₁₀, s, hs⟩ := exists_factor U hU hcU hη₀
  obtain ⟨η₂, hη₂, hη₂₁, t, ht⟩ := exists_factor V hV hcV hη₁
  refine ⟨η₂, hη₂, hη₂₁.trans (hη₁₀.trans hη₀b), r, s, t, ?_, ?_, ht⟩
  · intro c z hz
    exact hr c ⟨hz.1.trans_le (hη₂₁.trans hη₁₀), hz.2.trans_le (hη₂₁.trans hη₁₀)⟩
  · intro c z hz
    exact hs c (hz.trans_le hη₂₁)

end Finsler.CompactFactorCoverRefinement
