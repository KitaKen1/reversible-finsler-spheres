module

public import Finsler.Topology.PairDistanceCover
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! Any open cover pulled back from an actual target admits uniform
factorwise metric rectangles on compact input spaces. The scale depends
only on that cover and map, so it can precede all tested cochains. -/

@[expose] public section
namespace Finsler.CompactRectangleCoverRefinement

open Set

set_option autoImplicit false

theorem exists_refinement {P Q Z : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [TopologicalSpace Z] [CompactSpace P] [CompactSpace Q]
    {ι : Type*} (W : ι → Set Z) (hW : ∀ i, IsOpen (W i)) (hcW : ⋃ i, W i = univ)
    (f : C(P × Q, Z)) {b : ℝ} (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧ ∃ r : P × Q → ι, ∀ c : P × Q,
      MapsTo f (PairDistanceCover.cover id η c.1 ×ˢ PairDistanceCover.cover id η c.2) (W (r c)) := by
  classical
  have hc : (univ : Set (P × Q)) ⊆ ⋃ i, f ⁻¹' W i := by
    intro z _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcW.symm ▸ mem_univ (f z))
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun i => (hW i).preimage f.continuous) hc
  have hi : ∀ c : P × Q, ∃ i, Metric.ball c δ ⊆ f ⁻¹' W i :=
    fun c => hball c (mem_univ c)
  choose r hr using hi
  refine ⟨min δ b, lt_min hδ hb, min_le_right _ _, r, ?_⟩
  intro c z hz
  apply hr c
  change dist z c < δ
  rw [Prod.dist_eq]
  exact max_lt (hz.1.trans_le (min_le_left _ _)) (hz.2.trans_le (min_le_left _ _))

end Finsler.CompactRectangleCoverRefinement

