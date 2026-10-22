module

public import Finsler.Topology.PairDistanceCover
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! A finite collection of continuous tested lengths on a compact
intermediate tube admits one factorwise rectangle scale, below any prior
positive scale. This is a parameter-domain lemma; the original geometric
maps and nonzero cap witnesses still have to be supplied. -/

@[expose] public section
namespace Finsler.CompactRectangleOscillation

open Set
open Finsler.PairDistanceCover

noncomputable section
set_option maxHeartbeats 400000

variable {X Y ι : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

theorem exists_radius (s : Finset ι) {K : Set (X × Y)} (hK : IsCompact K)
    (f : ι → X × Y → ℝ) (hf : ∀ i ∈ s, ContinuousOn (f i) K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ i ∈ s, ∀ z ∈ K, ∀ w ∈ K,
      dist z w < δ → |f i z - f i w| < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨δa, hδa, hbounda⟩ :=
      (Metric.uniformContinuousOn_iff.mp
        (hK.uniformContinuousOn_of_continuous (hf a (Finset.mem_insert_self a s)))) ε hε
    refine ⟨min δa δ, lt_min hδa hδ, ?_⟩
    intro i hi z hz w hw hzw
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa only [Real.dist_eq] using hbounda z hz w hw (hzw.trans_le (min_le_left _ _))
    · exact hbound i hi z hz w hw (hzw.trans_le (min_le_right _ _))

theorem exists_rectangle_scale (s : Finset ι) {K : Set (X × Y)} (hK : IsCompact K)
    (f : ι → X × Y → ℝ) (hf : ∀ i ∈ s, ContinuousOn (f i) K)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ η > 0, η ≤ ρ ∧ ∀ (cx : X) (cy : Y) (i : ι), i ∈ s →
      ∀ x ∈ cover id η cx, ∀ x' ∈ cover id η cx,
      ∀ y ∈ cover id η cy, ∀ y' ∈ cover id η cy,
      (x, y) ∈ K → (x', y') ∈ K → |f i (x, y) - f i (x', y')| < ε := by
  obtain ⟨δ, hδ, hbound⟩ := exists_radius s hK f hf hε
  refine ⟨min (δ / 4) ρ, lt_min (by positivity) hρ, min_le_right _ _, ?_⟩
  intro cx cy i hi x hx x' hx' y hy y' hy' hz hw
  apply hbound i hi (x, y) hz (x', y') hw
  rw [Prod.dist_eq]
  apply max_lt
  · have hxx := same_member id hx hx'
    change dist x x' < 2 * min (δ / 4) ρ at hxx
    have hmin := min_le_left (δ / 4) ρ
    linarith
  · have hyy := same_member id hy hy'
    change dist y y' < 2 * min (δ / 4) ρ at hyy
    have hmin := min_le_left (δ / 4) ρ
    linarith

omit [PseudoMetricSpace X] [PseudoMetricSpace Y] in
theorem whole_parent_lower (s : Finset ι) (f : ι → X × Y → ℝ) (L : ι → ℝ)
    (P : Set (X × Y)) (ε : ℝ)
    (hosc : ∀ i ∈ s, ∀ z ∈ P, ∀ w ∈ P, |f i z - f i w| < ε)
    (hwitness : ∀ i ∈ s, ∃ w ∈ P, L i ≤ f i w) :
    ∀ i ∈ s, ∀ z ∈ P, L i - ε ≤ f i z := by
  intro i hi z hz
  obtain ⟨w, hw, hL⟩ := hwitness i hi
  have h := (abs_lt.mp (hosc i hi z hz w hw)).1
  linarith

end
end Finsler.CompactRectangleOscillation
