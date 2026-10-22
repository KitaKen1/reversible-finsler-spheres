module

public import Finsler.Topology.CompactRectangleOscillation
public import Finsler.Topology.SupportedSelfCutAdequacy
public import Finsler.Topology.NearFarCapComparison

/-! A common rectangle scale for a genuinely partial joined family.
The join near/far dichotomy first puts a whole relevant source piece in
the compact outer tube. Uniform continuity there then gives the actual
cut-far/cut-domain dichotomy. No extension of the family outside its
original domain, and no global closure of a zero extension, is used. -/

@[expose] public section
namespace Finsler.PartialJoinRectangleRefinement

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SelfCutThomCocycle
open Finsler.SelfCutParameterFamily Finsler.PairDistanceCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem exists_scale {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    {ι : Type*} [Fintype ι] {n : ℕ}
    (K : Set (P × Q)) (hK : IsCompact K) (e : ι → (TopCat.of K ⟶ parameters n))
    (r ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i) (hρr : ∀ i, 2 * ρ i < r i)
    {b : ℝ} (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧
    ∀ (i : ι) (cx : P) (cy : Q) (S : Set (P × Q)),
      S ⊆ cover id η cx ×ˢ cover id η cy →
    ∀ {E : Type*} [PseudoMetricSpace E] (u : P → E) (v : Q → E) (ρJ : ℝ),
      S ⊆ cover u (ρJ / 4) cx ×ˢ cover v (ρJ / 4) cy →
      (∀ z : P × Q, dist (u z.1) (v z.2) < 2 * ρJ → z ∈ K) →
      S ⊆ NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of Q) u v ρJ ∨
        S ⊆ {z | ρ i < distanceValue K e i z} ∨ S ⊆ domain K e r i := by
  classical
  obtain ⟨δ, hδ, hosc⟩ := FiniteGuardedOscillation.exists_simultaneous_radius Finset.univ
    (fun _ : ι => K) (fun _ _ => hK) (distanceValue K e)
    (fun i _ => distance_continuousOn K e i) ρ (fun i _ => hρ i)
  let η := min (δ / 4) b
  have hη : 0 < η := lt_min (div_pos hδ (by norm_num)) hb
  have hηb : η ≤ b := min_le_right _ _
  refine ⟨η, hη, hηb, ?_⟩
  intro i cx cy S hrect E inst u v ρJ hrectJ hTube
  obtain hfar | hnear := near_far_rectangle u v ρJ cx cy
  · left
    intro z hz
    exact hfar z.1 (hrectJ hz).1 z.2 (hrectJ hz).2
  · have hSK : S ⊆ K := by
      intro z hz
      exact hTube z (hnear z.1 (hrectJ hz).1 z.2 (hrectJ hz).2)
    by_cases hf : ∀ z ∈ S, ρ i < distanceValue K e i z
    · exact Or.inr (Or.inl hf)
    · push_neg at hf
      obtain ⟨w, hw, hdw⟩ := hf
      right; right
      intro z hz
      refine ⟨hSK hz, ?_⟩
      have hzw : dist z w < δ := by
        have hx := same_member id (hrect hz).1 (hrect hw).1
        have hy := same_member id (hrect hz).2 (hrect hw).2
        have hηδ : η ≤ δ / 4 := min_le_left _ _
        change dist z.1 w.1 < 2 * η at hx
        change dist z.2 w.2 < 2 * η at hy
        rw [Prod.dist_eq]
        apply max_lt <;> linarith
      have hh := hosc i (Finset.mem_univ i) z (hSK hz) w (hSK hw) hzw
      have hu := (abs_lt.mp hh).2
      have hr := hρr i
      change distanceValue K e i z < r i
      linarith

end
end Finsler.PartialJoinRectangleRefinement
