module

public import Finsler.Topology.JoinedFilteredCap
public import Finsler.Topology.CompactRectangleOscillation

/-! One actual rectangle scale refines each of the three genuine
joined-loop far/cut-domain covers before any cochain or degree. -/

@[expose] public section
namespace Finsler.JoinedRectangleRefinement

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}

def far (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (ρ : ℝ) (i : Fin 3) : Set (Outer X) :=
  {z | ρ < distanceValue (tube X) (family u a ha ha1) i z}

theorem rectangleCover_mono {η ζ : ℝ} (h : η ≤ ζ) (center : (ClosedInterval × ClosedInterval) × X) :
    JoinedFilteredCap.rectangleCover X η center ⊆ JoinedFilteredCap.rectangleCover X ζ center := by
  intro z hz
  exact ⟨hz.1.trans_le h, hz.2.trans_le h⟩

theorem exists_scale (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r b : ℝ} (hρ : 0 < ρ) (hρr : 2 * ρ < r) (hb : 0 < b) :
    ∃ η > 0, η ≤ b ∧ ∀ (i : Fin 3) (center : (ClosedInterval × ClosedInterval) × X),
      JoinedFilteredCap.rectangleCover X η center ⊆ far u a ha ha1 ρ i ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i := by
  classical
  obtain ⟨η, hη, hηb, hosc⟩ := CompactRectangleOscillation.exists_rectangle_scale Finset.univ
    (show IsCompact (tube X) from isCompact_univ)
    (distanceValue (tube X) (family u a ha ha1))
    (fun i _ => distance_continuousOn (tube X) (family u a ha ha1) i) hρ hb
  refine ⟨η, hη, hηb, ?_⟩
  intro i center
  by_cases hf : ∀ z ∈ JoinedFilteredCap.rectangleCover X η center,
      ρ < distanceValue (tube X) (family u a ha ha1) i z
  · left
    exact hf
  · right
    push_neg at hf
    obtain ⟨w, hw, hdw⟩ := hf
    intro z hz
    refine ⟨Set.mem_univ _, ?_⟩
    have hh := hosc center.1 center.2 i (Finset.mem_univ i)
      z.1 hz.1 w.1 hw.1 z.2 hz.2 w.2 hw.2 (Set.mem_univ _) (Set.mem_univ _)
    have hu := (abs_lt.mp hh).2
    change distanceValue (tube X) (family u a ha ha1) i z < r
    linarith

end
end Finsler.JoinedRectangleRefinement
