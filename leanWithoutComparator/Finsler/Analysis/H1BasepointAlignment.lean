module

public import Finsler.Geometry.NearbyRotor
public import Finsler.Analysis.H1OrthogonalLength

/-! Uniform controlled basepoint alignment for actual H¹ sphere loops.
Compactness makes the radius uniform over all sphere basepoints. A length
bound is fixed before choosing the radius. No cut-join chain or filling is asserted. -/

@[expose] public section

namespace Finsler.H1BasepointAlignment

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.NearbyRotor Finsler.H1OrthogonalLength Finsler.SobolevLength
open Set Metric
open scoped Topology RealInnerProductSpace

noncomputable section
variable {n : ℕ}

def nearUnitPairs (n : ℕ) : Set (Ambient n × Ambient n) :=
  {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 1 ∧ 1 ≤ ‖p.1 + p.2‖}

theorem nearUnitPairs_compact (n : ℕ) : IsCompact (nearUnitPairs n) := by
  have hc : IsClosed {p : Ambient n × Ambient n | 1 ≤ ‖p.1 + p.2‖} :=
    isClosed_le continuous_const (continuous_fst.add continuous_snd).norm
  convert ((isCompact_sphere (0 : Ambient n) 1).prod
    (isCompact_sphere (0 : Ambient n) 1)).inter_right hc using 1
  ext p
  simp [nearUnitPairs, and_assoc]

theorem exists_uniform_rotor_radius {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : Ambient n, ‖x‖ = 1 → ‖y‖ = 1 → dist y x < ρ →
      ‖(rotor x y).toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ := by
  have hc : ContinuousOn (fun p : Ambient n × Ambient n =>
      (rotor p.1 p.2).toContinuousLinearMap) (nearUnitPairs n) := by
    intro p hp
    have hx : p.1 ≠ 0 := by
      intro h
      have he := hp.1
      simp [h] at he
    have hsum : p.1 + p.2 ≠ 0 := by
      intro h
      have he := hp.2.2
      rw [h, norm_zero] at he
      norm_num at he
    exact (rotor_continuousAt hx hsum).continuousWithinAt
  have hu := (nearUnitPairs_compact n).uniformContinuousOn_of_continuous hc
  obtain ⟨r, hr, hd⟩ := Metric.uniformContinuousOn_iff.mp hu δ hδ
  refine ⟨min 1 r, lt_min zero_lt_one hr, fun x y hx hy hdist => ?_⟩
  have hsmall : ‖x - y‖ < 1 := by
    rw [norm_sub_rev]
    simpa only [dist_eq_norm] using hdist.trans_le (min_le_left 1 r)
  have hx2 : ‖x + x‖ = 2 := by
    rw [← two_smul ℝ x, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      hx, mul_one]
  have hsum : 1 ≤ ‖x + y‖ := by
    have ht := norm_add_le (x + y) (x - y)
    have he : (x + y) + (x - y) = x + x := by abel
    rw [he, hx2] at ht
    linarith
  have hxy : (x, y) ∈ nearUnitPairs n := ⟨hx, hy, hsum⟩
  have hxx : (x, x) ∈ nearUnitPairs n := ⟨hx, hx, by rw [hx2]; norm_num⟩
  have hpdist : dist ((x, y) : Ambient n × Ambient n) (x, x) < r := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist y x)] using
      hdist.trans_le (min_le_right 1 r)
  have he := hd (x, y) hxy (x, x) hxx hpdist
  have hid : (rotor x x).toContinuousLinearMap = ContinuousLinearMap.id ℝ (Ambient n) := by
    rw [rotor_self]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  simpa only [hid, dist_eq_norm] using he

/-- The correction changes the actual trace to y and costs less than ε length. -/
theorem exists_alignment (F : ReversibleMetric n) (M : ℝ) (hM : 0 ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x y : Ambient n, ‖x‖ = 1 → ‖y‖ = 1 → dist y x < ρ →
      ∀ u : SphereLoop n, continuousRepresentative (u.data : Space n) 0 = x → length F u ≤ M →
        continuousRepresentative ((rotateLoop (rotor x y) u).data : Space n) 0 = y ∧
          |length F (rotateLoop (rotor x y) u) - length F u| < ε := by
  obtain ⟨δ, hδ, hd⟩ := exists_additive_length_control F M hM hε
  obtain ⟨ρ, hρ, hrot⟩ := exists_uniform_rotor_radius (n := n) hδ
  refine ⟨ρ, hρ, fun x y hx hy hxy u hu hlen => ⟨?_, ?_⟩⟩
  · change continuousRepresentative (rotateData (rotor x y) (u.data : Space n)) 0 = y
    rw [representative_rotateData _ _ (by norm_num : (0 : ℝ) ∈ Icc 0 1), hu]
    exact rotor_map (hx.trans hy.symm)
  · exact hd _ (hrot x y hx hy hxy) u hlen


end
end Finsler.H1BasepointAlignment
