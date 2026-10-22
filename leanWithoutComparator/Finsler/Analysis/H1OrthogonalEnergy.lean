module

public import Finsler.Analysis.H1AlignmentHomotopy
public import Finsler.Topology.Birkhoff

/-! Direct energy control for actual nearby orthogonal corrections.
The positive input cut and additive output tolerance are fixed before choosing
one radius for every loop and every intermediate correction time. -/

@[expose] public section

namespace Finsler.H1OrthogonalEnergy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevLength Finsler.SmallRotation
open Finsler.SmallRotationGeneral Finsler.H1OrthogonalLength
open Finsler.CompactH1Alignment Finsler.H1AlignmentHomotopy Finsler.RotorHomotopy
open Finsler.BorelLoop MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

theorem exists_relative_energy_upper (F : ReversibleMetric n) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Ambient n ≃ₗᵢ[ℝ] Ambient n,
      ‖A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ →
      ∀ u : SphereLoop n, energy F (rotateLoop A u) ≤ (1 + η) ^ 2 * energy F u := by
  obtain ⟨δ, hδ, hd⟩ := exists_rotation_speed_control F hη
  refine ⟨δ, hδ, fun A hA u => ?_⟩
  have hpoint : ∀ᵐ t ∂intervalMeasure,
      Finsler.AmbientLagrangian.lagrangian F (weakJet (rotateLoop A u) t) ≤
        (1 + η) ^ 2 * Finsler.AmbientLagrangian.lagrangian F (weakJet u t) := by
    filter_upwards [weakJet_rotateLoop_ae A u, weakVelocity_orthogonal_ae u,
      ae_restrict_mem measurableSet_Ioo] with t hj hi ht
    have he := hd A hA _ _ (u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩) hi
    have hs : |speed F (rotateLoop A u) t - speed F u t| ≤ η * speed F u t := by
      change |pointSpeed F (weakJet (rotateLoop A u) t) - pointSpeed F (weakJet u t)| ≤ _
      rw [hj]
      exact he
    have hb : speed F (rotateLoop A u) t ≤ (1 + η) * speed F u t := by
      have hdif := (abs_sub_le_iff.mp hs).1
      linarith
    have hsq := pow_le_pow_left₀ (speed_nonneg F (rotateLoop A u) t) hb 2
    simpa only [mul_pow, speed_sq] using hsq
  calc
    energy F (rotateLoop A u) ≤
        ∫ t, (1 + η) ^ 2 * Finsler.AmbientLagrangian.lagrangian F (weakJet u t)
          ∂intervalMeasure :=
      integral_mono_ae (density_integrable F (rotateLoop A u))
        ((density_integrable F u).const_mul ((1 + η) ^ 2)) hpoint
    _ = (1 + η) ^ 2 * energy F u := integral_const_mul _ _

theorem exists_rotation_cut_control (F : ReversibleMetric n) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Ambient n ≃ₗᵢ[ℝ] Ambient n,
      ‖A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ →
      ∀ u : SphereLoop n, energy F u < q ^ 2 →
        energy F (rotateLoop A u) < (q + ε) ^ 2 := by
  let η : ℝ := ε / (q + 1)
  have hden : 0 < q + 1 := by linarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hd⟩ := exists_relative_energy_upper F hη
  refine ⟨δ, hδ, fun A hA u hu => ?_⟩
  have hid : η * (q + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hlin : (1 + η) * q < q + ε := by nlinarith
  have hpos : 0 < (1 + η) ^ 2 := sq_pos_of_pos (by linarith)
  calc
    energy F (rotateLoop A u) ≤ (1 + η) ^ 2 * energy F u := hd A hA u
    _ < (1 + η) ^ 2 * q ^ 2 := mul_lt_mul_of_pos_left hu hpos
    _ = ((1 + η) * q) ^ 2 := (mul_pow _ _ _).symm
    _ < (q + ε) ^ 2 := (sq_lt_sq₀ (by positivity) (by positivity)).mpr hlin

theorem exists_homotopy_cut_radius (F : ReversibleMetric n) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u : SphereLoop n, u ∈ lev F q →
      ∀ y : Sphere n, dist (y : Ambient n) (basepoint u) < ρ →
        ∀ s : _root_.unitInterval, hom s u y ∈ lev F (q + ε) := by
  obtain ⟨δ, hδ, hd⟩ := exists_rotation_cut_control F hq hε
  obtain ⟨ρ, hρ, hrot⟩ := exists_uniform_path_radius (n := n) hδ
  refine ⟨min 1 ρ, lt_min zero_lt_one hρ, min_le_left 1 ρ, fun u hu y hy s => ?_⟩
  apply (Finsler.Birkhoff.mem_lev_iff (add_pos hq hε) _).mpr
  apply hd _ ?_ u ((Finsler.Birkhoff.mem_lev_iff hq _).mp hu)
  exact hrot _ _ (u.sphere_constraint ⟨0, by norm_num⟩)
    (by simpa using y.property) (hy.trans_le (min_le_right 1 ρ)) s

theorem exists_alignment_cut_radius (F : ReversibleMetric n) {q ε : ℝ}
    (hq : 0 < q) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ u : SphereLoop n, u ∈ lev F q →
      ∀ y : Sphere n, dist (y : Ambient n) (basepoint u) < ρ → align u y ∈ lev F (q + ε) := by
  obtain ⟨ρ, hρ, hρ1, hd⟩ := exists_homotopy_cut_radius F hq hε
  exact ⟨ρ, hρ, hρ1, fun u hu y hy => by simpa only [hom_one] using hd u hu y hy 1⟩


end
end Finsler.H1OrthogonalEnergy
