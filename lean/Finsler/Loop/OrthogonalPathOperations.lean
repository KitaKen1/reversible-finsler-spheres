module

public import Finsler.Loop.OrthogonalShortArc
public import Finsler.Analysis.H1SelfCutNeighborhood

/-! The actual H1 affine restriction and matched concatenation commute
with a constant ambient orthogonal map, in the original parametrization. -/

@[expose] public section
namespace Finsler.OrthogonalPathOperations

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.H1OrthogonalLength Finsler.H1ConcatContinuity
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

variable {n : ℕ} (A : Ambient n ≃ₗᵢ[ℝ] Ambient n)

theorem restrict_map (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    restrict (rotateData A u) hs ht hst = rotateData A (restrict u hs ht hst) := by
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_restrict _ hs ht hst hτ,
    representative_rotateData _ _ (aff_mem_Icc hs ht hτ),
    representative_rotateData _ _ hτ, representative_restrict _ hs ht hst hτ]

theorem concat_map (u v : Space n) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hmatch : continuousRepresentative u 1 = continuousRepresentative v 0) :
    concat (rotateData A u) (rotateData A v) ha0 ha1 = rotateData A (concat u v ha0 ha1) := by
  have hrot : continuousRepresentative (rotateData A u) 1 = continuousRepresentative (rotateData A v) 0 := by
    rw [representative_rotateData _ _ (by norm_num : (1 : ℝ) ∈ Icc 0 1),
      representative_rotateData _ _ (by norm_num : (0 : ℝ) ∈ Icc 0 1), hmatch]
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_rotateData _ _ hτ]
  by_cases hle : τ ≤ a
  · rw [representative_concat_left _ _ ha0 ha1 ⟨hτ.1, hle⟩,
      representative_concat_left _ _ ha0 ha1 ⟨hτ.1, hle⟩,
      representative_rotateData _ _ (left_time_mem ha0 hτ hle)]
  · have hge : a ≤ τ := (lt_of_not_ge hle).le
    rw [representative_concat_right _ _ ha0 ha1 hrot ⟨hge, hτ.2⟩,
      representative_concat_right _ _ ha0 ha1 hmatch ⟨hge, hτ.2⟩,
      representative_rotateData _ _ (right_time_mem ha1 hτ hge)]

end
end Finsler.OrthogonalPathOperations
