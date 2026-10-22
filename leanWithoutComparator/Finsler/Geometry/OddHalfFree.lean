module

public import Finsler.Geometry.CircleHalfRotation

/-! odd total iteration has no half-fixed critical samples.
An invariant fixed-point-free neighbourhood can therefore be chosen before label assembly.
 -/

@[expose] public section

namespace Finsler.OddHalfFree

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonDescent Finsler.PolygonModel
open Finsler.SmoothSobolev Finsler.PolygonIterate Finsler.AmbientSymmetry Finsler.AmbientRotation
open Finsler.CircleFrameField Finsler.CircleHalfRotation Finsler.GeodesicFrames
open Finsler.RotationNatural Finsler.SamplePhase
noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {F : ReversibleMetric n}

theorem root_half_ne (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m N : ℕ) [NeZero s] [NeZero N]
    (hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N))
    (hodd : Odd (m * s)) (a : ℝ) :
    rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
      (amb (rootFamily g s N a)) ≠ amb (rootFamily g s N a) := by
  intro hfix
  let b := Int.fract a
  have hb0 : 0 ≤ b := Int.fract_nonneg a
  have hb1 : b < 1 := Int.fract_lt_one a
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨hb0, hb1.le⟩
  have hfixb : rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N))
      (amb (rootFamily g s N b)) = amb (rootFamily g s N b) := by
    change rotA _ _ (amb (rootFamily g s N (Int.fract a))) =
      amb (rootFamily g s N (Int.fract a))
    rw [← rootFamily_fract]
    exact hfix
  have heq : rootFamily g s N (b + 1 / 2) = rootFamily g s N b := by
    funext i
    apply Subtype.ext
    exact congrFun ((root_half_odd g m s N hodd b).trans hfixb) i
  by_cases h : b < 1 / 2
  · have hp : b + 1 / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    rcases phase_eq_of_root_eq M g hprime s N hf hb hp heq.symm with e | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      linarith
  · have hp : b - 1 / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hper := rootFamily_add_one g s N (b - 1 / 2)
    rw [show b - 1 / 2 + 1 = b + 1 / 2 by ring] at hper
    have heq' := hper.symm.trans heq
    rcases phase_eq_of_root_eq M g hprime s N hf hp hb heq' with e | ⟨e, e'⟩ | ⟨e, e'⟩ <;>
      linarith

theorem full_half_ne (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F)
    (hprime : Finsler.Geodesics.Prime g) (s m N : ℕ) [NeZero s] [NeZero m] [NeZero N]
    (hf : ∀ a : ℝ, SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) (2 * N))
    (hodd : Odd (m * s)) (a : ℝ) :
    rotA (m * (s * (2 * N))) (halfIndex m s N) (iterA m (s * (2 * N)) (amb (rootFamily g s N a))) ≠
      iterA m (s * (2 * N)) (amb (rootFamily g s N a)) := by
  intro h
  apply root_half_ne M g hprime s m N hf hodd a
  apply iterA_injective m (s * (2 * N))
  rw [iterA_rotA]
  exact h

theorem exists_free_neighbourhood {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : E →L[ℝ] E) (hτ : ∀ x, τ (τ x) = x) {Γ : Set E}
    (hΓ : ∀ x ∈ Γ, τ x ≠ x) :
    ∃ U : Set E, IsOpen U ∧ Γ ⊆ U ∧ (∀ x, τ x ∈ U ↔ x ∈ U) ∧ ∀ x ∈ U, τ x ≠ x := by
  refine ⟨{x | τ x ≠ x}, isOpen_ne_fun τ.continuous continuous_id, hΓ, ?_, fun _ hx => hx⟩
  intro x
  change τ (τ x) ≠ τ x ↔ τ x ≠ x
  rw [hτ]
  exact ne_comm

end

end Finsler.OddHalfFree
