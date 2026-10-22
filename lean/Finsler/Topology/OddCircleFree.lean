module

public import Finsler.Geometry.OddHalfFree
public import Finsler.Topology.CircleRoot

/-! actual odd critical circles admit neighbourhoods disjoint
from the half-fixed set, before applying circle_label_half.  -/

@[expose] public section

namespace Finsler.OddCircleFree

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.PolygonDescent Finsler.PolygonSampling Finsler.CircleSampling
open Finsler.GeodesicFrames Finsler.CircleRoot Finsler.CriticalCircles
open Finsler.CriticalLevels Finsler.PhaseNullity Finsler.PolygonIterate Finsler.AmbientRotation
open Finsler.CircleHalfRotation Finsler.OddHalfFree
open Finsler.AmbientSymmetry Finsler.PolygonModel Finsler.RootIsolation
noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

theorem exists_sample_ne {c : ℝ} (hc : 0 < c) (ℓ : Set (Sphere n) × Bool)
    (hℓ : ℓ.1 ∈ primeImages F) {k : ℕ} (hk : Odd k)
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K], k * (2 * N) = K →
      ∀ u ∈ circle F c ℓ, rotA K (k * N : ZMod K) (amb (samplePoly K u)) ≠
        amb (samplePoly K u) := by
  have : NeZero k := ⟨by obtain ⟨j, hj⟩ := hk; omega⟩
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_facts_all M (labelGeod F ℓ hℓ)
  refine ⟨N₀, fun N hN _ K _ hK u hu => ?_⟩
  subst K
  have hu' : amb (samplePoly (k * (2 * N)) u) ∈
      sampleSet (k * (2 * N)) (circle F c ℓ) := ⟨u, hu, rfl⟩
  rw [circle_eq F hc ℓ hℓ hkc, sampleSet_root] at hu'
  obtain ⟨a, ha⟩ := hu'
  rw [← ha]
  have h := root_half_ne M (labelGeod F ℓ hℓ) (labelGeod_prime F ℓ hℓ) k 1 N
    (fun a => hN₀ a (2 * N) (by omega)) (by simpa only [one_mul] using hk) a
  unfold halfIndex at h
  rw [red_natCast] at h
  simpa only [one_mul, Nat.cast_mul] using h

theorem exists_free_circle_neighbourhood {c : ℝ} (hc : 0 < c)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ.1 ∈ primeImages F) {k : ℕ} (hk : Odd k)
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K], k * (2 * N) = K →
      ∃ U : Set (ZMod K → Ambient n), IsOpen U ∧
        (∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ U) ∧
        (∀ y, rotA K (k * N : ZMod K) y ∈ U ↔ y ∈ U) ∧
        ∀ y ∈ U, rotA K (k * N : ZMod K) y ≠ y := by
  obtain ⟨N₀, hN₀⟩ := exists_sample_ne F hc ℓ hℓ hk hkc
  refine ⟨N₀, fun N hN _ K _ hK => ?_⟩
  have hadd : (k * N : ZMod K) + (k * N : ZMod K) = 0 := by
    have he : k * N + k * N = K := by
      calc k * N + k * N = k * (2 * N) := by ring
           _ = K := hK
    rw [← Nat.cast_mul, ← Nat.cast_add, he]
    exact ZMod.natCast_self K
  obtain ⟨U, hU, hΓ, hUi, hfree⟩ := exists_free_neighbourhood (rotA K (k * N : ZMod K))
    (fun y => by rw [rotA_rotA, hadd, rotA_zero])
    (Γ := sampleSet K (circle F c ℓ)) (by
      rintro y ⟨u, hu, rfl⟩
      exact hN₀ N hN hK u hu)
  exact ⟨U, hU, fun u hu => hΓ ⟨u, hu, rfl⟩, hUi, hfree⟩

end

end Finsler.OddCircleFree
