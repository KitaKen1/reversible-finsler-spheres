module

public import Finsler.Topology.RootIsolation
public import Finsler.Geometry.CircleSampling
public import Finsler.Geometry.RootBand

/-! The closed geodesic of a label and its circles. The closed geodesic of a label (a prime
image with an orientation) is the chosen prime closed geodesic with that image or its reversal;
it is prime and has the energy of the chosen one. If k √E = c > 0 for the chosen geodesic, the
critical circle of the label at the level c is the set of rotations of the k-fold iterate of the
closed geodesic of the label, and its loops have energy c². The samples of the rotations of the
s-fold iterate with s (2 N) vertices are the root polygons. -/

@[expose] public section

namespace Finsler.CircleRoot

open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.Loops
open Finsler.SmoothSobolev Finsler.SobolevReverse Finsler.CriticalLevels Finsler.OrientedCritical
open Finsler.CriticalCircles Finsler.RootIsolation Finsler.CircleSampling Finsler.GeodesicFrames
open Finsler.PolygonSampling Finsler.PolygonDescent
open Set

noncomputable section

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

variable {n : ℕ} (F : ReversibleMetric n)

/-- The closed geodesic of a label. -/
def labelGeod (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ.1 ∈ primeImages F) : ClosedGeodesic F :=
  cond ℓ.2 (chosen F ℓ.1 hℓ) (reverseGeodesic (chosen F ℓ.1 hℓ))

theorem labelGeod_prime (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ.1 ∈ primeImages F) :
    Prime (labelGeod F ℓ hℓ) := by
  obtain ⟨s, o⟩ := ℓ
  cases o
  · exact (prime_reverseGeodesic_iff _).mpr (chosen_prime F s hℓ)
  · exact chosen_prime F s hℓ

theorem energy_labelGeod (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ.1 ∈ primeImages F) :
    Finsler.LoopEnergy.energy F (labelGeod F ℓ hℓ).loop =
      Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ).loop := by
  obtain ⟨s, o⟩ := ℓ
  cases o
  · exact Finsler.LoopEnergy.energy_reverse F _
  · rfl

omit F in
theorem reverse_shift_iterate (γ : SmoothLoop n) (k : ℕ) (a : ℝ) :
    reverse (shift (iterate γ k) a) = shift (iterate (reverse γ) k) (-a) := by
  apply loop_ext
  intro t
  change γ ((k : ℝ) * (-t + a)) = γ (-((k : ℝ) * (t + -a)))
  congr 1
  ring

/-- The positive critical circle as the rotations of an iterate. -/
theorem posCircle_eq {c : ℝ} (hc : 0 < c) {s : Set (Sphere n)} (hs : s ∈ primeImages F) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c) :
    posCircle F c s = range fun a : ℝ => ofSmooth (shift (iterate (chosen F s hs).loop k) a) := by
  have hE := chosen_energy_pos F s hs
  ext γ
  constructor
  · rintro ⟨hs', k', θ, -, hk'c, rfl⟩
    have hkk : k' = k := by
      have h : (k' : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) =
          (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) :=
        hk'c.trans hkc.symm
      exact_mod_cast mul_right_cancel₀ hE.ne' h
    subst hkk
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact ⟨a, ofSmooth_shift _ a⟩
  · rintro ⟨a, rfl⟩
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, Nat.cast_zero, zero_mul] at hkc
        exact absurd hkc hc.ne
      · exact h
    exact ⟨hs, k, (a : Circ), hk, hkc, ofSmooth_shift _ a⟩

/-- **The critical circle of a label as the rotations of an iterate.** -/
theorem circle_eq {c : ℝ} (hc : 0 < c) (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ.1 ∈ primeImages F)
    {k : ℕ} (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ).loop) = c) :
    circle F c ℓ = range fun a : ℝ => ofSmooth (shift (iterate (labelGeod F ℓ hℓ).loop k) a) := by
  obtain ⟨s, o⟩ := ℓ
  cases o
  · change reverseSphere '' posCircle F c s = _
    rw [posCircle_eq F hc hℓ hkc]
    ext γ
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      refine ⟨-a, ?_⟩
      change ofSmooth (shift (iterate (reverse (chosen F s hℓ).loop) k) (-a)) =
        reverseSphere (ofSmooth (shift (iterate (chosen F s hℓ).loop k) a))
      rw [reverseSphere_ofSmooth, reverse_shift_iterate]
    · rintro ⟨a, rfl⟩
      refine ⟨_, ⟨-a, rfl⟩, ?_⟩
      change reverseSphere (ofSmooth (shift (iterate (chosen F s hℓ).loop k) (-a))) =
        ofSmooth (shift (iterate (reverse (chosen F s hℓ).loop) k) a)
      rw [reverseSphere_ofSmooth, reverse_shift_iterate, neg_neg]
  · exact posCircle_eq F hc hℓ hkc

/-- **The loops of a critical circle have energy c².** -/
theorem circle_energy {c : ℝ} (hc : 0 < c) (ℓ : Set (Sphere n) × Bool)
    (hℓ : ℓ.1 ∈ primeImages F) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hℓ).loop) = c) :
    ∀ u ∈ circle F c ℓ, Finsler.SobolevEnergy.energy F u = c ^ 2 := by
  rw [circle_eq F hc ℓ hℓ hkc]
  rintro _ ⟨a, rfl⟩
  rw [energy_ofSmooth_shift, energy_ofSmooth_iterate, energy_ofSmooth, energy_labelGeod, ← hkc,
    mul_pow, Real.sq_sqrt (Finsler.LoopEnergy.energy_nonneg F _)]

/-- **The loops of every critical circle of a level c have energy c².** -/
theorem energy_of_mem_circle {c : ℝ} (ℓ : Set (Sphere n) × Bool) :
    ∀ u ∈ circle F c ℓ, Finsler.SobolevEnergy.energy F u = c ^ 2 := by
  have hpos : ∀ s : Set (Sphere n), ∀ u ∈ posCircle F c s,
      Finsler.SobolevEnergy.energy F u = c ^ 2 := by
    rintro s _ ⟨hs, k, θ, -, hkc, rfl⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [← ofSmooth_shift, energy_ofSmooth_shift, energy_ofSmooth_iterate, energy_ofSmooth, ← hkc,
      mul_pow, Real.sq_sqrt (Finsler.LoopEnergy.energy_nonneg F _)]
  obtain ⟨s, o⟩ := ℓ
  cases o
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hs, k, θ, -, hkc, rfl⟩ := hu
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective θ
    rw [← ofSmooth_shift, reverseSphere_ofSmooth, energy_ofSmooth_reverse, energy_ofSmooth_shift,
      energy_ofSmooth_iterate, energy_ofSmooth, ← hkc, mul_pow,
      Real.sq_sqrt (Finsler.LoopEnergy.energy_nonneg F _)]
  · exact hpos s

/-- **The sampled root circle is the set of root polygons.** -/
theorem sampleSet_root (g : ClosedGeodesic F) (s N : ℕ) [NeZero s] [NeZero N] :
    sampleSet (s * (2 * N)) (range fun a : ℝ => ofSmooth (shift (iterate g.loop s) a)) =
      range fun a : ℝ => amb (rootFamily g s N a) := by
  have hs : (s : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne s
  ext z
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨(s : ℝ) * a, (sample_eq_root g s a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨_, ⟨a / s, rfl⟩, ?_⟩
    change amb (samplePoly (s * (2 * N)) (ofSmooth (shift (iterate g.loop s) (a / s)))) = _
    rw [sample_eq_root g s (a / s), mul_div_cancel₀ a hs]

end

end Finsler.CircleRoot
