module

public import Finsler.Definitions.PrimitiveRoot
public import Finsler.Definitions.Geodesic

/-! Prime representatives for the variational specification. Iterating a
variation and dividing its energy derivative by k² transfers stationarity
from an iterated loop to its root. The Euler--Lagrange comparison is separate. -/

@[expose] public section

namespace Finsler.Geodesics

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops TauCeti.Manifold Function
open scoped Manifold ContDiff

noncomputable section

variable {n : ℕ}

def iterateVariation (V : SmoothVariation n) (k : ℕ) : SmoothVariation n where
  family := fun p => V.family (p.1, (k : ℝ) * p.2)
  smooth := V.smooth.comp
    (contDiff_fst.prodMk (contDiff_const.mul contDiff_snd)).contMDiff
  periodic := by
    intro s t
    change V.family (s, (k : ℝ) * (t + 1)) = V.family (s, (k : ℝ) * t)
    rw [mul_add, mul_one]
    simpa using (V.periodic s).nat_mul k ((k : ℝ) * t)

theorem loopAt_iterateVariation (V : SmoothVariation n) (k : ℕ) (s : ℝ) :
    loopAt (iterateVariation V k) s = iterate (loopAt V s) k := by
  apply loop_ext
  intro t
  rfl

theorem regular_of_iterate {γ : SmoothLoop n} {k : ℕ} (hk : k ≠ 0)
    (hγ : Regular (iterate γ k)) : Regular γ := by
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hall : ∀ u : ℝ, curveVelocity (𝓡 n) γ ((k : ℝ) * u) ≠ 0 := by
    intro u hu
    have h := curveVelocity_comp (I := 𝓡 n) ((hasDerivAt_id u).const_mul (k : ℝ))
      (γ.smooth.mdifferentiableAt (by simp))
    simp only [id_eq, mul_one] at h
    have hne := hγ u
    change curveVelocity (𝓡 n) (γ ∘ fun t => (k : ℝ) * t) u ≠ 0 at hne
    rw [h, hu, smul_zero] at hne
    exact hne rfl
  intro t
  have he : (k : ℝ) * (t / k) = t := mul_div_cancel₀ t hkR
  have h := hall (t / k)
  rwa [he] at h

theorem stationary_of_iterate {F : ReversibleMetric n} {γ : SmoothLoop n} {k : ℕ}
    (hk : k ≠ 0) (hγ : Stationary F (iterate γ k)) : Stationary F γ := by
  intro V hV
  have hbase : loopAt (iterateVariation V k) 0 = iterate γ k := by
    rw [loopAt_iterateVariation, hV]
  have h := hγ (iterateVariation V k) hbase
  simp only [loopAt_iterateVariation, Finsler.LoopEnergy.energy_iterate] at h
  have hk2 : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hk)
  have h' := h.const_mul (((k : ℝ) ^ 2)⁻¹)
  simpa only [inv_mul_cancel_left₀ hk2, mul_zero] using h'

theorem exists_prime_representative {F : ReversibleMetric n} (γ : ClosedGeodesic F) :
    ∃ δ : ClosedGeodesic F, ∃ k : ℕ,
      0 < k ∧ Prime δ ∧ iterate δ.loop k = γ.loop ∧ image δ.loop = image γ.loop := by
  rcases exists_primitive_root γ.loop (closedGeodesic_nonconstant γ) with
    ⟨δ, k, hk, hprime, he⟩
  have hreg : Regular (iterate δ k) := he.symm ▸ γ.regular
  have hstat : Stationary F (iterate δ k) := he.symm ▸ γ.stationary
  let root : ClosedGeodesic F :=
    ⟨δ, regular_of_iterate (Nat.ne_of_gt hk) hreg,
      stationary_of_iterate (Nat.ne_of_gt hk) hstat⟩
  refine ⟨root, k, hk, hprime, he, ?_⟩
  change image δ = image γ.loop
  rw [← he, image_iterate δ (Nat.ne_of_gt hk)]

def closedImages (F : ReversibleMetric n) : Set (Set (Sphere n)) :=
  {s | ∃ γ : ClosedGeodesic F, image γ.loop = s}

theorem closedImages_eq_primeImages (F : ReversibleMetric n) :
    closedImages F = primeImages F := by
  ext s
  constructor
  · rintro ⟨γ, hγ⟩
    rcases exists_prime_representative γ with ⟨δ, k, hk, hprime, he, himage⟩
    exact ⟨δ, hprime, himage.trans hγ⟩
  · rintro ⟨γ, _, hγ⟩
    exact ⟨γ, hγ⟩

theorem infinite_closedImages_iff (F : ReversibleMetric n) :
    (closedImages F).Infinite ↔ InfinitePrimeImages F := by
  rw [closedImages_eq_primeImages]
  rfl

end

end Finsler.Geodesics
