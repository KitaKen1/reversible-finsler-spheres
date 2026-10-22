module

public import Finsler.Topology.EvenRootSupport
public import Finsler.Topology.FixedRootCatalogue

/-! One cutoff and one sampling threshold for both actual root parity cases in the finite catalogue. -/

@[expose] public section

namespace Finsler.RootCatalogueSupport

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.OrientedCritical Finsler.CriticalCircles Finsler.CircleLabel Finsler.CircleRoot Finsler.RootCatalogue
open Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.PolygonIterate Finsler.CircleHalfRotation
open Finsler.OddRootSupport Finsler.EvenRootSupport Finsler.FixedAmbientSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (F : ReversibleMetric n) (hfin : (primeImages F).Finite)

theorem exists_band_upper : ∃ upper : ℝ,
    ∀ ℓ (hℓ : ℓ ∈ labels F hfin) (k : ℕ), 0 < k →
      (isoBand F hfin (rootLevel F hfin ℓ hℓ k)).2 ≤ upper := by
  classical
  let C : Type := Σ ℓ : ↑(labels F hfin),
    ↑(Nat.divisors (2 * (Finsler.GeodesicFrames.iterData
      (labelGeod F ℓ.1 ((mem_labels F hfin ℓ.1).mp ℓ.2))).L))
  let level : C → ℝ := fun j => (j.2.1 : ℝ) * Real.sqrt
    (Finsler.LoopEnergy.energy F (chosen F j.1.1.1 ((mem_labels F hfin j.1.1).mp j.1.2)).loop)
  let b : C → ℝ := fun j => (isoBand F hfin (level j)).2
  refine ⟨∑ j : C, max 0 (b j), fun ℓ hℓ k hk => ?_⟩
  have hL : 0 < 2 * (Finsler.GeodesicFrames.iterData
      (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L := by
    have := (Finsler.GeodesicFrames.iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).one_le
    omega
  have hroot : rootOrder F hfin ℓ hℓ k ∈ Nat.divisors
      (2 * (Finsler.GeodesicFrames.iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hL.ne'⟩
  let j : C := ⟨⟨ℓ, hℓ⟩, ⟨rootOrder F hfin ℓ hℓ k, hroot⟩⟩
  exact (le_max_right 0 (b j)).trans
    (Finset.single_le_sum (fun i _ => le_max_left 0 (b i)) (Finset.mem_univ j))

theorem exists_uniform_support (hn : 1 ≤ n) :
    ∃ A N₀ : ℕ, RootCatalogue.Bounds F hfin A ∧ Finsler.FixedRootCatalogue.FixedBounds F hfin A ∧
      ∀ ℓ (hℓ : ℓ ∈ labels F hfin) (k : ℕ) (hk : 0 < k), ∀ s : ℕ, ∀ [NeZero s],
      s = rootOrder F hfin ℓ hℓ k → ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (m : ℕ) [NeZero m],
      Supports (fun z : TopCat.of {z : Om n (s * (2 * N)) |
          rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1)
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (isoBand_spec F hfin (rootLevel_pos F hfin ℓ hℓ hk)).1.le
            (isoBand_le F hfin (rootLevel F hfin ℓ hℓ k)) 2) (sq_nonneg (m : ℝ))) A := by
  obtain ⟨A, hA, hAf⟩ := Finsler.FixedRootCatalogue.exists_bounds F hfin hn
  obtain ⟨upper, hupper⟩ := exists_band_upper F hfin
  obtain ⟨N₁, hN₁⟩ := exists_even_transfer F hn upper
  obtain ⟨N₂, hN₂⟩ := exists_sample_ordinary F hn upper
  refine ⟨A, max N₁ N₂, hA, hAf, fun ℓ hℓ k hk s _ _ N hN _ m _ => ?_⟩
  obtain ⟨_, hf, hz⟩ := hA ℓ hℓ k hk
  obtain ⟨hff, hzf⟩ := hAf ℓ hℓ k hk
  have hl := (isoBand_spec F hfin (rootLevel_pos F hfin ℓ hℓ hk)).1
  have hab := isoBand_le F hfin (rootLevel F hfin ℓ hℓ k)
  have hu := hupper ℓ hℓ k hk
  by_cases hm : Even m
  · exact hN₁ N ((le_max_left _ _).trans hN) m s hm hl hab hu A hf hz
  · have hNN : N ≤ s * N := by
      simpa only [one_mul] using Nat.mul_le_mul_right N (Nat.one_le_iff_ne_zero.mpr (NeZero.ne s))
    exact Finsler.OddRootSupport.odd_support F m s N (Nat.not_even_iff_odd.mp hm) hl hab
      (hN₂ (s * N) (((le_max_right _ _).trans hN).trans hNN) hl hab hu) A hff hzf

end

end Finsler.RootCatalogueSupport
