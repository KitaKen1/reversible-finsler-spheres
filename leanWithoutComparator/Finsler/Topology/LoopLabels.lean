module

public import Finsler.Topology.LevelLabels

/-! The crossing of a critical level in the loop space. With finitely many prime closed geodesic
images, let c be the only critical level in [a₀, b₀], 0 < a₀ < c < b₀. For all cuts
a₀ ≤ a < c < b ≤ b₀ there are a number of vertices K, the labels with a critical circle at the
level c with their shifts b_ℓ = I(k) - I(gcd(k, 2L_ℓ)), dimensions r_ℓ of root labels and d > 0
such that for all tight cuts and times T ≥ 1 the ordinary cohomology of the loop pair (t_b, t_a)
has in every degree q in which it is finite dimensional the dimension Σ_ℓ r_ℓ(q - b_ℓ) over the
labels with b_ℓ ≤ q: the loop pair has the cohomology of the crossing pair of the penalized
energy with K vertices at the cuts a², b² (sampling and normalization) for every large K. -/

@[expose] public section

namespace Finsler.LoopLabels

open Module Filter Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.IntervalSobolev Finsler.SobolevEnergy Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel
open Finsler.PolygonDescent Finsler.CriticalLevels Finsler.CriticalCircles Finsler.EnergyDiagonal
open Finsler.AmbientPenalty Finsler.AmbientLoopPairs Finsler.GeodesicFrames
open Finsler.CircleRoot Finsler.LoopCrossingOriented Finsler.LensFamily Finsler.LevelLabels
open Finsler.CircleLabel
open CategoryTheory Finsler.BorelCochain Finsler.BorelLoop Finsler.PairTriple

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- **The crossing of a critical level in the loop space.** -/
theorem loop_level_labels (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {c a₀ b₀ : ℝ}
    (ha₀ : 0 < a₀) (hac : a₀ < c) (hcb : c < b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) {a b : ℝ} (hab : a ≤ b)
    (ha₀a : a₀ ≤ a) (hac' : a < c) (hcb' : c < b) (hbb₀ : b ≤ b₀) :
    ∃ (s : Finset (Set (Sphere n) × Bool)) (bi : Set (Sphere n) × Bool → ℕ)
      (r : Set (Sphere n) × Bool → ℝ → ℝ → ℝ → ℕ → ℕ) (d : ℝ),
      (∀ ℓ ∈ s, ∃ hℓ : ℓ ∈ labels F hfin, ∃ k : ℕ,
        (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
          (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c ∧
        bi ℓ = (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k -
          (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I
            (Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L)) ∧
          (∃ dr : ℝ, 0 < dr ∧ ∀ a' c' t : ℝ, 1 ≤ t → a' < c ^ 2 → c ^ 2 < c' → c' - a' < dr →
            ∀ j : ℕ, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
              ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
                Real.sqrt (Finsler.LoopEnergy.energy F
                  (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j) →
            r ℓ a' c' t j ≤ finrank (ZMod 2) (H (triv (pairOf (lev_mono F (isoBand_le F hfin
              ((Nat.gcd k (2 * (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).L) : ℝ) *
                Real.sqrt (Finsler.LoopEnergy.energy F
                  (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop)))))) j))) ∧
      0 < d ∧ ∀ a' c' t : ℝ, 1 ≤ t → a' < c ^ 2 → c ^ 2 < c' → c' - a' < d → ∀ q : ℕ,
        Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F hab))) q) →
        finrank (ZMod 2) (H (triv (pairOf (lev_mono F hab))) q) =
          ∑ ℓ ∈ s, if bi ℓ ≤ q then r ℓ a' c' t (q - bi ℓ) else 0 := by
  obtain ⟨L, Kmin, hL, hK⟩ := level_labels F hn hfin ha₀ hac hcb hone
  -- a polygon model of the band for all large numbers of vertices
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S₀.δ) (a := b₀) S₀.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (b₀ ^ 2 / (e * S₀.δ ^ 2))
  set K := L * (Kmin + N₁ + N₂ + 1) with hKdef
  have hKge : Kmin + N₁ + N₂ + 1 ≤ K := by
    rw [hKdef]
    exact Nat.le_mul_of_pos_left _ hL
  have : NeZero K := ⟨by omega⟩
  let M : PolygonModelData F b₀ K :=
    PolygonModelData.mk S₀ fun u hu s' t hs' ht hst =>
      hN₁ K (by omega) (by omega) u hu s' t hs' ht hst
  have hKR : b₀ ^ 2 / (e * S₀.δ ^ 2) < K := hN₂.trans_le (Nat.cast_le.mpr (by omega))
  have ha : 0 < a := ha₀.trans_le ha₀a
  have hb2 : b ^ 2 ≤ b₀ ^ 2 := pow_le_pow_left₀ (ha.le.trans hab) hbb₀ 2
  have hshort : ∀ q : ZMod K → Sphere n, PolygonDescent.energy F K q < b ^ 2 →
      ShortPolygon M.δ q := fun q hq =>
    short_of_energy_le he S₀.pos hedge hKR q (hq.le.trans hb2)
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  obtain ⟨s, bi, r, d, hs, hd, hcross⟩ := hK K (by omega) (Dvd.intro _ hKdef.symm) hab2 ha₀a hac'
    hcb' hbb₀
  refine ⟨s, bi, r, d, hs, hd, fun a' c' t ht ha' hc' hd' q hfin' => ?_⟩
  obtain ⟨e₁⟩ := nonempty_loop_equiv M zero_le_one hshort ha hab hbb₀ q
  have hfin₁ : Module.Finite (ZMod 2) (crossH (penW F K 1) hab2 q) := Module.Finite.equiv e₁
  rw [e₁.finrank_eq]
  exact hcross a' c' t ht ha' hc' hd' q hfin₁

end

end Finsler.LoopLabels
