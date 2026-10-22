module

public import Finsler.Topology.OddRootSupport
public import Finsler.Topology.AmbientLoopPairs

/-! Ordinary loop support supplies the actual even-multiplicity fixed root at fine sampling. -/

@[expose] public section

namespace Finsler.EvenRootSupport

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientPenalty
open Finsler.AmbientSymmetry Finsler.PolygonIterate Finsler.CircleHalfRotation
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel Finsler.PolygonLoopPairs
open Finsler.PolygonDescent Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensFamily Finsler.OddRootSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_ordinary_transfer {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n) (upper : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {lam l u : ℝ}, 0 ≤ lam →
      ∀ (hl : 0 < l) (hlu : l ≤ u), u ≤ upper → ∀ A : ℕ,
      (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F hlu))) q)) →
      (∀ q, A ≤ q → ∀ z : H (triv (pairOf (lev_mono F hlu))) q, z = 0) →
      Supports (B := TopCat.of (Om n N)) (penW F N lam) (pow_le_pow_left₀ hl.le hlu 2) A := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := upper) S.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (upper ^ 2 / (e * S.δ ^ 2))
  refine ⟨max N₁ N₂, fun N hN _ lam l u hlam hl hlu hu A hf hz => ?_⟩
  let P : PolygonModelData F upper N :=
    PolygonModelData.mk S fun v hv s t hs ht hst =>
      hN₁ N ((le_max_left _ _).trans hN) (NeZero.pos N) v hv s t hs ht hst
  have hNR : upper ^ 2 / (e * S.δ ^ 2) < (N : ℝ) :=
    hN₂.trans_le (Nat.cast_le.mpr ((le_max_right _ _).trans hN))
  have hshort : ∀ q : ZMod N → Sphere n, energy F N q < u ^ 2 → ShortPolygon P.δ q :=
    fun q hq => short_of_energy_lt he S.pos hedge hu (hl.le.trans hlu) hNR q hq
  have heq := fun q => Finsler.AmbientLoopPairs.nonempty_loop_equiv P hlam hshort hl hlu hu q
  constructor
  · intro q
    obtain ⟨eq⟩ := heq q
    have := hf q
    exact Module.Finite.equiv eq
  · intro q hq z
    obtain ⟨eq⟩ := heq q
    exact eq.symm.injective ((hz q hq (eq.symm z)).trans eq.symm.map_zero.symm)

theorem exists_even_transfer {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n) (upper : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (m s : ℕ) [NeZero m] [NeZero s],
      Even m → ∀ {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u), u ≤ upper → ∀ A : ℕ,
      (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (lev_mono F hlu))) q)) →
      (∀ q, A ≤ q → ∀ z : H (triv (pairOf (lev_mono F hlu))) q, z = 0) →
      Supports (fun z : TopCat.of {z : Om n (s * (2 * N)) |
          rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F (s * (2 * N)) (1 / m) z.1.1)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl.le hlu 2) (sq_nonneg (m : ℝ))) A := by
  obtain ⟨N₀, hN₀⟩ := exists_ordinary_transfer F hn upper
  refine ⟨N₀, fun N hN _ m s _ _ hm l u hl hlu hu A hf hz => ?_⟩
  have hNN : N ≤ s * (2 * N) := by
    have h1 := Nat.mul_le_mul_right (2 * N) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne s))
    simp only [one_mul] at h1
    exact (show N ≤ 2 * N by omega).trans h1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  obtain ⟨hfi, hzi⟩ := hN₀ (s * (2 * N)) (hN.trans hNN)
    (le_of_lt (div_pos zero_lt_one hmpos)) hl hlu hu A hf hz
  obtain ⟨hfs, hzs⟩ := Finsler.ScaledRootSupport.cross_support ((m : ℝ) ^ 2)
    (sq_pos_of_pos hmpos) (pow_le_pow_left₀ hl.le hlu 2) A hfi hzi
  exact Finsler.RootParitySupport.even_support F m s N hm _ A hfs hzs

end

end Finsler.EvenRootSupport
