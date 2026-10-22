module

public import Finsler.Topology.RootLabelPacket
public import Finsler.Topology.OddCirclePacket

/-! Select actual shared-root packets inside a half-fixed-free
neighbourhood whenever the multiplicity is odd, preserving every ordinary estimate. -/

@[expose] public section

namespace Finsler.MixedRootPacket

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.LocalLabelReverse Finsler.RootLabelPacket
open Finsler.CircleLabel Finsler.FiniteCirclePackets Finsler.PairedCirclePacket
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.PolygonSampling Finsler.PolygonDescent Finsler.RootIsolation Finsler.AmbientPenalty
open Finsler.AmbientSymmetry

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000

variable {n : ℕ}

def Retained (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k N K : ℕ) [NeZero N]
    (c : ℝ) (d : Packet n K) : Prop :=
  ∃ 𝒱 : Set (ZMod K → Ambient n), Shared F hfin ℓ hℓ k N K c 𝒱 d

theorem exists_circle_packet (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    {ℓ : Set (Sphere n) × Bool} (hℓ : ℓ ∈ labels F hfin) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K], k * (2 * N) = K →
      ∀ {𝒰 : Set (ZMod K → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
        ∃ d : Packet n K, d.U ⊆ 𝒰 ∧ CircleSpec F hfin ℓ hℓ k N c η d ∧
          Retained F hfin ℓ hℓ k N K c d ∧
          (Odd k → ∀ y ∈ d.U, rotA K (k * N : ZMod K) y ≠ y) := by
  classical
  obtain ⟨N₁, hN₁⟩ := Finsler.RootLabelPacket.exists_circle_packet F hn hfin hc hℓ hkc
  by_cases hk : Odd k
  · obtain ⟨N₂, hN₂⟩ := Finsler.OddCircleFree.exists_free_circle_neighbourhood F hc ℓ
      ((mem_labels F hfin ℓ).mp hℓ) hk hkc
    refine ⟨max N₁ N₂, fun N hN _ K _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
    obtain ⟨U, hU, hΓU, _, hfree⟩ := hN₂ N ((le_max_right _ _).trans hN) hK
    obtain ⟨d, hdU, hd, hshare⟩ := hN₁ N ((le_max_left _ _).trans hN) hK
      (h𝒰.inter hU) (fun u hu => ⟨hΓ u hu, hΓU u hu⟩) hη
    exact ⟨d, hdU.trans inter_subset_left, hd, ⟨𝒰 ∩ U, hshare⟩,
      fun _ y hy => hfree y (hdU hy).2⟩
  · refine ⟨N₁, fun N hN _ K _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
    obtain ⟨d, hdU, hd, hshare⟩ := hN₁ N hN hK h𝒰 hΓ hη
    exact ⟨d, hdU, hd, ⟨𝒰, hshare⟩, fun h => False.elim (hk h)⟩

theorem exists_paired_circle_packets (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    (s : Set (Sphere n)) (hs : s ∈ primeImages F) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {M : ℕ} [NeZero M], k * (2 * N) = 2 * M →
      ∀ {𝒰 : Set (ZMod (2 * M) → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ posCircle F c s, amb (samplePoly (2 * M) u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
        ∃ d : Packet n (2 * M), d.U ⊆ 𝒰 ∧ Spec F hfin s hs k N c η d ∧
          Retained F hfin (s, true) ((mem_labels F hfin (s, true)).mpr hs) k N (2 * M) c d ∧
          (Odd k → ∀ y ∈ d.U, rotA (2 * M) (M : ZMod (2 * M)) y ≠ y) := by
  have hpos : (s, true) ∈ labels F hfin := (mem_labels F hfin (s, true)).mpr hs
  obtain ⟨N₀, hN₀⟩ := exists_circle_packet F hn hfin hc hpos hkc
  refine ⟨N₀, fun N hN _ M _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
  obtain ⟨d, hdU, hd, hshare, hfree⟩ := hN₀ N hN hK h𝒰 hΓ hη
  have hkn : k * N = M := by nlinarith [hK]
  have hidx : (k * N : ZMod (2 * M)) = (M : ZMod (2 * M)) := by
    rw [← Nat.cast_mul, hkn]
  have hh := hd.2.1
  rw [hidx] at hh hfree
  refine ⟨d, hdU, ⟨hd, ?_, reverse_half M hh, reverse_model M F hd.2.2.2.2⟩, hshare, hfree⟩
  rw [sampleSet_neg]
  exact reverse_analytic M F hd.1

end

end Finsler.MixedRootPacket

