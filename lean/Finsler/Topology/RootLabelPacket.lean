module

public import Finsler.Topology.CircleLabelRoot
public import Finsler.Topology.FiniteCirclePackets

/-! Preserve the actual shared-root witnesses in complete packets and finite selections.
The negative packet is still the explicit reversal of the same positive packet. -/

@[expose] public section

namespace Finsler.RootLabelPacket

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.LocalLabelReverse Finsler.CircleLabel
open Finsler.CircleLabelRoot Finsler.FiniteCirclePackets Finsler.PairedCirclePacket
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.PolygonSampling Finsler.PolygonDescent Finsler.RootIsolation Finsler.AmbientPenalty

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5

variable {n : ℕ}

def Shared (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k N K : ℕ) [NeZero N]
    (c : ℝ) (𝒰 : Set (ZMod K → Ambient n)) (d : Packet n K) : Prop :=
  ActualSharedRoot F hfin ℓ hℓ k N K d.b c 𝒰 d.U d.W d.β d.T d.big d.small

theorem exists_circle_packet (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    {ℓ : Set (Sphere n) × Bool} (hℓ : ℓ ∈ labels F hfin) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K], k * (2 * N) = K →
      ∀ {𝒰 : Set (ZMod K → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ circle F c ℓ, amb (samplePoly K u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
        ∃ d : Packet n K, d.U ⊆ 𝒰 ∧ CircleSpec F hfin ℓ hℓ k N c η d ∧
          Shared F hfin ℓ hℓ k N K c 𝒰 d := by
  obtain ⟨N₀, hN₀⟩ := circle_label_half_root F hn hfin hc hℓ hkc
  refine ⟨N₀, fun N hN _ K _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
  obtain ⟨b, r, U, W, β, C, T, big, small, hshare, hUi, hTi, hWi, hβi, hbi, hsi,
    hb, hU, hU𝒰, hUr, hW, hWle, hWlt, hT, hTU, hβT, hβd, hβb, hβle, hβlt,
    hbig, hsmall, hsb, hbT, hCs, hCU, hΓT, hC, hroot, hmodel⟩ := hN₀ N hN hK h𝒰 hΓ hη
  refine ⟨⟨b, r, U, W, β, C, T, big, small⟩, hU𝒰, ?_, hshare⟩
  refine ⟨⟨hU, hUr, hW, hWle, hWlt, hT, hTU, hβT, hβd, hβb, hβle, hβlt,
    hbig, hsmall, hsb, hbT, hCs, hCU, ?_, hC⟩,
    ⟨hUi, hTi, hWi, hβi, hbi, hsi⟩, hb, hroot, hmodel⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hΓT u hu

theorem exists_paired_circle_packets (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    (s : Set (Sphere n)) (hs : s ∈ primeImages F) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {M : ℕ} [NeZero M], k * (2 * N) = 2 * M →
      ∀ {𝒰 : Set (ZMod (2 * M) → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ posCircle F c s, amb (samplePoly (2 * M) u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
        ∃ d : Packet n (2 * M), d.U ⊆ 𝒰 ∧ Spec F hfin s hs k N c η d ∧
          Shared F hfin (s, true) ((mem_labels F hfin (s, true)).mpr hs) k N (2 * M) c 𝒰 d := by
  have hpos : (s, true) ∈ labels F hfin := (mem_labels F hfin (s, true)).mpr hs
  obtain ⟨N₀, hN₀⟩ := exists_circle_packet F hn hfin hc hpos hkc
  refine ⟨N₀, fun N hN _ M _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
  obtain ⟨d, hdU, hd, hshare⟩ := hN₀ N hN hK h𝒰 hΓ hη
  have hkn : k * N = M := by nlinarith [hK]
  have hidx : (k * N : ZMod (2 * M)) = (M : ZMod (2 * M)) := by
    rw [← Nat.cast_mul, hkn]
  have hh := hd.2.1
  rw [hidx] at hh
  refine ⟨d, hdU, ⟨hd, ?_, reverse_half M hh, reverse_model M F hd.2.2.2.2⟩, hshare⟩
  rw [sampleSet_neg]
  exact reverse_analytic M F hd.1

theorem exists_finite_circle_packets {ι : Type*} [Fintype ι]
    (F : ReversibleMetric n) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {c : ℝ} (hc : 0 < c) (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F)
    (k : ι → ℕ)
    (hkc : ∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F (s i) (hs i)).loop) = c) :
    ∃ L M₀ : ℕ, 0 < L ∧ (∀ i, k i ∣ L) ∧ ∀ M : ℕ, M₀ ≤ M → L ∣ M → ∀ [NeZero M],
      ∀ U : ι → Set (ZMod (2 * M) → Ambient n), (∀ i, IsOpen (U i)) →
      (∀ i, ∀ u ∈ posCircle F c (s i), amb (samplePoly (2 * M) u) ∈ U i) →
      ∀ {η : ℝ}, 0 < η → ∃ d : ι → Packet n (2 * M),
        ∀ i, (d i).U ⊆ U i ∧ Spec F hfin (s i) (hs i) (k i) (M / k i) c η (d i) ∧
          ∃ hN : NeZero (M / k i),
            @Shared n F hfin (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i))
              (k i) (M / k i) (2 * M) hN c (U i) (d i) := by
  classical
  have hk : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have he : k i = 0 := by omega
    have he' := hkc i
    rw [he, Nat.cast_zero, zero_mul] at he'
    exact hc.ne he'
  have hex := fun i => exists_paired_circle_packets F hn hfin hc (s i) (hs i) (hkc i)
  choose N₀ hN₀ using hex
  let L : ℕ := ∏ i, k i
  let Nmax : ℕ := Finset.univ.sup N₀
  have hL : 0 < L := Finset.prod_pos fun i _ => hk i
  have hki : ∀ i, k i ∣ L := fun i => Finset.dvd_prod_of_mem k (Finset.mem_univ i)
  have hNi : ∀ i, N₀ i ≤ Nmax := fun i => Finset.le_sup (Finset.mem_univ i)
  refine ⟨L, L * (Nmax + 1), hL, hki, fun M hM hLM _ U hU hΓ η hη => ?_⟩
  have hNlarge : ∀ i, Nmax + 1 ≤ M / k i := by
    intro i
    rw [Nat.le_div_iff_mul_le (hk i)]
    calc (Nmax + 1) * k i ≤ (Nmax + 1) * L :=
          Nat.mul_le_mul_left _ (Nat.le_of_dvd hL (hki i))
         _ = L * (Nmax + 1) := Nat.mul_comm _ _
         _ ≤ M := hM
  have hp : ∀ i, ∃ d : Packet n (2 * M), d.U ⊆ U i ∧
      Spec F hfin (s i) (hs i) (k i) (M / k i) c η d ∧
      ∃ hN : NeZero (M / k i),
        @Shared n F hfin (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i))
          (k i) (M / k i) (2 * M) hN c (U i) d := by
    intro i
    have hN : NeZero (M / k i) := ⟨by have := hNlarge i; omega⟩
    have hK : k i * (2 * (M / k i)) = 2 * M := by
      have he := Nat.mul_div_cancel' ((hki i).trans hLM)
      calc k i * (2 * (M / k i)) = 2 * (k i * (M / k i)) := by ring
           _ = 2 * M := by rw [he]
    obtain ⟨d, hdU, hd, hshare⟩ := hN₀ i (M / k i)
      (by have := hNi i; have := hNlarge i; omega) hK (hU i) (hΓ i) hη
    exact ⟨d, hdU, hd, hN, hshare⟩
  choose d hd using hp
  exact ⟨d, hd⟩

end

end Finsler.RootLabelPacket
