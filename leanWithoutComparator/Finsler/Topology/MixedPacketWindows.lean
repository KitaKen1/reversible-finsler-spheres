module

public import Finsler.Topology.RootPacketWindows
public import Finsler.Topology.PacketWindowCatalogue
public import Finsler.Topology.MixedFinitePackets
public import Finsler.Topology.PairedFixedWindow

/-! Simultaneous packets retain actual root witnesses,
centered even windows and odd fixed-free neighbourhoods in the same finite family. -/

@[expose] public section

namespace Finsler.MixedPacketWindows

open Finsler.MixedRootPacket
open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.RootLabelPacket Finsler.FiniteCirclePackets
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.CircleLabel Finsler.CircleRoot
open Finsler.PolygonSampling Finsler.PolygonDescent Finsler.AmbientPenalty
open Finsler.CircleRootWindow Finsler.GeodesicFrames

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem exists_finite_above (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F) (k Q : ι → ℕ)
    (hkc : ∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F (s i) (hs i)).loop) = c) :
    ∃ L M₀ : ℕ, 0 < L ∧ (∀ i, k i ∣ L) ∧ ∀ M : ℕ, M₀ ≤ M → L ∣ M → ∀ [NeZero M],
      ∀ U : ι → Set (ZMod (2 * M) → Ambient n), (∀ i, IsOpen (U i)) →
      (∀ i, ∀ u ∈ posCircle F c (s i), amb (samplePoly (2 * M) u) ∈ U i) →
      ∀ {η : ℝ}, 0 < η → ∃ d : ι → Packet n (2 * M),
        ∀ i, Q i ≤ M / k i ∧ (d i).U ⊆ U i ∧
          Spec F hfin (s i) (hs i) (k i) (M / k i) c η (d i) ∧
          (∃ hN : NeZero (M / k i),
            @Retained n F hfin (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i))
              (k i) (M / k i) (2 * M) hN c (d i)) ∧
          (Odd (k i) → ∀ y ∈ (d i).U,
            Finsler.AmbientSymmetry.rotA (2 * M) (M : ZMod (2 * M)) y ≠ y) := by
  classical
  obtain ⟨L, M₁, hL, hkL, hdata⟩ :=
    Finsler.MixedFinitePackets.exists_finite_circle_packets F hn hfin hc s hs k hkc
  let Qmax : ℕ := Finset.univ.sup Q
  have hk : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have h0 : k i = 0 := by omega
    have h := hkc i
    rw [h0, Nat.cast_zero, zero_mul] at h
    exact hc.ne h
  refine ⟨L, max M₁ (L * (Qmax + 1)), hL, hkL,
    fun M hM hLM _ U hU hΓ η hη => ?_⟩
  obtain ⟨d, hd⟩ := hdata M ((le_max_left _ _).trans hM) hLM U hU hΓ hη
  refine ⟨d, fun i => ⟨?_, hd i⟩⟩
  have hQi : Q i ≤ Qmax := Finset.le_sup (Finset.mem_univ i)
  rw [Nat.le_div_iff_mul_le (hk i)]
  calc Q i * k i ≤ (Qmax + 1) * L :=
        Nat.mul_le_mul (by omega) (Nat.le_of_dvd hL (hkL i))
       _ = L * (Qmax + 1) := Nat.mul_comm _ _
       _ ≤ M := (le_max_right _ _).trans hM

def Ready (F : ReversibleMetric n) (hfin : (primeImages F).Finite)
    (ℓ : Set (Sphere n) × Bool) (hℓ : ℓ ∈ labels F hfin) (k A Q : ℕ) : Prop :=
  ∀ N : ℕ, Q ≤ N → ∀ [NeZero N] {K : ℕ} [NeZero K] {c : ℝ}
    {𝒰 : Set (ZMod K → Ambient n)} {d : Packet n K},
    Shared F hfin ℓ hℓ k N K c 𝒰 d →
    ∀ j : ℕ, ∀ [NeZero j], k = 2 * j →
      Window F (k * N : ZMod K) A
        ((iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I j) c d

theorem exists_packets (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {A : ℕ}
    (hcat : Finsler.PacketWindowCatalogue.Catalogue F hfin A)
    {c : ℝ} (hc : 0 < c) (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F)
    (k : ι → ℕ)
    (hkc : ∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F (s i) (hs i)).loop) = c) :
    ∃ L M₀ : ℕ, 0 < L ∧ (∀ i, k i ∣ L) ∧ ∀ M : ℕ, M₀ ≤ M → L ∣ M → ∀ [NeZero M],
      ∀ U : ι → Set (ZMod (2 * M) → Ambient n), (∀ i, IsOpen (U i)) →
      (∀ i, ∀ u ∈ posCircle F c (s i), amb (samplePoly (2 * M) u) ∈ U i) →
      ∀ {η : ℝ}, 0 < η → ∃ d : ι → Packet n (2 * M),
        ∀ i, (d i).U ⊆ U i ∧ Spec F hfin (s i) (hs i) (k i) (M / k i) c η (d i) ∧
          (∃ hN : NeZero (M / k i),
            @Retained n F hfin (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i))
              (k i) (M / k i) (2 * M) hN c (d i)) ∧
          (Odd (k i) → ∀ y ∈ (d i).U,
            Finsler.AmbientSymmetry.rotA (2 * M) (M : ZMod (2 * M)) y ≠ y) ∧
          ∀ j : ℕ, ∀ [NeZero j], k i = 2 * j →
            Window F (M : ZMod (2 * M)) A
              ((iterData (labelGeod F (s i, true) (hs i))).I j) c (d i) := by
  classical
  have hk : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have h0 : k i = 0 := by omega
    have h := hkc i
    rw [h0, Nat.cast_zero, zero_mul] at h
    exact hc.ne h
  have hready : ∀ i, ∃ Q : ℕ, Ready F hfin (s i, true)
      ((mem_labels F hfin (s i, true)).mpr (hs i)) (k i) A Q :=
    fun i => hcat (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i)) (k i) (hk i)
  choose Q hQ using hready
  obtain ⟨L, M₀, hL, hkL, hdata⟩ := exists_finite_above F hn hfin hc s hs k Q hkc
  refine ⟨L, M₀, hL, hkL, fun M hM hLM _ U hU hΓ η hη => ?_⟩
  obtain ⟨d, hd⟩ := hdata M hM hLM U hU hΓ hη
  refine ⟨d, fun i => ⟨(hd i).2.1, (hd i).2.2.1, (hd i).2.2.2.1, (hd i).2.2.2.2, ?_⟩⟩
  intro j _ hj
  obtain ⟨hN, 𝒱, hshare⟩ := (hd i).2.2.2.1
  letI := hN
  have h : Window F ((k i : ZMod (2 * M)) * ((M / k i : ℕ) : ZMod (2 * M))) A
      ((iterData (labelGeod F (s i, true) (hs i))).I j) c (d i) :=
    @hQ i (M / k i) (hd i).1 inferInstance (2 * M) inferInstance c 𝒱 (d i)
      hshare j inferInstance hj
  have hkn : k i * (M / k i) = M := Nat.mul_div_cancel' ((hkL i).trans hLM)
  have hidx : (k i : ZMod (2 * M)) * ((M / k i : ℕ) : ZMod (2 * M)) =
      (M : ZMod (2 * M)) := by
    rw [← Nat.cast_mul, hkn]
  rwa [hidx] at h


theorem exists_uniform_packets (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, Finsler.RootCatalogue.Bounds F hfin A ∧
      ∀ {c : ℝ}, 0 < c → ∀ (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F)
        (k : ι → ℕ),
      (∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F (s i) (hs i)).loop) = c) →
      ∃ L M₀ : ℕ, 0 < L ∧ (∀ i, k i ∣ L) ∧ ∀ M : ℕ, M₀ ≤ M → L ∣ M → ∀ [NeZero M],
      ∀ U : ι → Set (ZMod (2 * M) → Ambient n), (∀ i, IsOpen (U i)) →
      (∀ i, ∀ u ∈ posCircle F c (s i), amb (samplePoly (2 * M) u) ∈ U i) →
      ∀ {η : ℝ}, 0 < η → ∃ d : ι → Packet n (2 * M),
        ∀ i, (d i).U ⊆ U i ∧ Spec F hfin (s i) (hs i) (k i) (M / k i) c η (d i) ∧
          (∃ hN : NeZero (M / k i),
            @Retained n F hfin (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i))
              (k i) (M / k i) (2 * M) hN c (d i)) ∧
          (Odd (k i) → ∀ y ∈ (d i).U,
            Finsler.AmbientSymmetry.rotA (2 * M) (M : ZMod (2 * M)) y ≠ y) ∧
          ∀ j : ℕ, ∀ [NeZero j], k i = 2 * j →
            Window F (M : ZMod (2 * M)) A
              ((iterData (labelGeod F (s i, true) (hs i))).I j) c (d i) := by
  obtain ⟨A, hA, hcat⟩ := Finsler.PacketWindowCatalogue.exists_catalogue F hn hfin
  exact ⟨A, hA, fun {c} hc s hs k hkc => exists_packets F hn hfin hcat hc s hs k hkc⟩

end

end Finsler.MixedPacketWindows

