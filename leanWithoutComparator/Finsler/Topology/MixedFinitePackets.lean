module

public import Finsler.Topology.MixedRootPacket

/-! Preserve the actual shared-root witnesses in complete packets and finite selections.
The negative packet is still the explicit reversal of the same positive packet. -/

@[expose] public section

namespace Finsler.MixedFinitePackets

open Finsler.MixedRootPacket
open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.LocalLabelReverse Finsler.CircleLabel
open Finsler.CircleLabelRoot Finsler.FiniteCirclePackets Finsler.PairedCirclePacket
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.PolygonSampling Finsler.PolygonDescent Finsler.RootIsolation Finsler.AmbientPenalty

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5

variable {n : ℕ}

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
          (∃ hN : NeZero (M / k i),
            @Retained n F hfin (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i))
              (k i) (M / k i) (2 * M) hN c (d i)) ∧
          (Odd (k i) → ∀ y ∈ (d i).U,
            Finsler.AmbientSymmetry.rotA (2 * M) (M : ZMod (2 * M)) y ≠ y) := by
  classical
  have hk : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have he : k i = 0 := by omega
    have he' := hkc i
    rw [he, Nat.cast_zero, zero_mul] at he'
    exact hc.ne he'
  have hex := fun i => Finsler.MixedRootPacket.exists_paired_circle_packets F hn hfin hc (s i) (hs i) (hkc i)
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
      (∃ hN : NeZero (M / k i),
        @Retained n F hfin (s i, true) ((mem_labels F hfin (s i, true)).mpr (hs i))
          (k i) (M / k i) (2 * M) hN c d) ∧
      (Odd (k i) → ∀ y ∈ d.U,
        Finsler.AmbientSymmetry.rotA (2 * M) (M : ZMod (2 * M)) y ≠ y) := by
    intro i
    have hN : NeZero (M / k i) := ⟨by have := hNlarge i; omega⟩
    have hK : k i * (2 * (M / k i)) = 2 * M := by
      have he := Nat.mul_div_cancel' ((hki i).trans hLM)
      calc k i * (2 * (M / k i)) = 2 * (k i * (M / k i)) := by ring
           _ = 2 * M := by rw [he]
    obtain ⟨d, hdU, hd, hshare, hfree⟩ := hN₀ i (M / k i)
      (by have := hNi i; have := hNlarge i; omega) hK (hU i) (hΓ i) hη
    exact ⟨d, hdU, hd, ⟨hN, hshare⟩, hfree⟩
  choose d hd using hp
  exact ⟨d, hd⟩

end

end Finsler.MixedFinitePackets

