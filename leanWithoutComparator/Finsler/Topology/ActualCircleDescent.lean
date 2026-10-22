module

public import Finsler.Topology.CirclePacketFamily
public import Finsler.Topology.CirclePacketGeometry
public import Finsler.Topology.LevelLabels

/-! An actual K-equivariant ambient descent at an isolated positive critical level.
The active prime images, both orientations, uniform sampling bounds, disjoint ambient
neighbourhoods and critical-band coverage are all constructed here. The local packets retain
their ordinary lens models and root bounds. Fixed-part comparisons and HalfTight are separate. -/

@[expose] public section

namespace Finsler.ActualCircleDescent

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.Loops
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.PolygonModel Finsler.PolygonDescent Finsler.PolygonSampling Finsler.PolygonCritical
open Finsler.PolygonLoop Finsler.IntervalSobolev Finsler.PhaseNullity Finsler.SamplePhase
open Finsler.SmoothSobolev Finsler.EnergySphereSmooth Finsler.AmbientPenalty
open Finsler.EnergyDiagonal
open Finsler.LoopCrossingOriented
open Finsler.LocalLabelPacket Finsler.FiniteCirclePackets Finsler.CirclePacketFamily
open Finsler.CirclePacketGeometry
open Finsler.CircleRoot
open scoped Topology ContDiff NNReal

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 2400000

variable {n : ℕ}

/-- For all sufficiently large common multiples of the active iteration multiplicities,
complete actual-circle packets admit a global descent commuting with reversal and half-turn.
All geometric inputs to the packet-family construction are discharged. -/
theorem exists_actual_global (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (hac : a₀ < c) (hcb : c < b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) :
    ∃ k : Active F hfin c → ℕ,
      (∀ i, 0 < k i ∧ (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
        (chosen F i.1 (active_mem_prime F hfin c i)).loop) = c) ∧
      ∃ L Mmin : ℕ, 0 < L ∧ (∀ i, k i ∣ L) ∧
        ∀ M : ℕ, Mmin ≤ M → L ∣ M → ∀ [NeZero M] {η : ℝ}, 0 < η →
          ∃ d : Active F hfin c → Packet n (2 * M),
            (∀ i, Spec F hfin i.1 (active_mem_prime F hfin c i)
              (k i) (M / k i) c η (d i)) ∧
            Nonempty (Global M F (packetFamily M d) (a₀ ^ 2) (b₀ ^ 2)) := by
  classical
  have hc : 0 < c := ha₀.trans hac
  have hab₀ : a₀ ≤ b₀ := (hac.trans hcb).le
  let ι := Active F hfin c
  let s : ι → Set (Sphere n) := Subtype.val
  have hs : ∀ i, s i ∈ primeImages F := active_mem_prime F hfin c
  choose k hkpos hkc using exists_multiplicity F hfin c
  have hkc' := fun i => hkc i (hs i)
  obtain ⟨L, M₀, hL, hkL, hglobal⟩ :=
    exists_finite_global F hn hfin hc s hs k hkc'
  obtain ⟨S₀⟩ := exists_segmentData F
  obtain ⟨δ₁, hδ₁, hC1⟩ := exists_ambientMinEnergy_contDiffAt_one F
  let S := shrink S₀ (lt_min S₀.pos hδ₁) (min_le_left _ _)
  have hSδ : S.δ ≤ δ₁ := min_le_right _ _
  have hsf : ∀ p : ι × Bool, ∃ K₀ : ℕ, ∀ a : ℝ, ∀ K : ℕ, K₀ ≤ K →
      ∀ [NeZero K], SampleFacts S (ofSmooth (shift (labelGeod F (s p.1, p.2) (hs p.1)).loop a)) K :=
    fun p => exists_sample_facts_all S (labelGeod F (s p.1, p.2) (hs p.1))
  choose K₀ hK₀ using hsf
  let Nmax := Finset.univ.sup K₀
  have hNmax : ∀ p, K₀ p ≤ Nmax := fun p => Finset.le_sup (Finset.mem_univ p)
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := b₀) S.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (b₀ ^ 2 / (e * S.δ ^ 2))
  refine ⟨k, fun i => ⟨hkpos i, hkc' i⟩,
    L, M₀ + L * (Nmax + 1) + N₁ + N₂, hL, hkL,
    fun M hM hLM _ η hη => ?_⟩
  have hkn : ∀ i, k i * (M / k i) = M :=
    fun i => Nat.mul_div_cancel' ((hkL i).trans hLM)
  have hNM : ∀ i, Nmax + 1 ≤ M / k i := by
    intro i
    rw [Nat.le_div_iff_mul_le (hkpos i)]
    calc (Nmax + 1) * k i ≤ (Nmax + 1) * L :=
          Nat.mul_le_mul_left _ (Nat.le_of_dvd hL (hkL i))
      _ = L * (Nmax + 1) := Nat.mul_comm _ _
      _ ≤ M := by omega
  have hNi : ∀ i, NeZero (M / k i) := fun i => ⟨by have := hNM i; omega⟩
  have h2N : ∀ i, 1 < 2 * (M / k i) := fun i => by have := hNM i; omega
  have hK : ∀ i, k i * (2 * (M / k i)) = 2 * M := by
    intro i
    calc k i * (2 * (M / k i)) = 2 * (k i * (M / k i)) := by ring
      _ = 2 * M := by rw [hkn i]
  let MK : PolygonModelData F b₀ (2 * M) :=
    PolygonModelData.mk S fun u hu s' t hs' ht hst =>
      hN₁ (2 * M) (by omega) (Nat.mul_pos two_pos (Nat.pos_of_neZero M)) u hu s' t hs' ht hst
  have hKR : b₀ ^ 2 / (e * S.δ ^ 2) < (2 * M : ℕ) :=
    hN₂.trans_le (Nat.cast_le.mpr (by omega))
  have hshort : ∀ q : ZMod (2 * M) → Sphere n,
      PolygonDescent.energy F (2 * M) q ≤ b₀ ^ 2 → ShortPolygon MK.δ q :=
    fun q hq => short_of_energy_le he S.pos hedge hKR q hq
  have hCK : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < MK.δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)) :=
    fun P Q h => hC1 P Q (h.trans_le hSδ)
  have hrec : ∀ p : ι × Bool, ∀ u ∈ circle F c (s p.1, p.2),
      ∃ hq : ShortPolygon MK.δ (samplePoly (2 * M) u),
        broken MK ⟨samplePoly (2 * M) u, hq⟩ = u := by
    intro p
    letI := hNi p.1
    apply circle_reconstruction MK hc (s p.1) (hs p.1) p.2 (k p.1)
      (M / k p.1) (h2N p.1) (hK p.1) (hkc' p.1)
    intro a
    exact hK₀ p a (2 * (M / k p.1)) (by have := hNmax p; have := hNM p.1; omega)
  obtain ⟨U, hU, hUdis, hUrev⟩ :=
    exists_circle_neighbourhoods MK c s Subtype.val_injective hrec
  have hcover : ∀ q : ZMod (2 * M) → Sphere n,
      a₀ ^ 2 ≤ PolygonDescent.energy F (2 * M) q →
      PolygonDescent.energy F (2 * M) q ≤ b₀ ^ 2 → PolyCritical F (2 * M) q →
      ∃ p : ι × Bool, (incl q : Om n (2 * M)).1 ∈
        Finsler.RootIsolation.sampleSet (2 * M) (circle F c (s p.1, p.2)) := by
    intro q ha hb hq
    exact critical_band_cover MK hfin ha₀ hab₀ hone hshort hq ha hb
  obtain ⟨d, hd, hg⟩ := hglobal M (by omega) hLM hCK hshort U
    (fun i => (hU i).1) (fun i => (hU i).2) hUdis hUrev hcover hη
  exact ⟨d, fun i => (hd i).2, hg⟩

end

end Finsler.ActualCircleDescent
