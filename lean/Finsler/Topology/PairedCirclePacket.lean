module

public import Finsler.Topology.LocalLabelPacket
public import Finsler.Topology.LocalLabelReverse
public import Finsler.Geometry.MilnorEquivariance

/-! a positive actual circle packet and its explicitly reversed
negative packet, with the same shift/root dimensions and complete ordinary lens estimates. -/

@[expose] public section

namespace Finsler.PairedCirclePacket

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.LocalLabelReverse Finsler.CircleLabel
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.PolygonDescent Finsler.PolygonSampling Finsler.RootIsolation
open Finsler.MilnorEquivariance Finsler.SobolevReverse Finsler.AmbientPenalty
open Finsler.AmbientSymmetry Finsler.PolygonDescentK
noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5

variable {n K : ℕ} [NeZero K]

theorem sampleSet_neg (F : ReversibleMetric n) (c : ℝ) (s : Set (Sphere n)) :
    sampleSet K (negCircle F c s) = revA K ⁻¹' sampleSet K (posCircle F c s) := by
  ext y
  change y ∈ (fun u => amb (samplePoly K u)) ''
    (Finsler.SobolevReverse.reverseSphere '' posCircle F c s) ↔
      revA K y ∈ (fun u => amb (samplePoly K u)) '' posCircle F c s
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    change amb (samplePoly K u) = revA K (amb (samplePoly K (reverseSphere u)))
    rw [samplePoly_reverse, amb_reversePolygon, revA_revA]
  · rintro ⟨u, hu, he⟩
    refine ⟨reverseSphere u, ⟨u, hu, rfl⟩, ?_⟩
    change amb (samplePoly K (reverseSphere u)) = y
    change amb (samplePoly K u) = revA K y at he
    rw [samplePoly_reverse, amb_reversePolygon, he, revA_revA]

theorem exists_paired_circle_packets (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    (s : Set (Sphere n)) (hs : s ∈ primeImages F) {k : ℕ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {M : ℕ} [NeZero M], k * (2 * N) = 2 * M →
      ∀ {𝒰 : Set (ZMod (2 * M) → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ posCircle F c s, amb (samplePoly (2 * M) u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
        ∃ d : Packet n (2 * M), d.U ⊆ 𝒰 ∧
          CircleSpec F hfin (s, true) ((mem_labels F hfin (s, true)).mpr hs) k N c η d ∧
          Analytic F c η (sampleSet (2 * M) (negCircle F c s)) (reversePacket M d) ∧
          HalfInvariant (M : ZMod (2 * M)) (reversePacket M d) ∧
          Model F c (reversePacket M d) := by
  have hpos : (s, true) ∈ labels F hfin := (mem_labels F hfin (s, true)).mpr hs
  obtain ⟨N₀, hN₀⟩ := exists_circle_packet F hn hfin hc hpos hkc
  refine ⟨N₀, fun N hN _ M _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
  obtain ⟨d, hdU, hd⟩ := hN₀ N hN hK h𝒰 hΓ hη
  have hkn : k * N = M := by nlinarith [hK]
  have hidx : (k * N : ZMod (2 * M)) = (M : ZMod (2 * M)) := by
    rw [← Nat.cast_mul, hkn]
  have hh := hd.2.1
  rw [hidx] at hh
  refine ⟨d, hdU, hd, ?_, reverse_half M hh, reverse_model M F hd.2.2.2.2⟩
  rw [sampleSet_neg]
  exact reverse_analytic M F hd.1

end

end Finsler.PairedCirclePacket
