module

public import Finsler.Topology.LocalLabelPacket
public import Finsler.Topology.OddCircleFree

/-! an actual odd critical-circle label, with every ordinary
estimate, can be chosen to avoid the half-fixed set. -/

@[expose] public section

namespace Finsler.OddCirclePacket

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.CircleLabel Finsler.LocalLabelPacket Finsler.OddCircleFree
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical
open Finsler.PolygonDescent Finsler.PolygonSampling Finsler.AmbientSymmetry
open Finsler.AmbientPenalty
noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5

variable {n K : ℕ} [NeZero K]

theorem exists_odd_circle_packet (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c : ℝ} (hc : 0 < c)
    {ℓ : Set (Sphere n) × Bool} (hℓ : ℓ ∈ labels F hfin) {k : ℕ} (hk : Odd k)
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {K' : ℕ} [NeZero K'], k * (2 * N) = K' →
      ∀ {𝒰 : Set (ZMod K' → Ambient n)}, IsOpen 𝒰 →
      (∀ u ∈ circle F c ℓ, amb (samplePoly K' u) ∈ 𝒰) → ∀ {η : ℝ}, 0 < η →
        ∃ d : Packet n K', d.U ⊆ 𝒰 ∧ CircleSpec F hfin ℓ hℓ k N c η d ∧
          ∀ y ∈ d.U, rotA K' (k * N : ZMod K') y ≠ y := by
  obtain ⟨N₁, hN₁⟩ := exists_circle_packet F hn hfin hc hℓ hkc
  obtain ⟨N₂, hN₂⟩ := exists_free_circle_neighbourhood F hc ℓ
    ((mem_labels F hfin ℓ).mp hℓ) hk hkc
  refine ⟨max N₁ N₂, fun N hN _ K' _ hK 𝒰 h𝒰 hΓ η hη => ?_⟩
  obtain ⟨U, hU, hΓU, -, hfree⟩ := hN₂ N ((le_max_right _ _).trans hN) hK
  obtain ⟨d, hdU, hd⟩ := hN₁ N ((le_max_left _ _).trans hN) hK (h𝒰.inter hU)
    (fun u hu => ⟨hΓ u hu, hΓU u hu⟩) hη
  exact ⟨d, hdU.trans inter_subset_left, hd, fun y hy => hfree y (hdU hy).2⟩

theorem big_fixed_empty (F : ReversibleMetric n) {c η : ℝ}
    {Γ : Set (ZMod K → Ambient n)} {d : Packet n K} (hd : Analytic F c η Γ d)
    (a : ZMod K) (hfree : ∀ y ∈ d.U, rotA K a y ≠ y) :
    {Q : Om n K | Q ∈ d.big ∧ rotA K a Q.1 = Q.1} = ∅ := by
  rcases hd with ⟨-, -, -, -, -, -, hTU, -, -, -, -, -, -, -, -, hbT, -, -, -, -⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro Q ⟨hQ, hfix⟩
  exact hfree Q.1 (hTU (hbT Q hQ)) hfix

end

end Finsler.OddCirclePacket
