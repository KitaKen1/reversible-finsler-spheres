module

public import Finsler.Topology.PacketDeformation

/-! choose the actual lower and upper cut-flow times from the
compact deformed bands and strict regular-strip descent. -/

@[expose] public section

namespace Finsler.PacketCutTimes

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.CirclePacketFamily Finsler.PacketDeformation
open Finsler.AmbientPenalty Finsler.FlowLens Finsler.CutMove
open scoped NNReal

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {c η a₀ b₀ : ℝ} {p : ι → Packet n (2 * M)}
variable {Γ : ι → Set (ZMod (2 * M) → Ambient n)}

theorem exists_cut_times (han : ∀ i, Analytic F c η (Γ i) (p i))
    (hdis : ∀ i j, i ≠ j → Disjoint (p i).U (p j).U)
    (G : CirclePacketFamily.Global M F p a₀ b₀) (hn : 1 ≤ n) (hη : 0 ≤ η)
    {aw a b bw : ℝ} (ha₀ : a₀ ≤ aw - η) (hb₀ : bw + η ≤ b₀)
    (haw : aw ≤ a) (hac : a < c ^ 2) (hcb : c ^ 2 < b) (hbw : b ≤ bw) :
    ∃ τl τu : ℝ, 0 ≤ τl ∧ 0 ≤ τu ∧
      (∀ Q : Om n (2 * M), deformed M F p Q.1 < a →
        deformed M F p ((PacketDeformation.Global.descent G).flow τl Q).1 < aw) ∧
      ∀ Q : Om n (2 * M), deformed M F p Q.1 < bw →
        deformed M F p ((PacketDeformation.Global.descent G).flow τu Q).1 < b := by
  have hl : ∀ Q : Om n (2 * M), aw ≤ deformed M F p Q.1 →
      deformed M F p Q.1 ≤ a →
      deformed M F p ((PacketDeformation.Global.descent G).flow 1 Q).1 < deformed M F p Q.1 := by
    intro Q hQa hQb
    exact PacketDeformation.Global.strict_regular han hdis G hη ha₀ hb₀ Q hQa
      (hQb.trans (hac.le.trans (hcb.le.trans hbw))) (ne_of_lt (hQb.trans_lt hac))
  have hu : ∀ Q : Om n (2 * M), b ≤ deformed M F p Q.1 →
      deformed M F p Q.1 ≤ bw →
      deformed M F p ((PacketDeformation.Global.descent G).flow 1 Q).1 < deformed M F p Q.1 := by
    intro Q hQa hQb
    exact PacketDeformation.Global.strict_regular han hdis G hη ha₀ hb₀ Q
      (haw.trans (hac.le.trans (hcb.le.trans hQa))) hQb (ne_of_gt (hcb.trans_le hQa))
  obtain ⟨τl, hτl, hpushl⟩ := exists_push_lt (PacketDeformation.Global.descent G)
    (deformed_continuous han hn) (deformed_band_compact han hdis hn hη aw a) hl
  obtain ⟨τu, hτu, hpushu⟩ := exists_push_lt (PacketDeformation.Global.descent G)
    (deformed_continuous han hn) (deformed_band_compact han hdis hn hη b bw) hu
  exact ⟨τl, τu, hτl, hτu, hpushl, hpushu⟩

end

end Finsler.PacketCutTimes
