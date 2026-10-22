module

public import Finsler.Topology.AmbientLensPieces
public import Finsler.Topology.PacketCutTimes

/-! the conditional pieces construction for the actual global
packet descent. Its cut-flow times are supplied by compact regular strips. Local and fixed
windows remain hypotheses. -/

@[expose] public section

namespace Finsler.PacketPieces

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.LocalLabelPacket
open Finsler.CirclePacketFamily Finsler.PacketDeformation Finsler.PacketCutTimes
open Finsler.AmbientPenalty Finsler.AmbientK Finsler.FixedAmbientNormalize
open Finsler.FlowLens Finsler.InvPairs Finsler.PolySplit Finsler.BorelIterate
open Finsler.BorelComparison Finsler.SampleK Finsler.FixedSampleK Finsler.OrbitAssembly
open Finsler.BorelCochain

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {c η a₀ b₀ : ℝ} {p : ι → Packet n (2 * M)}
variable {Γ : ι → Set (ZMod (2 * M) → Ambient n)}

/-- Pieces for the actual packet energy and its actual global descent, conditional only on
the displayed sampling, trapping and window data. The lower/upper cut times are constructed. -/
theorem nonempty_pieces (han : ∀ i, Analytic F c η (Γ i) (p i))
    (hdis : ∀ i j, i ≠ j → Disjoint (p i).U (p j).U)
    (G : CirclePacketFamily.Global M F p a₀ b₀) (hn : 1 ≤ n) (hη : 0 ≤ η)
    (hgρ : ∀ Q : Om n (2 * M), deformed M F p ((ambK M).ρ Q).1 = deformed M F p Q.1)
    (hgσ : ∀ Q : Om n (2 * M), deformed M F p ((ambK M).σ Q).1 = deformed M F p Q.1)
    {l u a' a b T : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hla : l ^ 2 ≤ a) (hac : a < c ^ 2) (hcb : c ^ 2 < b) (hbu : b ≤ u ^ 2)
    (ha₀ : a₀ ≤ l ^ 2 - η) (hb₀ : u ^ 2 + η ≤ b₀)
    (hTval : ∀ i y, y ∈ (p i).T →
      l ^ 2 + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < u ^ 2 - η)
    (ha' : a' < a) (hT : 0 ≤ T) {J : Type}
    (𝒲 : J → Set (Om n (2 * M))) (h𝒲K : ∀ j, Inv (ambK M) (𝒲 j))
    (h𝒲 : ∀ j, IsOpen (𝒲 j)) (h𝒲dis : Pairwise fun i j => Disjoint (𝒲 i) (𝒲 j))
    (htrap : ∀ Q : Om n (2 * M), deformed M F p Q.1 < b →
      a' < deformed M F p ((PacketDeformation.Global.descent G).flow T Q).1 → ∃ j, Q ∈ 𝒲 j)
    (hsK : ∀ q, Function.Bijective (HRmap (borelHom (sampleHom (F := F) (M := M) hl hlu)) q))
    (hsF : ∀ q, Function.Bijective (HRmap (borelHom (sampleFixHom (F := F) (M := M) hl hlu)) q))
    (hsR : ∀ q, Function.Bijective (HRmap (sampleFixHom (F := F) (M := M) hl hlu).φ q))
    {c₀ A : ℝ} {S : Finset ℝ} (slope : J → ℝ) (hslope : ∀ j, slope j ∈ S)
    (hwin : ∀ j (i : ℕ), A < |(i : ℝ) - slope j * c₀| →
      ∀ z : HR (partComplex (ambK M) hgρ hgσ (PacketDeformation.Global.descent G) G.rho G.sigma
        a' a b T 𝒲 h𝒲K j) i, z = 0)
    (hwinh : ∀ j (i : ℕ), 2 * A < |2 * (i : ℝ) - slope j * c₀| →
      ∀ z : HR (fixPartComplex (ambK M) (fixOm_invariant M) hgρ hgσ
        (PacketDeformation.Global.descent G) G.rho G.sigma a' a b T 𝒲 h𝒲K j) i, z = 0) :
    Nonempty (Pieces F hlu c₀ A S) := by
  classical
  have hab := hac.le.trans hcb.le
  obtain ⟨τl, τu, hτl, hτu, hpushl, hpushu⟩ := exists_cut_times han hdis G hn hη
    ha₀ hb₀ hla hac hcb hbu
  obtain ⟨hsa, hsb⟩ := wide_sublevels han hdis hη hTval
  exact ⟨AmbientLensPieces.pieces M F hgρ hgσ (PacketDeformation.Global.descent G) G.rho G.sigma
    hl hlu hla hab hbu hT hsa hsb hτu hpushu (by norm_num) hτl hpushl
    (deformed_continuous han hn) ha' 𝒲 h𝒲K h𝒲 h𝒲dis htrap hsK hsF hsR slope hslope hwin hwinh⟩

end

end Finsler.PacketPieces
