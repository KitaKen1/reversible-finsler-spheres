module

public import Finsler.Topology.CircleRootWindow
public import Finsler.Topology.PacketDeformation

/-! Instantiate a retained fixed Window with the same actual
global packet descent, discharging tube, compact-band and strictness hypotheses. -/

@[expose] public section

namespace Finsler.PacketFixedWindow

open Set Module Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.CirclePacketFamily Finsler.PacketDeformation
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.AmbientSymmetry
open Finsler.FlowLens Finsler.LensContinuation Finsler.BorelCochain Finsler.BorelPair
open Finsler.BorelLoop Finsler.PairTriple Finsler.CircleRootWindow

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {c η a₀ b₀ : ℝ} {p : ι → Packet n (2 * M)}
variable {Γ : ι → Set (ZMod (2 * M) → Ambient n)}

theorem exists_fixed_window (han : ∀ i, Analytic F c η (Γ i) (p i))
    (hdis : ∀ i j, i ≠ j → Disjoint (p i).U (p j).U)
    (G : CirclePacketFamily.Global M F p a₀ b₀) (hn : 1 ≤ n) (hη : 0 ≤ η)
    (i : ι) {A I : ℕ} (hw : Window F (M : ZMod (2 * M)) A I c (p i))
    {aw bw : ℝ} (ha : a₀ ≤ aw - η) (hb : bw + η ≤ b₀)
    (hac : aw < c ^ 2) (hcb : c ^ 2 < bw) :
    ∃ e : ℝ, 0 < e ∧ ∀ a b T : ℝ, 1 ≤ T → a < c ^ 2 → c ^ 2 < b → b - a < e →
      (∀ q, Module.Finite (ZMod 2) (H (triv (pairOf
        (inter_subset_inter_left {Q : Om n (2 * M) | rotA (2 * M) (M : ZMod (2 * M)) Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n (2 * M) => deformed M F p Q.1)
            (PacketDeformation.Global.descent G) (p i).big a b T)))) q)) ∧
      ∀ q : ℕ, (A : ℝ) < |(q : ℝ) - I| → ∀ z : H (triv (pairOf
        (inter_subset_inter_left {Q : Om n (2 * M) | rotA (2 * M) (M : ZMod (2 * M)) Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n (2 * M) => deformed M F p Q.1)
            (PacketDeformation.Global.descent G) (p i).big a b T)))) q, z = 0 := by
  classical
  let R : Set (Om n (2 * M)) := ⋃ j : {j : ι // j ≠ i}, (p j.1).small
  have hR : IsOpen R := isOpen_iUnion fun j =>
    (han j.1).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hbigR : Disjoint (p i).big R := by
    apply Set.disjoint_left.mpr
    intro Q hQi hQR
    obtain ⟨j, hj⟩ := mem_iUnion.mp hQR
    have hTi := (han i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hQi
    have hTj := (han j.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q
      ((han j.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hj)
    exact Set.disjoint_left.mp (tubes_disjoint han hdis i j.1 j.2.symm) hTi hTj
  apply hw G.lipschitz G.nonzero G.differentiable G.supported G.nonpos
    (G.agrees i) (fun y hy => deformed_on_tube han hdis i hy) hac hcb hR hbigR
    (deformed_continuous han hn) (deformed_band_compact han hdis hn hη aw bw)
  intro Q hQa hQb hQ
  apply PacketDeformation.Global.strict_deformed han hdis G hη ha hb Q hQa hQb
  intro j hCj
  have hsj := (han j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hCj
  by_cases hji : j = i
  · subst j
    exact hQ (Or.inl hsj)
  · exact hQ (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hsj⟩))

end

end Finsler.PacketFixedWindow

