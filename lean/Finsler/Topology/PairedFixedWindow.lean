module

public import Finsler.Topology.ReverseFixedWindow
public import Finsler.Topology.CirclePacketFamily
public import Finsler.Geometry.GeodesicReverseData

/-! Transport even fixed windows to both orientations of a family. -/

@[expose] public section

namespace Finsler.PairedFixedWindow

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.LocalLabelReverse Finsler.CirclePacketFamily
open Finsler.CircleRootWindow Finsler.CircleRoot Finsler.GeodesicFrames

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 800000

theorem family_window {n : ℕ} (M : ℕ) [NeZero M] {ι : Type*}
    (F : ReversibleMetric n) (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F)
    (k : ι → ℕ) (A : ℕ) (c : ℝ) (d : ι → Packet n (2 * M))
    (hwin : ∀ i j, ∀ [NeZero j], k i = 2 * j →
      Window F (M : ZMod (2 * M)) A
        ((iterData (Finsler.CriticalLevels.chosen F (s i) (hs i))).I j) c (d i))
    (p : ι × Bool) (j : ℕ) [NeZero j] (hkj : k p.1 = 2 * j) :
    Window F (M : ZMod (2 * M)) A
      ((iterData (labelGeod F (s p.1, p.2) (hs p.1))).I j) c (packetFamily M d p) := by
  rw [Finsler.GeodesicReverseData.label_index]
  rcases p with ⟨i, o⟩
  cases o
  · change Window F (M : ZMod (2 * M)) A
      ((iterData (Finsler.CriticalLevels.chosen F (s i) (hs i))).I j) c (reversePacket M (d i))
    apply Finsler.ReverseFixedWindow.reverse_window M F
    exact @hwin i j inferInstance hkj
  · change Window F (M : ZMod (2 * M)) A
      ((iterData (Finsler.CriticalLevels.chosen F (s i) (hs i))).I j) c (d i)
    exact @hwin i j inferInstance hkj

end

end Finsler.PairedFixedWindow

