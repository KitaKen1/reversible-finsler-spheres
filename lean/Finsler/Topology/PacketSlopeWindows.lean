module

public import Finsler.Topology.ActualWindowCollar
public import Finsler.Topology.UniformPacketWindow
public import Finsler.Topology.EmptyFixedWindow
public import Finsler.Topology.HalfPartWindows

/-! Fixed windows of the same actual global descent lie around the half-slope line.
Even packets use their retained windows; odd packets have empty fixed label regions. -/

@[expose] public section

namespace Finsler.PacketSlopeWindows

open Set Module Finsler.Geometry Finsler.SphereGeometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.CircleRoot Finsler.OrientedCritical
open Finsler.GeodesicFrames Finsler.CrossingSlopes Finsler.LocalLabelPacket
open Finsler.CirclePacketFamily Finsler.ActualWindowCollar Finsler.PacketDeformation
open Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.AmbientK Finsler.FixedAmbientNormalize
open Finsler.FlowLens Finsler.LensContinuation Finsler.LensFamily Finsler.PacketSupport
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem fixed_set_eq {n : ℕ} (M : ℕ) [NeZero M] :
    {Q : Om n (2 * M) | rotA (2 * M) (M : ZMod (2 * M)) Q.1 = Q.1} = fixOm M := by
  ext Q
  change ((ambK M).σ Q).1 = Q.1 ↔ (ambK M).σ Q = Q
  exact Subtype.ext_iff.symm

theorem half_index_far {n : ℕ} (F : ReversibleMetric n)
    (s : Set (Sphere n)) (hs : s ∈ primeImages F) (k j : ℕ) [NeZero j]
    (hkj : k = 2 * j) {c : ℝ}
    (hkc : (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F s hs).loop) = c)
    (A q : ℕ) (hq : 2 * ((A + n : ℕ) : ℝ) < |2 * (q : ℝ) - slope F (s, true) * c|) :
    (A : ℝ) < |(q : ℝ) - (iterData (chosen F s hs)).I j| := by
  have hEpos := chosen_energy_pos F s hs
  have hmean := (iterData (chosen F s hs)).mean j (Nat.pos_of_neZero j)
  have hslope : slope F (s, true) * c = 2 * (j : ℝ) * (iterData (chosen F s hs)).Δ := by
    unfold Finsler.CrossingSlopes.slope
    rw [dite_eq_left hs, ← hkc, hkj]
    push_cast
    field_simp
    change (iterData (chosen F s hs)).Δ * (j : ℝ) = (j : ℝ) * (iterData (chosen F s hs)).Δ
    ring
  by_contra hnot
  have hnear := abs_le.mp (not_lt.mp hnot)
  have hm := abs_le.mp hmean
  have hbound : |2 * (q : ℝ) - slope F (s, true) * c| ≤ 2 * ((A : ℝ) + n) := by
    rw [hslope, abs_le]
    constructor <;> linarith [hnear.1, hnear.2, hm.1, hm.2]
  exact (not_lt_of_ge hbound) (by simpa only [Nat.cast_add] using hq)

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {hfin : (primeImages F).Finite}
variable {s : ι → Set (Sphere n)} {hs : ∀ i, s i ∈ primeImages F} {k : ι → ℕ}
variable {A : ℕ} {c η a₀ b₀ aw bw : ℝ}

theorem fixed_slope_window (B : Data F hfin s hs k A M c η a₀ b₀ aw bw)
    (hn : 1 ≤ n) (hη : 0 ≤ η) (hk : ∀ i, 0 < k i)
    (hkc : ∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F (chosen F (s i) (hs i)).loop) = c)
    (ha : a₀ ≤ aw - η) (hb : bw + η ≤ b₀) (hac : aw < c ^ 2) (hcb : c ^ 2 < bw) (i : ι) :
    ∃ e : ℝ, 0 < e ∧ ∀ a b T : ℝ, 1 ≤ T → a < c ^ 2 → c ^ 2 < b → b - a < e →
      ∀ q : ℕ, 2 * ((A + n : ℕ) : ℝ) < |2 * (q : ℝ) - slope F (s i, true) * c| →
        ∀ z : H (triv (pairOf (inter_subset_inter_left (fixOm M)
          (partY_sub_partU (fun Q : Om n (2 * M) => deformed M F (packetFamily M B.d) Q.1)
            (PacketDeformation.Global.descent B.global) (B.d i).big a b T)))) q, z = 0 := by
  classical
  have han := family_analytic M F hfin s hs k (fun i => M / k i) B.spec
  by_cases he : Even (k i)
  · obtain ⟨j, hj⟩ := he
    have hkj : k i = 2 * j := by omega
    have : NeZero j := ⟨by have := hk i; omega⟩
    obtain ⟨e, he, hw⟩ := Finsler.PacketFixedWindow.exists_fixed_window han B.disjoint
      B.global hn hη (i, true) (B.even_window i j hkj) ha hb hac hcb
    rw [fixed_set_eq M] at hw
    refine ⟨e, he, fun a b T hT hac' hcb' hab q hq => ?_⟩
    exact (hw a b T hT hac' hcb' hab).2 q (half_index_far F (s i) (hs i) (k i) j hkj (hkc i) A q hq)
  · have hfree := B.odd_free i (Nat.not_even_iff_odd.mp he)
    have hempty := Finsler.EmptyFixedWindow.big_fixed_empty (B.spec i).1.1 hfree
    have hdis : Disjoint (B.d i).big (fixOm M) := Set.disjoint_iff_inter_eq_empty.mpr hempty
    refine ⟨1, zero_lt_one, fun a b T _ _ _ _ q _ z => ?_⟩
    exact Finsler.HalfPartWindows.fixed_lens_eq_zero
      (PacketDeformation.Global.descent B.global) hdis a b T q z

end

end Finsler.PacketSlopeWindows
