module

public import Finsler.Topology.ActualCircleCollar
public import Finsler.Topology.MixedPacketWindows
public import Finsler.Topology.PacketFixedWindow

/-! One root cutoff works at every isolated level. The same selected packets retain
their ordinary models, odd fixed-free tubes, even fixed windows, collar and actual global flow. -/

@[expose] public section

namespace Finsler.ActualWindowCollar

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.Loops
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical Finsler.CircleRoot
open Finsler.PolygonModel Finsler.PolygonDescent Finsler.PolygonSampling Finsler.PolygonCritical
open Finsler.PolygonLoop Finsler.IntervalSobolev Finsler.PhaseNullity Finsler.SamplePhase
open Finsler.SmoothSobolev Finsler.EnergySphereSmooth Finsler.AmbientPenalty
open Finsler.EnergyDiagonal Finsler.LoopCrossingOriented Finsler.CirclePacketGeometry
open Finsler.AmbientLoopPairs Finsler.RootIsolation Finsler.ActualCircleCollar
open Finsler.LocalLabelPacket Finsler.FiniteCirclePackets Finsler.CirclePacketFamily
open Finsler.CircleRootWindow Finsler.GeodesicFrames
open scoped Topology ContDiff NNReal

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 2400000

variable {n : ℕ}

structure Data {ι : Type*} [Fintype ι] (F : ReversibleMetric n)
    (hfin : (primeImages F).Finite) (s : ι → Set (Sphere n))
    (hs : ∀ i, s i ∈ primeImages F) (k : ι → ℕ) (A M : ℕ) [NeZero M]
    (c η a₀ b₀ aw bw : ℝ) where
  d : ι → Packet n (2 * M)
  spec : ∀ i, Spec F hfin (s i) (hs i) (k i) (M / k i) c η (d i)
  kn : ∀ i, k i * (M / k i) = M
  retained : ∀ i, ∃ hN : NeZero (M / k i),
    @Finsler.MixedRootPacket.Retained n F hfin (s i, true)
      ((mem_labels F hfin (s i, true)).mpr (hs i)) (k i) (M / k i) (2 * M) hN c (d i)
  disjoint : ∀ p q : ι × Bool, p ≠ q →
    Disjoint (packetFamily M d p).U (packetFamily M d q).U
  collar : ∀ p : ι × Bool, ∀ y ∈ (packetFamily M d p).T,
    aw + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < bw - η
  odd_free : ∀ i, Odd (k i) → ∀ y ∈ (d i).U,
    Finsler.AmbientSymmetry.rotA (2 * M) (M : ZMod (2 * M)) y ≠ y
  even_window : ∀ i j, ∀ [NeZero j], k i = 2 * j →
    Window F (M : ZMod (2 * M)) A ((iterData (chosen F (s i) (hs i))).I j) c (d i)
  global : Global M F (packetFamily M d) a₀ b₀

def Available (F : ReversibleMetric n) (hfin : (primeImages F).Finite) (A : ℕ) : Prop :=
  ∀ {c a₀ b₀ : ℝ}, 0 < a₀ → a₀ < c → c < b₀ →
    (∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) →
    ∃ k : Active F hfin c → ℕ,
      (∀ i, 0 < k i ∧ (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
        (chosen F i.1 (active_mem_prime F hfin c i)).loop) = c) ∧
      ∃ L Mmin : ℕ, 0 < L ∧ (∀ i, k i ∣ L) ∧
        ∀ M : ℕ, Mmin ≤ M → L ∣ M → ∀ [NeZero M] {aw bw η : ℝ},
          0 < η → aw + η < c ^ 2 → c ^ 2 < bw - η →
          Nonempty (Data F hfin (fun i : Active F hfin c => i.1)
            (active_mem_prime F hfin c) k A M c η (a₀ ^ 2) (b₀ ^ 2) aw bw)

-- The construction below reuses the actual uniform models and separated neighbourhoods.
theorem available_of_catalogue (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {A : ℕ}
    (hcat : Finsler.PacketWindowCatalogue.Catalogue F hfin A) : Available F hfin A := by
  intro c a₀ b₀ ha₀ hac hcb hone
  classical
  have hc : 0 < c := ha₀.trans hac
  let ι := Active F hfin c
  let s : ι → Set (Sphere n) := Subtype.val
  have hs : ∀ i, s i ∈ primeImages F := active_mem_prime F hfin c
  choose k hkpos hkc using exists_multiplicity F hfin c
  have hkc' := fun i => hkc i (hs i)
  obtain ⟨L₁, M₁, hL₁, hkL, hselect⟩ :=
    Finsler.MixedPacketWindows.exists_packets F hn hfin hcat hc s hs k hkc'
  obtain ⟨L₂, M₂, hL₂, hmodels⟩ := exists_uniform_models F hn hc s hs k hkc' b₀
  refine ⟨k, fun i => ⟨hkpos i, hkc' i⟩,
    L₁ * L₂, M₁ + M₂, Nat.mul_pos hL₁ hL₂,
    (fun i => (hkL i).trans (dvd_mul_right L₁ L₂)), fun M hM hLM _ aw bw η hη haw hbw => ?_⟩
  have hL₁M : L₁ ∣ M := (dvd_mul_right L₁ L₂).trans hLM
  have hL₂M : L₂ ∣ M := (dvd_mul_left L₂ L₁).trans hLM
  obtain ⟨P, hC1, hshort, hrec⟩ := hmodels M (by omega) hL₂M
  obtain ⟨U, hU, hdis, hcross⟩ :=
    exists_circle_neighbourhoods P c s Subtype.val_injective hrec
  let V : ι → Set (ZMod (2 * M) → Ambient n) := fun i =>
    Subtype.val '' (Subtype.val ⁻¹' U i ∩
      {Q : Om n (2 * M) | aw + η < penW F (2 * M) 1 Q ∧ penW F (2 * M) 1 Q < bw - η})
  have hVo : ∀ i, IsOpen (V i) := fun i =>
    (isOpen_nonzero (N := 2 * M)).isOpenMap_subtype_val _
      (((hU i).1.preimage continuous_subtype_val).inter
        ((isOpen_lt continuous_const (penW_continuous F hn 1)).inter
          (isOpen_lt (penW_continuous F hn 1) continuous_const)))
  have hVU : ∀ i, V i ⊆ U i := by
    rintro i _ ⟨Q, ⟨hQU, -⟩, rfl⟩
    exact hQU
  have hVband : ∀ i y, y ∈ V i →
      aw + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < bw - η := by
    rintro i _ ⟨Q, ⟨-, hQ⟩, rfl⟩
    exact hQ
  have hVΓ : ∀ i, ∀ u ∈ posCircle F c (s i), amb (samplePoly (2 * M) u) ∈ V i := by
    intro i u hu
    obtain ⟨hq, he⟩ := hrec (i, true) u hu
    have hp := sample_circle_pen P (s i, true) hu hq he
    refine ⟨incl (samplePoly (2 * M) u), ⟨(hU i).2 u hu, ?_⟩, rfl⟩
    change aw + η < pen F (2 * M) 1 (amb (samplePoly (2 * M) u)) ∧
      pen F (2 * M) 1 (amb (samplePoly (2 * M) u)) < bw - η
    rw [hp]
    exact ⟨haw, hbw⟩
  have hcover : ∀ q : ZMod (2 * M) → Sphere n,
      a₀ ^ 2 ≤ PolygonDescent.energy F (2 * M) q →
      PolygonDescent.energy F (2 * M) q ≤ b₀ ^ 2 → PolyCritical F (2 * M) q →
      ∃ p : ι × Bool, (incl q : Om n (2 * M)).1 ∈
        sampleSet (2 * M) (circle F c (s p.1, p.2)) := by
    intro q ha hb hq
    exact critical_band_cover P hfin ha₀ (hac.trans hcb).le hone hshort hq ha hb
  obtain ⟨d, hd⟩ := hselect M (by omega) hL₁M V hVo hVΓ hη
  have hspec : ∀ i, Spec F hfin (s i) (hs i) (k i) (M / k i) c η (d i) :=
    fun i => (hd i).2.1
  have hkn : ∀ i, k i * (M / k i) = M :=
    fun i => Nat.mul_div_cancel' ((hkL i).trans hL₁M)
  have hsub : ∀ i, (d i).U ⊆ V i := fun i => (hd i).1
  have hVdis : ∀ i j, i ≠ j → Disjoint (V i) (V j) :=
    fun i j hij => (hdis i j hij).mono (hVU i) (hVU j)
  have hVrev : ∀ i j, Disjoint (V i) (Finsler.PolygonDescentK.revA (2 * M) ⁻¹' V j) :=
    fun i j => (hcross i j).mono (hVU i) (preimage_mono (hVU j))
  obtain ⟨G⟩ := Finsler.CirclePacketFamily.exists_global M F hn hfin s hs k
    (fun i => M / k i) hspec hkn hsub hVdis hVrev hC1 hshort hcover
  refine ⟨⟨d, hspec, hkn, (fun i => (hd i).2.2.1),
    family_disjoint M hsub hVdis hVrev, ?_,
    (fun i => (hd i).2.2.2.1), (fun i => (hd i).2.2.2.2), G⟩⟩
  rintro ⟨i, o⟩ y hy
  have hTU := (hspec i).1.1.2.2.2.2.2.2.1
  cases o
  · have hv := hVband i _ (hsub i (hTU hy))
    have he := Finsler.RevLabel.pen_revA F 1 y
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  · exact hVband i _ (hsub i (hTU hy))


theorem exists_uniform_collar (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, Finsler.RootCatalogue.Bounds F hfin A ∧ Available F hfin A := by
  obtain ⟨A, hA, hcat⟩ := Finsler.PacketWindowCatalogue.exists_catalogue F hn hfin
  exact ⟨A, hA, available_of_catalogue F hn hfin hcat⟩

end

end Finsler.ActualWindowCollar
