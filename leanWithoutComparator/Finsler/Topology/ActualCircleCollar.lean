module

public import Finsler.Topology.ActualCircleDescent

/-! uniform actual-circle polygon models and packet tubes inside
a prescribed energy collar. -/

@[expose] public section

namespace Finsler.ActualCircleCollar

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics Finsler.Loops
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.OrientedCritical Finsler.CircleRoot
open Finsler.PolygonModel Finsler.PolygonDescent Finsler.PolygonSampling Finsler.PolygonCritical
open Finsler.PolygonLoop Finsler.IntervalSobolev Finsler.PhaseNullity Finsler.SamplePhase
open Finsler.SmoothSobolev Finsler.EnergySphereSmooth Finsler.AmbientPenalty
open Finsler.EnergyDiagonal Finsler.LoopCrossingOriented Finsler.CirclePacketGeometry
open Finsler.AmbientLoopPairs
open Finsler.RootIsolation
open Finsler.LocalLabelPacket Finsler.FiniteCirclePackets Finsler.CirclePacketFamily
open scoped Topology ContDiff NNReal

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 2400000

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- One fixed segment model and a finite maximum of sampling bounds work for both
orientations of every circle, uniformly in sufficiently large divisible vertex counts. -/
theorem exists_uniform_models (F : ReversibleMetric n) (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (s : ι → Set (Sphere n)) (hs : ∀ i, s i ∈ primeImages F) (k : ι → ℕ)
    (hkc : ∀ i, (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
      (chosen F (s i) (hs i)).loop) = c) (A : ℝ) :
    ∃ L Mmin : ℕ, 0 < L ∧ ∀ M : ℕ, Mmin ≤ M → L ∣ M → ∀ [NeZero M],
      ∃ P : PolygonModelData F A (2 * M),
        (∀ X Y : Sphere n, ‖(Y : Ambient n) - X‖ < P.δ →
          ContDiffAt ℝ 1 (ambientMinEnergy F) ((X : Ambient n), (Y : Ambient n))) ∧
        (∀ q : ZMod (2 * M) → Sphere n,
          PolygonDescent.energy F (2 * M) q ≤ A ^ 2 → ShortPolygon P.δ q) ∧
        ∀ p : ι × Bool, ∀ u ∈ circle F c (s p.1, p.2),
          ∃ hq : ShortPolygon P.δ (samplePoly (2 * M) u),
            broken P ⟨samplePoly (2 * M) u, hq⟩ = u := by
  classical
  have hkpos : ∀ i, 0 < k i := by
    intro i
    by_contra hi
    have h0 : k i = 0 := by omega
    have h := hkc i
    rw [h0, Nat.cast_zero, zero_mul] at h
    exact hc.ne h
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
  let L := ∏ i, k i
  have hL : 0 < L := Finset.prod_pos (fun i _ => hkpos i)
  have hkL : ∀ i, k i ∣ L := fun i => Finset.dvd_prod_of_mem k (Finset.mem_univ i)
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := S.δ) (a := A) S.pos
  obtain ⟨e, he, hedge⟩ := Finsler.PolygonEnergyGlobal.exists_edge_bound F hn
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (A ^ 2 / (e * S.δ ^ 2))
  refine ⟨L, L * (Nmax + 1) + N₁ + N₂, hL, fun M hM hLM _ => ?_⟩
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
  let P : PolygonModelData F A (2 * M) :=
    PolygonModelData.mk S fun u hu s' t hs' ht hst =>
      hN₁ (2 * M) (by omega) (Nat.mul_pos two_pos (Nat.pos_of_neZero M)) u hu s' t hs' ht hst
  have hKR : A ^ 2 / (e * S.δ ^ 2) < (2 * M : ℕ) :=
    hN₂.trans_le (Nat.cast_le.mpr (by omega))
  refine ⟨P, fun X Y h => hC1 X Y (h.trans_le hSδ),
    fun q hq => short_of_energy_le he S.pos hedge hKR q hq, ?_⟩
  intro p
  letI := hNi p.1
  apply circle_reconstruction P hc (s p.1) (hs p.1) p.2 (k p.1)
    (M / k p.1) (h2N p.1) (hK p.1) (hkc p.1)
  intro a
  exact hK₀ p a (2 * (M / k p.1)) (by have := hNmax p; have := hNM p.1; omega)

theorem sample_circle_pen {F : ReversibleMetric n} {A c : ℝ} {K : ℕ} [NeZero K]
    (P : PolygonModelData F A K) (ℓ : Set (Sphere n) × Bool) {u : SphereLoop n}
    (hu : u ∈ circle F c ℓ)
    (hq : ShortPolygon P.δ (samplePoly K u))
    (hrec : broken P ⟨samplePoly K u, hq⟩ = u) :
    pen F K 1 (amb (samplePoly K u)) = c ^ 2 := by
  have he := energy_broken P ⟨samplePoly K u, hq⟩
  rw [hrec, energy_of_mem_circle F ℓ _ hu] at he
  change c ^ 2 = PolygonDescent.energy F K (samplePoly K u) at he
  change penW F K 1 (incl (samplePoly K u)) = c ^ 2
  rw [penW_incl]
  exact he.symm

/-- The actual packets can be chosen with their tubes strictly inside prescribed energy cuts.
This supplies the margin needed to keep the original wide sublevels after deformation. -/
theorem exists_actual_collar (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {c a₀ b₀ : ℝ} (ha₀ : 0 < a₀)
    (hac : a₀ < c) (hcb : c < b₀)
    (hone : ∀ c' ∈ crit F, a₀ ≤ c' → c' ≤ b₀ → c' = c) :
    ∃ k : Active F hfin c → ℕ,
      (∀ i, 0 < k i ∧ (k i : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
        (chosen F i.1 (active_mem_prime F hfin c i)).loop) = c) ∧
      ∃ L Mmin : ℕ, 0 < L ∧ ∀ M : ℕ, Mmin ≤ M → L ∣ M → ∀ [NeZero M]
        {aw bw η : ℝ}, 0 < η → aw + η < c ^ 2 → c ^ 2 < bw - η →
          ∃ d : Active F hfin c → Packet n (2 * M),
            (∀ i, Spec F hfin i.1 (active_mem_prime F hfin c i)
              (k i) (M / k i) c η (d i)) ∧
            (∀ p : Active F hfin c × Bool, ∀ y ∈ (packetFamily M d p).T,
              aw + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < bw - η) ∧
            Nonempty (Global M F (packetFamily M d) (a₀ ^ 2) (b₀ ^ 2)) := by
  classical
  have hc : 0 < c := ha₀.trans hac
  let ι := Active F hfin c
  let s : ι → Set (Sphere n) := Subtype.val
  have hs : ∀ i, s i ∈ primeImages F := active_mem_prime F hfin c
  choose k hkpos hkc using exists_multiplicity F hfin c
  have hkc' := fun i => hkc i (hs i)
  obtain ⟨L₁, M₁, hL₁, hkL, hglobal⟩ := exists_finite_global F hn hfin hc s hs k hkc'
  obtain ⟨L₂, M₂, hL₂, hmodels⟩ := exists_uniform_models F hn hc s hs k hkc' b₀
  refine ⟨k, fun i => ⟨hkpos i, hkc' i⟩,
    L₁ * L₂, M₁ + M₂, Nat.mul_pos hL₁ hL₂,
    fun M hM hLM _ aw bw η hη haw hbw => ?_⟩
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
  obtain ⟨d, hd, hG⟩ := hglobal M (by omega) hL₁M hC1 hshort V hVo hVΓ
    (fun i j hij => (hdis i j hij).mono (hVU i) (hVU j))
    (fun i j => (hcross i j).mono (hVU i) (preimage_mono (hVU j)))
    hcover hη
  refine ⟨d, fun i => (hd i).2, ?_, hG⟩
  rintro ⟨i, o⟩ y hy
  have hTU := (hd i).2.1.1.2.2.2.2.2.2.1
  cases o
  · have hv := hVband i _ ((hd i).1 (hTU hy))
    have he := Finsler.RevLabel.pen_revA F 1 y
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  · exact hVband i _ ((hd i).1 (hTU hy))

end

end Finsler.ActualCircleCollar
