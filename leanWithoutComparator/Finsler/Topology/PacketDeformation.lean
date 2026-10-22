module

public import Finsler.Topology.CirclePacketFamily
public import Finsler.Geometry.LevelCrossing
public import Finsler.Topology.LensTrap

/-! deformed-energy bands and local lens models for the actual
global packet descent. -/

@[expose] public section

namespace Finsler.PacketDeformation

open Set Module Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.LocalLabelPacket Finsler.CirclePacketFamily Finsler.AmbientPenalty
open Finsler.LevelField Finsler.AmbientDescent Finsler.FlowLens Finsler.LensContinuation
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open scoped Topology ContDiff NNReal

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option maxHeartbeats 200000

variable {n M : ℕ} [NeZero M] {ι : Type*} [Fintype ι]
variable {F : ReversibleMetric n} {c η : ℝ} {p : ι → Packet n (2 * M)}
variable {Γ : ι → Set (ZMod (2 * M) → Ambient n)}
variable (han : ∀ i, Analytic F c η (Γ i) (p i))
variable (hdis : ∀ i j, i ≠ j → Disjoint (p i).U (p j).U)

include han hdis

omit hdis [Fintype ι] in
theorem beta_off_tube (i : ι) {y : ZMod (2 * M) → Ambient n} (hy : y ∉ (p i).T) :
    (p i).β y = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hy ((han i).2.2.2.2.2.2.2.1 h))

omit [Fintype ι] in
theorem tubes_disjoint (i j : ι) (hij : i ≠ j) : Disjoint (p i).T (p j).T :=
  (hdis i j hij).mono (han i).2.2.2.2.2.2.1 (han j).2.2.2.2.2.2.1

theorem sum_on_tube (i : ι) {y : ZMod (2 * M) → Ambient n} (hy : y ∈ (p i).T) :
    (∑ j, (p j).β y) = (p i).β y := by
  classical
  exact Finset.sum_eq_single i
    (fun j _ hji => beta_off_tube han j (fun hj =>
      Set.disjoint_left.mp (tubes_disjoint han hdis i j hji.symm) hy hj))
    (fun h => (h (Finset.mem_univ i)).elim)

theorem deformed_on_tube (i : ι) {y : ZMod (2 * M) → Ambient n} (hy : y ∈ (p i).T) :
    deformed M F p y = pen F (2 * M) 1 y + (p i).β y := by
  rw [deformed, sum_on_tube han hdis i hy]

omit hdis in
theorem deformed_off_tubes {y : ZMod (2 * M) → Ambient n} (hy : ∀ i, y ∉ (p i).T) :
    deformed M F p y = pen F (2 * M) 1 y := by
  unfold deformed
  rw [Finset.sum_eq_zero (fun i _ => beta_off_tube han i (hy i)), add_zero]

theorem deformed_on_critical (i : ι) {y : ZMod (2 * M) → Ambient n} (hy : y ∈ (p i).C) :
    deformed M F p y = c ^ 2 := by
  have hUi : y ∈ (p i).U := (han i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hy
  have hother : ∀ j, j ≠ i → (p j).β y = 0 := by
    intro j hji
    exact beta_off_tube han j (fun hj => Set.disjoint_left.mp (hdis i j hji.symm)
      hUi ((han j).2.2.2.2.2.2.1 hj))
  have hs : (∑ j, (p j).β y) = (p i).β y := by
    classical
    exact Finset.sum_eq_single i (fun j _ hj => hother j hj)
      (fun h => (h (Finset.mem_univ i)).elim)
  have hc := (han i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 y hy
  rw [deformed, hs, hc.1, hc.2, add_zero]

theorem deformed_bound (hη : 0 ≤ η) (y : ZMod (2 * M) → Ambient n) :
    |deformed M F p y - pen F (2 * M) 1 y| ≤ η := by
  by_cases hy : ∃ i, y ∈ (p i).T
  · obtain ⟨i, hi⟩ := hy
    rw [deformed_on_tube han hdis i hi, add_sub_cancel_left]
    exact (han i).2.2.2.2.2.2.2.2.2.1 y
  · rw [deformed_off_tubes han (fun i hi => hy ⟨i, hi⟩), sub_self, abs_zero]
    exact hη

omit hdis in
theorem deformed_continuous (hn : 1 ≤ n) :
    Continuous (fun Q : Om n (2 * M) => deformed M F p Q.1) := by
  apply (penW_continuous F hn 1).add
  exact continuous_finsetSum _ fun i _ =>
    ((show Differentiable ℝ (p i).β from fun y =>
      (han i).2.2.2.2.2.2.2.2.1 y).continuous.comp continuous_subtype_val)

theorem deformed_band_compact (hn : 1 ≤ n) (hη : 0 ≤ η) (a b : ℝ) :
    IsCompact {Q : Om n (2 * M) | a ≤ deformed M F p Q.1 ∧ deformed M F p Q.1 ≤ b} := by
  have hg := deformed_continuous han hn
  apply (band_isCompact F hn one_pos (a - η) (b + η)).of_isClosed_subset
    ((isClosed_le continuous_const hg).inter (isClosed_le hg continuous_const))
  intro Q hQ
  change a ≤ deformed M F p Q.1 ∧ deformed M F p Q.1 ≤ b at hQ
  have h := abs_le.mp (deformed_bound han hdis hη Q.1)
  change a - η ≤ pen F (2 * M) 1 Q.1 ∧ pen F (2 * M) 1 Q.1 ≤ b + η
  rcases hQ with ⟨hQa, hQb⟩
  constructor <;> linarith [h.1, h.2]

theorem collar_cases (hη : 0 ≤ η) {aw bw : ℝ}
    (hTval : ∀ i y, y ∈ (p i).T →
      aw + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < bw - η)
    (y : ZMod (2 * M) → Ambient n) :
    deformed M F p y = pen F (2 * M) 1 y ∨
      (aw < deformed M F p y ∧ deformed M F p y < bw ∧
        aw < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < bw) := by
  by_cases hy : ∃ i, y ∈ (p i).T
  · obtain ⟨i, hi⟩ := hy
    right
    rw [deformed_on_tube han hdis i hi]
    have ht := hTval i y hi
    have hb := abs_le.mp ((han i).2.2.2.2.2.2.2.2.2.1 y)
    exact ⟨by linarith [ht.1, hb.1], by linarith [ht.2, hb.2],
      by linarith [ht.1], by linarith [ht.2]⟩
  · exact Or.inl (deformed_off_tubes han (fun i hi => hy ⟨i, hi⟩))

theorem wide_sublevels (hη : 0 ≤ η) {aw bw : ℝ}
    (hTval : ∀ i y, y ∈ (p i).T →
      aw + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < bw - η) :
    sub (penW F (2 * M) 1) aw = sub (fun Q : Om n (2 * M) => deformed M F p Q.1) aw ∧
      sub (penW F (2 * M) 1) bw = sub (fun Q : Om n (2 * M) => deformed M F p Q.1) bw := by
  constructor
  · ext Q
    change pen F (2 * M) 1 Q.1 < aw ↔ deformed M F p Q.1 < aw
    rcases collar_cases han hdis hη hTval Q.1 with h | h
    · rw [h]
    · constructor <;> intro hQ <;> linarith [h.1, h.2.2.1]
  · ext Q
    change pen F (2 * M) 1 Q.1 < bw ↔ deformed M F p Q.1 < bw
    rcases collar_cases han hdis hη hTval Q.1 with h | h
    · rw [h]
    · exact ⟨fun _ => h.2.1, fun _ => h.2.2.2⟩

namespace Global

variable {a₀ b₀ : ℝ} (G : Global M F p a₀ b₀)

def descent : Descent (Om n (2 * M)) (fun Q => deformed M F p Q.1) :=
  descentOf G.lipschitz G.nonzero G.differentiable G.supported G.nonpos

theorem strict_deformed (hη : 0 ≤ η) {aw bw : ℝ}
    (ha : a₀ ≤ aw - η) (hb : bw + η ≤ b₀) (Q : Om n (2 * M))
    (hQa : aw ≤ deformed M F p Q.1) (hQb : deformed M F p Q.1 ≤ bw)
    (hQ : ∀ i, Q.1 ∉ (p i).C) :
    deformed M F p ((descent G).flow 1 Q).1 < deformed M F p Q.1 := by
  have h := abs_le.mp (deformed_bound han hdis hη Q.1)
  apply G.strict Q _ _ hQ
  · change a₀ ≤ pen F (2 * M) 1 Q.1
    linarith
  · change pen F (2 * M) 1 Q.1 ≤ b₀
    linarith

theorem strict_regular (hη : 0 ≤ η) {aw bw : ℝ}
    (ha : a₀ ≤ aw - η) (hb : bw + η ≤ b₀) (Q : Om n (2 * M))
    (hQa : aw ≤ deformed M F p Q.1) (hQb : deformed M F p Q.1 ≤ bw)
    (hQ : deformed M F p Q.1 ≠ c ^ 2) :
    deformed M F p ((descent G).flow 1 Q).1 < deformed M F p Q.1 :=
  strict_deformed han hdis G hη ha hb Q hQa hQb
    (fun i hi => hQ (deformed_on_critical han hdis i hi))

theorem strict_collar (hη : 0 ≤ η) {aw bw : ℝ} (ha : a₀ ≤ aw) (hb : bw ≤ b₀)
    (hTval : ∀ i y, y ∈ (p i).T →
      aw + η < pen F (2 * M) 1 y ∧ pen F (2 * M) 1 y < bw - η)
    (Q : Om n (2 * M)) (hQa : aw ≤ deformed M F p Q.1)
    (hQb : deformed M F p Q.1 ≤ bw) (hQ : ∀ i, Q.1 ∉ (p i).C) :
    deformed M F p ((descent G).flow 1 Q).1 < deformed M F p Q.1 := by
  have hband : a₀ ≤ penW F (2 * M) 1 Q ∧ penW F (2 * M) 1 Q ≤ b₀ := by
    change a₀ ≤ pen F (2 * M) 1 Q.1 ∧ pen F (2 * M) 1 Q.1 ≤ b₀
    rcases collar_cases han hdis hη hTval Q.1 with h | h
    · rw [h] at hQa hQb
      exact ⟨ha.trans hQa, hQb.trans hb⟩
    · exact ⟨ha.trans h.2.2.1.le, h.2.2.2.le.trans hb⟩
  exact G.strict Q hband.1 hband.2 hQ

theorem exists_trap (hn : 1 ≤ n) (hη : 0 ≤ η) {aw bw : ℝ}
    (ha : a₀ ≤ aw - η) (hb : bw + η ≤ b₀) :
    ∃ e : ℝ, 0 < e ∧ ∀ a b T : ℝ, aw ≤ a → b ≤ bw → b - a < e → 1 ≤ T →
      ∀ Q : Om n (2 * M), deformed M F p Q.1 < b →
        a ≤ deformed M F p ((descent G).flow T Q).1 → ∃ i, Q ∈ (p i).big := by
  have ho : IsOpen (⋃ i, (p i).big) := isOpen_iUnion fun i =>
    (han i).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hstrict : ∀ Q : Om n (2 * M), aw ≤ deformed M F p Q.1 →
      deformed M F p Q.1 ≤ bw → Q ∉ ⋃ i, (p i).big →
        deformed M F p ((descent G).flow 1 Q).1 < deformed M F p Q.1 := by
    intro Q hQa hQb hQ
    apply strict_deformed han hdis G hη ha hb Q hQa hQb
    intro i hCi
    exact hQ (mem_iUnion.mpr ⟨i, (han i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      ((han i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hCi)⟩)
  obtain ⟨e, he, ht⟩ := Finsler.LensTrap.exists_trap (descent G)
    (deformed_continuous han hn) ho (deformed_band_compact han hdis hn hη aw bw) hstrict
  exact ⟨e, he, fun a b T ha hb hab hT Q hQ hQ' =>
    mem_iUnion.mp (ht a b T ha hb hab hT Q hQ hQ')⟩

/-- The ordinary lens estimates of each packet hold for this actual global descent.
The remainder is the union of all other small label sets. -/
theorem lens_model (hn : 1 ≤ n) (hη : 0 ≤ η) (hm : ∀ i, Model F c (p i))
    {aw bw : ℝ} (ha : a₀ ≤ aw - η) (hb : bw + η ≤ b₀)
    (hac : aw < c ^ 2) (hcb : c ^ 2 < bw) (i : ι) :
    ∃ e : ℝ, 0 < e ∧ ∀ a b t : ℝ, 1 ≤ t → a < c ^ 2 → c ^ 2 < b → b - a < e →
      (∀ j : ℕ, finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
        (fun Q : Om n (2 * M) => deformed M F p Q.1) (descent G) (p i).big a b t)))
          (j + (p i).b)) = (p i).r a b t j) ∧
      (∀ j : ℕ, j < (p i).b → ∀ x : H (triv (pairOf (partY_sub_partU
        (fun Q : Om n (2 * M) => deformed M F p Q.1) (descent G) (p i).big a b t))) j, x = 0) := by
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
  apply hm i G.lipschitz G.nonzero G.differentiable G.supported G.nonpos
    (G.agrees i) (fun y hy => deformed_on_tube han hdis i hy) hac hcb
    (deformed_continuous han hn) (deformed_band_compact han hdis hn hη aw bw) hR hbigR
  intro Q hQa hQb hQ
  apply strict_deformed han hdis G hη ha hb Q hQa hQb
  intro j hCj
  have hsj := (han j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q hCj
  by_cases hji : j = i
  · subst j
    exact hQ (Or.inl hsj)
  · exact hQ (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hsj⟩))

end Global

end

end Finsler.PacketDeformation
