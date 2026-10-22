module

public import Finsler.Geometry.LevelCrossing
public import Finsler.Topology.ECupLens

/-! The crossing of a level with one label, for the cup with a global class (Claude prototype).

The setting of `LevelCrossing.level_crossing` with a single label. If for every descent agreeing
with the label field on the piece the cup with a global class e of the ambient polygons annihilates
no nonzero class of the lens pair of the label set in degree l (for tight cuts around c₀), then it
annihilates no nonzero class of the crossing pair of the penalized energy at the wide cuts in
degree l. The proof is the proof of `level_crossing`: the cuts move through regular strips
(`ECupLens.move_iff`) and the tight crossing is the lens pair of the trapping label set
(`ECupLens.crossing_iff`); all these isomorphisms are induced by inclusions of pairs. -/

@[expose] public section

namespace Finsler.LevelCrossingCup

open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.Geometry
open Finsler.SphereRetraction Finsler.EnergySphereSmooth Finsler.PolygonCritical
open Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal
open Finsler.PolygonDescent Finsler.PseudoGradient Finsler.SphereFlow Finsler.FlowLens
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.LevelField Finsler.LevelBuild
open Finsler.LevelDescent Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.LensContinuation Finsler.LensFamily Finsler.CutMove
open Finsler.LevelCrossing Finsler.ECup Finsler.ECupLens
open Set Filter Module
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {K : ℕ} [NeZero K]

set_option maxHeartbeats 800000 in
/-- **The crossing of a level with one label, for the cup with a global class.** -/
theorem level_crossing_cup (F : ReversibleMetric n) (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod K → Sphere n, PolygonDescent.energy F K q ≤ b₀ → ShortPolygon δ q)
    {U : Set (ZMod K → Ambient n)} {W : (ZMod K → Ambient n) → ZMod K → Ambient n}
    {β : (ZMod K → Ambient n) → ℝ} {C T : Set (ZMod K → Ambient n)} {𝒲 𝒲' : Set (Om n K)}
    (hU : IsOpen U) (hUO : U ⊆ regSet F K 1) (hW : ContDiffOn ℝ ∞ W U)
    (hWle : ∀ y ∈ U, fderiv ℝ (pen F K 1) y (W y) ≤ 0)
    (hWlt : ∀ y ∈ U, y ∉ C → fderiv ℝ (pen F K 1) y (W y) < 0)
    (hT : IsCompact T) (hTU : T ⊆ U)
    (hβT : tsupport β ⊆ T) (hβd : ∀ y, DifferentiableAt ℝ β y)
    (hβle : ∀ y ∈ tsupport β, fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) ≤ 0)
    (hβlt : ∀ y ∈ tsupport β, y ∉ C → fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) < 0)
    (h𝒲 : IsOpen 𝒲) (h𝒲𝒲' : 𝒲' ⊆ 𝒲) (h𝒲T : ∀ Q ∈ 𝒲, Q.1 ∈ T)
    (hC𝒲 : ∀ Q : Om n K, Q.1 ∈ C → Q ∈ 𝒲') (hCU : C ⊆ U) {c₀ : ℝ}
    (hCval : ∀ y ∈ C, pen F K 1 y = c₀ ∧ β y = 0)
    {η : ℝ} (hβη : ∀ y, |β y| ≤ η)
    {aw bw : ℝ} (ha₀ : a₀ ≤ aw) (hb₀ : bw ≤ b₀) (hac₀ : aw < c₀) (hc₀b : c₀ < bw)
    (hTval : ∀ y ∈ T, aw + η < pen F K 1 y ∧ pen F K 1 y < bw - η)
    (hcrit : ∀ q : ZMod K → Sphere n, a₀ ≤ PolygonDescent.energy F K q →
      PolygonDescent.energy F K q ≤ b₀ → PolyCritical F K q → (incl q : Om n K).1 ∈ T)
    {p : ℕ} (e : cohomologyZMod2 (Om n K) p) (l : ℕ)
    (hP2 : ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
        (hL : LipschitzWith KL V) (hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
        {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
        (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
        (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0),
        (∀ y ∈ T, V y = W y) → (∀ y ∈ T, g y = pen F K 1 y + β y) →
        ∀ {a₀a b₀a : ℝ}, a₀a < c₀ → c₀ < b₀a → Continuous (fun Q : Om n K => g Q.1) →
        IsCompact {Q : Om n K | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a} →
        ∀ {R : Set (Om n K)}, IsOpen R → Disjoint 𝒲 R →
        (∀ Q : Om n K, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ 𝒲' ∪ R →
          g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
        ∃ d : ℝ, 0 < d ∧ ∀ a c t : ℝ, 1 ≤ t → a < c₀ → c₀ < c → c - a < d →
          CupInjW e (partY_sub_partU (fun Q : Om n K => g Q.1)
            (descentOf hL hV0 hg hsupp hle) 𝒲 a c t) l)
    (habw : aw ≤ bw) :
    CupInjW e (sub_mono (penW F K 1) habw) l := by
  classical
  -- the descent of the level
  obtain ⟨V, KL, hL, hV0, hg, hsupp, hle, hVT, hlt⟩ := exists_level_descent F hn hδ hshort
    (s := (Finset.univ : Finset Unit)) (U := fun _ => U) (W := fun _ => W) (β := fun _ => β)
    (C := fun _ => C) (T := fun _ => T) (fun _ _ => hU) (fun _ _ => hUO)
    (fun i _ j _ hij => absurd (Subsingleton.elim i j) hij) (fun _ _ => hW) (fun _ _ => hWle)
    (fun _ _ => hWlt) (fun _ _ => hT) (fun _ _ => hTU) (fun _ _ => hβT) (fun _ _ => hβd)
    (fun _ _ => hβle) (fun _ _ => hβlt)
    (fun q h1 h2 h3 => mem_iUnion₂.mpr ⟨(), Finset.mem_univ _, hcrit q h1 h2 h3⟩)
  have hsum : ∀ y, ∑ _j ∈ (Finset.univ : Finset Unit), β y = β y := fun y => by simp
  have hη : 0 ≤ η := (abs_nonneg _).trans (hβη 0)
  have hβzero : ∀ y, y ∉ T → β y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hβT h))
  have hcase : ∀ y : ZMod K → Ambient n, (β y = 0) ∨
      (aw < pen F K 1 y + β y ∧ pen F K 1 y + β y < bw ∧
        aw < pen F K 1 y ∧ pen F K 1 y < bw) := by
    intro y
    by_cases h : y ∈ T
    · right
      have h1 := hTval y h
      have h2 := abs_le.mp (hβη y)
      exact ⟨by linarith only [h1.1, h2.1], by linarith only [h1.2, h2.2],
        by linarith only [h1.1, hη], by linarith only [h1.2, hη]⟩
    · left
      exact hβzero y h
  -- the deformed energy has the sublevels of the penalized energy at the wide cuts
  have hsa : sub (penW F K 1) aw =
      sub (fun Q : Om n K => pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1) aw := by
    ext Q
    change pen F K 1 Q.1 < aw ↔ pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 < aw
    rw [hsum]
    rcases hcase Q.1 with h | h
    · rw [h, add_zero]
    · constructor <;> intro h' <;> linarith only [h', h.1, h.2.2.1]
  have hsb : sub (penW F K 1) bw =
      sub (fun Q : Om n K => pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1) bw := by
    ext Q
    change pen F K 1 Q.1 < bw ↔ pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 < bw
    rw [hsum]
    rcases hcase Q.1 with h | h
    · rw [h, add_zero]
    · exact ⟨fun _ => h.2.1, fun _ => h.2.2.2⟩
  -- the band of the deformed energy lies in the band of the penalized energy
  have hband : ∀ Q : Om n K, aw ≤ pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 →
      pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 ≤ bw →
        a₀ ≤ penW F K 1 Q ∧ penW F K 1 Q ≤ b₀ := by
    intro Q h1 h2
    rw [hsum] at h1 h2
    change a₀ ≤ pen F K 1 Q.1 ∧ pen F K 1 Q.1 ≤ b₀
    rcases hcase Q.1 with h | h
    · rw [h, add_zero] at h1 h2
      exact ⟨ha₀.trans h1, h2.trans hb₀⟩
    · exact ⟨by linarith only [ha₀, h.2.2.1], by linarith only [hb₀, h.2.2.2]⟩
  have hnotC : ∀ Q : Om n K, pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 ≠ c₀ →
      Q.1 ∉ C := fun Q hQ hC => by
    apply hQ
    rw [hsum, (hCval Q.1 hC).1, (hCval Q.1 hC).2, add_zero]
  have hstrict : ∀ Q : Om n K, aw ≤ pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 →
      pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 ≤ bw → Q.1 ∉ C →
      pen F K 1 ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 +
          ∑ _j ∈ (Finset.univ : Finset Unit), β ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 <
        pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 :=
    fun Q h1 h2 h3 => hlt Q (hband Q h1 h2).1 (hband Q h1 h2).2 fun _ _ => h3
  -- continuity and compact bands
  have hgc : Continuous fun Q : Om n K =>
      pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 :=
    (penW_continuous F hn 1).add (continuous_finsetSum _ fun _ _ =>
      ((show Differentiable ℝ β from fun y => hβd y).continuous.comp continuous_subtype_val))
  have hKband : ∀ x y : ℝ, aw ≤ x → y ≤ bw →
      IsCompact {Q : Om n K | x ≤ pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 ∧
        pen F K 1 Q.1 + ∑ _j ∈ (Finset.univ : Finset Unit), β Q.1 ≤ y} :=
    fun x y hx hy => (band_isCompact F hn one_pos a₀ b₀).of_isClosed_subset
      ((isClosed_le continuous_const hgc).inter (isClosed_le hgc continuous_const))
      (fun Q hQ => hband Q (hx.trans hQ.1) (hQ.2.trans hy))
  -- the trap of the label set
  obtain ⟨dF, hdF, htrap⟩ := Finsler.LensTrap.exists_trap (descentOf hL hV0 hg hsupp hle) hgc h𝒲
    (hKband aw bw le_rfl le_rfl)
    (fun Q h1 h2 hQ => hstrict Q h1 h2 fun hC => hQ (h𝒲𝒲' (hC𝒲 Q hC)))
  -- the label
  obtain ⟨dd, hdd, hP⟩ := hP2 hL hV0 hg hsupp hle (hVT () (Finset.mem_univ _))
    (fun y _ => by rw [hsum]) hac₀ hc₀b hgc (hKband aw bw le_rfl le_rfl) isOpen_empty
    (disjoint_empty _) (fun Q h1 h2 hQ => hstrict Q h1 h2 fun hC => hQ (Or.inl (hC𝒲 Q hC)))
  -- tight cuts
  obtain ⟨d, hd, hd1, hd2, hd3, hd4⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ dF / 2 ∧ d ≤ c₀ - aw ∧
      d ≤ bw - c₀ ∧ d ≤ dd :=
    ⟨min (dF / 2) (min (c₀ - aw) (min (bw - c₀) dd)),
      lt_min (half_pos hdF) (lt_min (by linarith only [hac₀]) (lt_min (by linarith only [hc₀b]) hdd)),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have haw : aw ≤ c₀ - d / 4 := by linarith only [hd2, hd]
  have hac : c₀ - d / 4 ≤ c₀ + d / 4 := by linarith only [hd]
  have hcbw : c₀ + d / 4 ≤ bw := by linarith only [hd3, hd]
  -- moving the cuts
  have hmove := move_iff e (descentOf hL hV0 hg hsupp hle) hgc haw hac hcbw
    (hKband aw (c₀ - d / 4) le_rfl (hac.trans hcbw)) (hKband (c₀ + d / 4) bw (haw.trans hac) le_rfl)
    (fun Q h1 h2 => hstrict Q h1 (h2.trans (hac.trans hcbw))
      (hnotC Q (fun h => by linarith only [h, h2, hd])))
    (fun Q h1 h2 => hstrict Q (haw.trans (hac.trans h1)) h2
      (hnotC Q (fun h => by linarith only [h, h1, hd])))
    hsa hsb habw l
  -- the tight crossing is the lens pair of the label set
  have ha' : max aw (c₀ + d / 4 - dF / 2) < c₀ - d / 4 :=
    max_lt (by linarith only [hd2, hd]) (by linarith only [hd1, hd])
  have hcross := crossing_iff e (descentOf hL hV0 hg hsupp hle) (a' := max aw (c₀ + d / 4 - dF / 2))
    (𝒲 := 𝒲) hgc hac ha' zero_le_one
    (htrap _ (c₀ + d / 4) 1 (le_max_left _ _) hcbw (by
      have := le_max_right aw (c₀ + d / 4 - dF / 2)
      linarith only [this, hdF]) le_rfl) l
  exact hmove.mpr (hcross.mpr (hP (c₀ - d / 4) (c₀ + d / 4) 1 le_rfl (by linarith only [hd])
    (by linarith only [hd]) (by linarith only [hd4, hd])))

end

end Finsler.LevelCrossingCup
