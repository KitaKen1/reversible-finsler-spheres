module

public import Finsler.Topology.GapOrdinary
public import Finsler.Topology.CrossingSupport
public import Finsler.Algebra.BandWindow

/-! The comparison on degree gaps from basic inputs (source Lemma 9.2, assembly). The basic
inputs (`BasicGaps`) are: a power of w annihilating the global reflection classes; a finite set
of slopes containing 0 and the resonance slope α; a margin c; a filling increment D; and for
large cuts a:

* local supports: the ordinary crossing groups of single crossings between a and a + D + 1
  vanish in degrees farther than c from all lines s a, and the reflection Borel crossing groups
  of single crossings below a vanish in degrees above all lines s a by more than c;
* filling: for b ≥ a + D the image of the ordinary restriction from t_b to t_a lies in the image
  of the restriction from the loop space;
* resonance: the ordinary restriction from the loop space to t_a is injective in degrees below
  α a - c and zero in degrees above α a + c, outside the low degrees;
* a bound for the cokernel of global restriction in the band degrees.

With finitely many prime closed geodesic images these give `ComparisonGaps`: a degree farther
than c + N + 3 from all slope lines lies above all of them, where the reflection Borel
cohomology of the cut vanishes, or in a long window between two consecutive lines, where the
ordinary restriction is bijective (below the resonance line) or the ordinary cohomology of the
cut vanishes (above it). The basic inputs are hypotheses; they are not proved. -/

@[expose] public section

namespace Finsler.ComparisonBasic

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.CriticalLevels Finsler.NilpotentW Finsler.EventSum
open Finsler.DefectBound Finsler.Defect Finsler.GapOrdinary

noncomputable section

variable {n : ℕ}

/-- The basic inputs of the comparison on degree gaps. -/
structure BasicGaps (F : ReversibleMetric n) where
  /-- a power of w annihilating the global reflection classes -/
  N : ℕ
  w_nil : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0
  /-- the slopes -/
  S : Finset ℝ
  zero_mem : (0 : ℝ) ∈ S
  S_nonneg : ∀ s ∈ S, 0 ≤ s
  /-- the resonance slope -/
  α : ℝ
  α_mem : α ∈ S
  /-- the margin -/
  c : ℝ
  c_nonneg : 0 ≤ c
  /-- the filling increment -/
  D : ℝ
  D_nonneg : 0 ≤ D
  /-- the threshold for the cuts -/
  a₀ : ℝ
  a₀_pos : 0 < a₀
  /-- ordinary crossing groups just above a cut vanish away from the slope lines -/
  cross_zero : ∀ (a a' b' : ℝ) (hab' : a' ≤ b'), a₀ ≤ a → a ≤ a' → b' ≤ a + D + 1 →
    a' ∉ crit F → b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
    (∀ s ∈ S, c < |(i : ℝ) - s * a|) → ∀ z : H (crossComplex F hab') i, z = 0
  /-- reflection Borel crossing groups below a cut vanish above all slope lines -/
  cross_top : ∀ (a a' b' : ℝ) (hab' : a' ≤ b'), a₀ ≤ a → 0 < a' → b' ≤ a →
    a' ∉ crit F → b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
    (∀ s ∈ S, s * a + c < (i : ℝ)) → ∀ z : HR (crossComplex F hab') i, z = 0
  /-- filling: classes that extend by D extend to the loop space -/
  fill : ∀ (a b : ℝ) (hab : a ≤ b), a₀ ≤ a → a + D ≤ b → ∀ (i : ℕ) (y : H (levComplex F b) i),
    ∃ x : H (fullComplex n) i, Hmap (resHom F a) i x = Hmap (cutHom F hab) i y
  /-- resonance below the line of slope α -/
  res_inj : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, c < (i : ℝ) → (i : ℝ) < α * a - c →
    Function.Injective (Hmap (resHom F a) i)
  /-- resonance above the line of slope α -/
  res_zero : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, α * a + c < (i : ℝ) →
    ∀ x : H (fullComplex n) i, Hmap (resHom F a) i x = 0
  /-- the bound for the band degrees -/
  R : ℕ
  band_rank : ∀ a, a₀ ≤ a → a ∉ crit F → 2 * a ∉ crit F → ∀ j : ℕ,
    (∃ s ∈ S, |(j : ℝ) - s * a| ≤ c + N + 3) → finrank (ZMod 2) (coker F a j) ≤ R

variable {F : ReversibleMetric n}

/-- With finitely many prime closed geodesic images there is a regular cut in every interval
(p, p + 1). -/
theorem exists_regular_between (hfin : (primeImages F).Finite) (p : ℝ) :
    ∃ y, p < y ∧ y < p + 1 ∧ y ∉ crit F := by
  have hS : (crit F ∩ Icc p (p + 1)).Finite := crit_finite F hfin p (p + 1)
  have hI : (Ioo p (p + 1)).Infinite := Ioo_infinite (by linarith)
  obtain ⟨y, hy, hyS⟩ := (hI.sdiff hS).nonempty
  exact ⟨y, hy.1, hy.2, fun hc => hyS ⟨hc, hy.1.le, hy.2.le⟩⟩

/-- Surjectivity of the ordinary restriction from the loop space in a degree which, with the
next one, is far from the slope lines. -/
theorem res_surjective (B : BasicGaps F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : B.a₀ ≤ a) (hac : a ∉ crit F) (i : ℕ)
    (h0 : ∀ s ∈ B.S, B.c < |(i : ℝ) - s * a|)
    (h1 : ∀ s ∈ B.S, B.c < |((i + 1 : ℕ) : ℝ) - s * a|) :
    Function.Surjective (Hmap (resHom F a) i) := by
  obtain ⟨b, hb1, hb2, hbc⟩ := exists_regular_between hfin (a + B.D)
  have hab : a ≤ b := by linarith [B.D_nonneg]
  refine CrossingSupport.res_surjective_of_crossings F hn hfin (B.a₀_pos.trans_le ha) hab hac hbc i
    (fun a' b' hab' haa' hb'b ha'c hb'c hsub => ?_) (B.fill a b hab ha hb1.le i)
  have hb' : b' ≤ a + B.D + 1 := by linarith
  exact ⟨B.cross_zero a a' b' hab' ha haa' hb' ha'c hb'c hsub i h0,
    B.cross_zero a a' b' hab' ha haa' hb' ha'c hb'c hsub (i + 1) h1⟩

/-- The least distance between distinct slopes. -/
def gamma (B : BasicGaps F) : ℝ := Classical.choose (BandWindow.exists_gap B.S)

theorem gamma_pos (B : BasicGaps F) : 0 < gamma B :=
  (Classical.choose_spec (BandWindow.exists_gap B.S)).1

theorem gamma_le (B : BasicGaps F) : ∀ σ ∈ B.S, ∀ τ ∈ B.S, σ < τ → gamma B ≤ τ - σ :=
  (Classical.choose_spec (BandWindow.exists_gap B.S)).2

/-- The band of a cut: the degrees within c + N + 3 of a slope line. -/
def band (B : BasicGaps F) (a : ℝ) : Finset ℕ :=
  B.S.biUnion fun s =>
    Finset.Icc ⌈s * a - (B.c + B.N + 3)⌉₊ ⌊s * a + (B.c + B.N + 3)⌋₊

/-- A degree within c + N + 3 of a slope line lies in the band. -/
theorem mem_band (B : BasicGaps F) {a : ℝ} {j : ℕ} {s : ℝ} (hs : s ∈ B.S)
    (h : |(j : ℝ) - s * a| ≤ B.c + B.N + 3) : j ∈ band B a := by
  rw [abs_le] at h
  refine Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
  · exact Nat.ceil_le.mpr (by linarith [h.1])
  · exact Nat.le_floor (by linarith [h.2])

/-- A degree of the band is within c + N + 3 of a slope line, for a nonnegative cut. -/
theorem exists_of_mem_band (B : BasicGaps F) {a : ℝ} (ha : 0 ≤ a) {j : ℕ}
    (hj : j ∈ band B a) : ∃ s ∈ B.S, |(j : ℝ) - s * a| ≤ B.c + B.N + 3 := by
  obtain ⟨s, hs, hmem⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmem
  have hN : (0 : ℝ) ≤ B.N := Nat.cast_nonneg _
  have h0 : 0 ≤ s * a + (B.c + B.N + 3) := by
    have := mul_nonneg (B.S_nonneg s hs) ha
    linarith [B.c_nonneg]
  refine ⟨s, hs, abs_le.mpr ⟨?_, ?_⟩⟩
  · have := Nat.ceil_le.mp h1
    linarith
  · have h3 : (j : ℝ) ≤ (⌊s * a + (B.c + B.N + 3)⌋₊ : ℝ) := Nat.cast_le.mpr h2
    have h4 := Nat.floor_le h0
    linarith

/-- The number of degrees in the band is bounded independently of the cut. -/
theorem band_card_le (B : BasicGaps F) {a : ℝ} (ha : 0 ≤ a) :
    (band B a).card ≤ B.S.card * (⌊2 * (B.c + B.N + 3)⌋₊ + 1) := by
  have hN : (0 : ℝ) ≤ B.N := Nat.cast_nonneg _
  refine (Finset.card_biUnion_le).trans ?_
  rw [← smul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun s hs => ?_
  rw [Nat.card_Icc]
  have h0 : 0 ≤ s * a + (B.c + B.N + 3) := by
    have := mul_nonneg (B.S_nonneg s hs) ha
    linarith [B.c_nonneg]
  have h1 : (⌊s * a + (B.c + B.N + 3)⌋₊ : ℝ) ≤ s * a + (B.c + B.N + 3) := Nat.floor_le h0
  have h2 : s * a - (B.c + B.N + 3) ≤ (⌈s * a - (B.c + B.N + 3)⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : ⌊s * a + (B.c + B.N + 3)⌋₊ - ⌈s * a - (B.c + B.N + 3)⌉₊ ≤
      ⌊2 * (B.c + B.N + 3)⌋₊ := by
    by_cases hle : ⌈s * a - (B.c + B.N + 3)⌉₊ ≤ ⌊s * a + (B.c + B.N + 3)⌋₊
    · refine Nat.le_floor ?_
      rw [Nat.cast_sub hle]
      linarith
    · rw [Nat.sub_eq_zero_of_le (not_le.mp hle).le]
      exact Nat.zero_le _
  omega

/-- The threshold for the cuts in the comparison. -/
def threshold (B : BasicGaps F) : ℝ :=
  max B.a₀ (15 * (2 * B.c + 2 * B.N + 4) / gamma B)

/-- The comparison on degree gaps from the basic inputs. -/
def toComparisonGaps (B : BasicGaps F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ComparisonGaps F where
  N := B.N
  w_nil := B.w_nil
  a₀ := threshold B
  δ := gamma B / 30
  δ_pos := div_pos (gamma_pos B) (by norm_num)
  W := B.S.card * (⌊2 * (B.c + B.N + 3)⌋₊ + 1)
  R := B.R
  band := fun a => if 0 ≤ a then band B a else ∅
  band_card := fun a => by
    by_cases ha : 0 ≤ a
    · rw [ite_eq_left ha]
      exact band_card_le B ha
    · rw [ite_eq_right ha, Finset.card_empty]
      exact Nat.zero_le _
  band_rank := fun a ha hac h2a j hj => by
    have ha₀ : B.a₀ ≤ a := (le_max_left _ _).trans ha
    have ha0 : 0 ≤ a := (B.a₀_pos.trans_le ha₀).le
    rw [ite_eq_left ha0] at hj
    exact B.band_rank a ha₀ hac h2a j (exists_of_mem_band B ha0 hj)
  gap := fun a ha hac h2a j hj => by
    have hN : (0 : ℝ) ≤ B.N := Nat.cast_nonneg _
    have ha₀ : B.a₀ ≤ a := (le_max_left _ _).trans ha
    have ha0 : 0 < a := B.a₀_pos.trans_le ha₀
    have hγ := gamma_pos B
    have ha2 : 15 * (2 * B.c + 2 * B.N + 4) ≤ gamma B * a := by
      have h : 15 * (2 * B.c + 2 * B.N + 4) / gamma B ≤ a := (le_max_right _ _).trans ha
      rw [div_le_iff₀ hγ] at h
      linarith
    rw [ite_eq_left ha0.le] at hj
    have hfar : ∀ s ∈ B.S, B.c + B.N + 3 < |(j : ℝ) - s * a| := fun s hs => by
      by_contra hcon
      exact hj (mem_band B hs (not_lt.mp hcon))
    rcases BandWindow.exists_window B.zero_mem (gamma_le B) B.c_nonneg B.N ha0 ha2 j hfar
      with habove | ⟨g₀, t, ht, hg₀j, hjg, hNg, hwin⟩
    · refine Or.inl fun x => ?_
      refine CrossingSupport.lev_eq_zero_of_crossings F hn hfin ha0 hac j
        (fun a' b' hab' ha' hb'a ha'c hb'c hsub z => ?_) x
      refine B.cross_top a a' b' hab' ha₀ ha' hb'a ha'c hb'c hsub j (fun s hs => ?_) z
      have h1 := hfar s hs
      rw [abs_of_pos (sub_pos.mpr (habove s hs))] at h1
      linarith
    · have hside : ∀ i : ℕ, g₀ ≤ i + B.N → i ≤ g₀ + 14 * t + B.N + 2 →
          B.c < (i : ℝ) ∧ ((B.α * a < j → B.α * a + B.c < i) ∧
            (¬ B.α * a < j → (i : ℝ) < B.α * a - B.c)) := by
        intro i hi1 hi2
        have h0 := (hwin i hi1 hi2 0 B.zero_mem).1
        rw [zero_mul, sub_zero, abs_of_nonneg (Nat.cast_nonneg i)] at h0
        obtain ⟨hα1, hα2⟩ := hwin i hi1 hi2 B.α B.α_mem
        refine ⟨h0, fun hj' => ?_, fun hj' => ?_⟩
        · have hi : B.α * a < i := hα2.mpr hj'
          rw [abs_of_pos (sub_pos.mpr hi)] at hα1
          linarith
        · have hi : ¬ B.α * a < i := fun h => hj' (hα2.mp h)
          rw [abs_of_nonpos (sub_nonpos.mpr (not_lt.mp hi))] at hα1
          linarith
      have hsurj : ∀ i : ℕ, g₀ ≤ i + B.N → i + 1 ≤ g₀ + 14 * t + B.N + 2 →
          Function.Surjective (Hmap (resHom F a) i) := fun i hi1 hi2 =>
        res_surjective B hn hfin ha₀ hac i
          (fun s hs => (hwin i hi1 (by omega) s hs).1)
          (fun s hs => (hwin (i + 1) (by omega) hi2 s hs).1)
      by_cases hαj : B.α * a < j
      · refine Or.inr (Or.inr ⟨g₀, t, ht, hg₀j, hjg, fun i hi1 hi2 z => ?_⟩)
        obtain ⟨x, rfl⟩ := hsurj i (by omega) (by omega) z
        exact B.res_zero a ha₀ i ((hside i (by omega) (by omega)).2.1 hαj) x
      · refine Or.inr (Or.inl ⟨g₀, t, ht, hg₀j, hjg, hNg, fun i hi1 hi2 => ?_⟩)
        have hs := hside i hi1 (by omega)
        exact ⟨B.res_inj a ha₀ i hs.1 (hs.2.2 hαj), hsurj i hi1 (by omega)⟩

/-- With finitely many prime closed geodesic images, the local bounds for single crossings and
the basic inputs of the comparison on degree gaps, the defect is bounded on all positive regular
cuts. -/
theorem exists_defect_le_of_basic (E : EventBounds F) (B : BasicGaps F) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a, 0 < a → a ∉ crit F → defect F a ≤ C :=
  exists_defect_le_of_comparison E (toComparisonGaps B hn hfin) hn hfin

end

end Finsler.ComparisonBasic
