module

public import Finsler.Topology.ComparisonBasic
public import Finsler.Topology.BandRank
public import Finsler.Topology.OrdinaryRank
public import Finsler.Topology.WindowCount

/-! The band rank from local ranks, and the bounded defect from basic data (source (9.8), (9.9)
and the end of the proof of Theorem 9.1). The rank inputs (`RankInputs`) are: a bound C for the
reflection crossing groups of single crossings in the degrees above `jlow`, with vanishing when
no critical level of the crossing is active for the degree, and at most K active critical levels
for each such degree; a bound for the ordinary crossing groups of single crossings in the
degrees up to `jlow + 1`; and a bound G for the image of the ordinary restriction from the loop
space in the degrees up to `jlow`. With the filling statement and finitely many prime closed
geodesic images they give a uniform bound for the cokernel of global restriction of large
regular cuts in every degree. Together with the remaining basic data of the comparison on
degree gaps (`GapData`: slopes, margin, local supports, filling, resonance, the power of w) and
the local bounds for single crossings (`EventBounds`), the defect is bounded on all positive
regular cuts. All these inputs are hypotheses; none of them is proved. -/

@[expose] public section

namespace Finsler.ComparisonRank

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.CriticalLevels Finsler.NilpotentW Finsler.EventSum
open Finsler.DefectBound Finsler.Defect Finsler.GapOrdinary Finsler.ComparisonBasic

noncomputable section

variable {n : ℕ}

/-- The rank inputs for the band degrees. -/
structure RankInputs (F : ReversibleMetric n) (a₀ : ℝ) where
  /-- bound for the reflection crossing groups in high degrees -/
  C : ℕ
  /-- bound for the number of active critical levels of a high degree -/
  K : ℕ
  /-- the low degrees -/
  jlow : ℕ
  /-- the critical levels that are active for a degree -/
  act : ℕ → Set ℝ
  cross_rank : ∀ j : ℕ, jlow < j → ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → a' ∉ crit F →
    b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton →
    finrank (ZMod 2) (HR (crossComplex F hab') j) ≤ C ∧
      ((∀ l ∈ crit F ∩ Icc a' b', l ∉ act j) → ∀ z : HR (crossComplex F hab') j, z = 0)
  act_count : ∀ j : ℕ, jlow < j → ∀ a : ℝ, (crit F ∩ Icc 0 a ∩ act j).ncard ≤ K
  /-- bound for the ordinary crossing groups in low degrees -/
  Cord : ℕ
  cross_ord : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → a' ∉ crit F → b' ∉ crit F →
    (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ, i ≤ jlow →
    finrank (ZMod 2) (H (crossComplex F hab') (i + 1)) ≤ Cord
  /-- bound for the image of the ordinary restriction from the loop space in low degrees -/
  G : ℕ
  res_rank : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, i ≤ jlow →
    finrank (ZMod 2) (LinearMap.range (Hmap (resHom F a) i)) ≤ G

variable {F : ReversibleMetric n}

/-- The bound for the number of critical levels in windows of length D + 1. -/
def windowBound (hfin : (primeImages F).Finite) (D : ℝ) : ℕ :=
  Classical.choose (WindowCount.exists_window_count F hfin (D + 1))

theorem windowBound_spec (hfin : (primeImages F).Finite) (D a : ℝ) :
    (crit F ∩ Icc a (a + (D + 1))).ncard ≤ windowBound hfin D :=
  Classical.choose_spec (WindowCount.exists_window_count F hfin (D + 1)) a

/-- The uniform bound for the cokernels. -/
def rankBound {a₀ : ℝ} (I : RankInputs F a₀) (hfin : (primeImages F).Finite) (D : ℝ) : ℕ :=
  max ((I.jlow + 1) * (I.G + I.Cord * windowBound hfin D)) (I.C * I.K)

/-- The ordinary cohomology of a large regular cut in low degrees is bounded, from filling. -/
theorem finrank_lev_le {a₀ : ℝ} (I : RankInputs F a₀) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) (ha₀ : 0 < a₀) {D : ℝ} (hD : 0 ≤ D)
    (hfill : ∀ (a b : ℝ) (hab : a ≤ b), a₀ ≤ a → a + D ≤ b → ∀ (i : ℕ)
      (y : H (levComplex F b) i),
      ∃ x : H (fullComplex n) i, Hmap (resHom F a) i x = Hmap (cutHom F hab) i y)
    {a : ℝ} (ha : a₀ ≤ a) (hac : a ∉ crit F) {i : ℕ} (hi : i ≤ I.jlow) :
    finrank (ZMod 2) (H (levComplex F a) i) ≤ I.G + I.Cord * windowBound hfin D := by
  have ha0 : 0 < a := ha₀.trans_le ha
  obtain ⟨b, hb1, hb2, hbc⟩ := exists_regular_between hfin (a + D)
  have hab : a ≤ b := by linarith
  refine OrdinaryRank.finrank_lev_le_of_fill F hn hfin ha0 hab hac hbc i I.Cord I.G
    (windowBound hfin D)
    (fun a' b' hab' haa' ha'c hb'c hsub =>
      I.cross_ord a' b' hab' (ha0.trans_le haa') ha'c hb'c hsub i hi)
    (hfill a b hab ha hb1.le i) (I.res_rank a ha i hi) ?_
  refine (ncard_le_ncard (inter_subset_inter_right _ (Icc_subset_Icc le_rfl ?_))
    (crit_finite F hfin a (a + (D + 1)))).trans (windowBound_spec hfin D a)
  linarith

/-- The cokernel of global restriction of a large regular cut is bounded in every degree. -/
theorem finrank_coker_le {a₀ : ℝ} (I : RankInputs F a₀) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) (ha₀ : 0 < a₀) {D : ℝ} (hD : 0 ≤ D)
    (hfill : ∀ (a b : ℝ) (hab : a ≤ b), a₀ ≤ a → a + D ≤ b → ∀ (i : ℕ)
      (y : H (levComplex F b) i),
      ∃ x : H (fullComplex n) i, Hmap (resHom F a) i x = Hmap (cutHom F hab) i y)
    {a : ℝ} (ha : a₀ ≤ a) (hac : a ∉ crit F) (j : ℕ) :
    finrank (ZMod 2) (coker F a j) ≤ rankBound I hfin D :=
  BandRank.finrank_coker_le_max F hn hfin ha₀ I.C I.K I.jlow
    (I.G + I.Cord * windowBound hfin D) I.act I.cross_rank I.act_count
    (fun _ ha' hac' _ hi => finrank_lev_le I hn hfin ha₀ hD hfill ha' hac' hi) ha hac j

/-- The basic data of the comparison on degree gaps without the band rank. -/
structure GapData (F : ReversibleMetric n) where
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
  cross_zero : ∀ (a a' b' : ℝ) (hab' : a' ≤ b'), a₀ ≤ a → a ≤ a' → b' ≤ a + D + 1 →
    a' ∉ crit F → b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
    (∀ s ∈ S, c < |(i : ℝ) - s * a|) → ∀ z : H (crossComplex F hab') i, z = 0
  cross_top : ∀ (a a' b' : ℝ) (hab' : a' ≤ b'), a₀ ≤ a → 0 < a' → b' ≤ a →
    a' ∉ crit F → b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
    (∀ s ∈ S, s * a + c < (i : ℝ)) → ∀ z : HR (crossComplex F hab') i, z = 0
  fill : ∀ (a b : ℝ) (hab : a ≤ b), a₀ ≤ a → a + D ≤ b → ∀ (i : ℕ) (y : H (levComplex F b) i),
    ∃ x : H (fullComplex n) i, Hmap (resHom F a) i x = Hmap (cutHom F hab) i y
  res_inj : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, c < (i : ℝ) → (i : ℝ) < α * a - c →
    Function.Injective (Hmap (resHom F a) i)
  res_zero : ∀ a : ℝ, a₀ ≤ a → ∀ i : ℕ, α * a + c < (i : ℝ) →
    ∀ x : H (fullComplex n) i, Hmap (resHom F a) i x = 0

/-- The basic inputs of the comparison on degree gaps from the basic data and the rank
inputs. -/
def toBasicGaps (Gd : GapData F) (I : RankInputs F Gd.a₀) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) : BasicGaps F where
  N := Gd.N
  w_nil := Gd.w_nil
  S := Gd.S
  zero_mem := Gd.zero_mem
  S_nonneg := Gd.S_nonneg
  α := Gd.α
  α_mem := Gd.α_mem
  c := Gd.c
  c_nonneg := Gd.c_nonneg
  D := Gd.D
  D_nonneg := Gd.D_nonneg
  a₀ := Gd.a₀
  a₀_pos := Gd.a₀_pos
  cross_zero := Gd.cross_zero
  cross_top := Gd.cross_top
  fill := Gd.fill
  res_inj := Gd.res_inj
  res_zero := Gd.res_zero
  R := rankBound I hfin Gd.D
  band_rank := fun _ ha hac _ j _ =>
    finrank_coker_le I hn hfin Gd.a₀_pos Gd.D_nonneg Gd.fill ha hac j

/-- **Bounded defect from basic data** (source Theorem 9.1 with Lemma 9.2, (9.8) and (9.9)).
With finitely many prime closed geodesic images, the local bounds for single crossings, the
basic data of the comparison on degree gaps and the rank inputs, the defect is bounded on all
positive regular cuts. -/
theorem exists_defect_le_of_data (E : EventBounds F) (Gd : GapData F)
    (I : RankInputs F Gd.a₀) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a, 0 < a → a ∉ crit F → defect F a ≤ C :=
  exists_defect_le_of_basic E (toBasicGaps Gd I hn hfin) hn hfin

end

end Finsler.ComparisonRank
