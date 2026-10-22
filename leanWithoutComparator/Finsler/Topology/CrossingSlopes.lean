module

public import Finsler.Topology.LevelUniform
public import Finsler.Topology.CutFinite
public import Finsler.Topology.GysinCount
public import Finsler.Topology.OrdinaryRestriction
public import Finsler.Topology.BandRank

/-! Single crossings and slope lines. The ordinary connecting map of a short exact sequence of
involutive complexes vanishes on the image of the middle complex; hence the ordinary cohomology
of the subcomplex vanishes if the quotient map is bijective in all degrees, and the ordinary
crossing of a regular strip vanishes. Reflection Borel cohomology vanishes above the ordinary
cohomology as soon as it vanishes in high degrees (w is injective where the ordinary cohomology
vanishes, by the Gysin sequence); the reflection Borel crossing at regular cuts vanishes in high
degrees. With finitely many prime closed geodesic images there are a bound B and a finite set S
of slopes Δ/√E (mean index over length of the prime closed geodesics, and 0) such that every
single crossing at regular cuts has ordinary and reflection Borel groups of dimension at most B
in every degree, and for every D ≥ 0 a margin c with: the ordinary groups of a single crossing
in [a, a + D + 1] vanish in degrees i with |i - s a| > c for all slopes s, and the reflection
Borel groups of a single crossing below a vanish in degrees i > s a + c for all slopes s. -/

@[expose] public section

namespace Finsler.CrossingSlopes

open Module Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.CircleLabel Finsler.CircleRoot
open Finsler.GeodesicFrames Finsler.LevelBounds Finsler.LevelUniform
open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelExact Finsler.BorelCrossing

noncomputable section

section Algebra

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''}

/-- The ordinary connecting map vanishes on the image of the middle complex. -/
theorem delta_comp_zero_ordinary (h : ShortExact ι π) (n : ℕ) (x : H K n) :
    Finsler.OrdinaryDelta.delta h n (Hmap π n x) = 0 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Hmap, Submodule.mapQ_apply, Finsler.OrdinaryDelta.delta, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change ret h (n + 1) (K.d n (sec h n (π.f n (b : K.C n)))) ∈ coboundaries K' (n + 1)
  obtain ⟨v, hv⟩ := Finsler.OrdinaryDelta.d_sec_eq h n _ (b : K.C n) rfl
  rw [hv, LinearMap.mem_ker.mp b.2, zero_add, ret_incl]
  exact ⟨v, rfl⟩

/-- The ordinary cohomology of the subcomplex vanishes if the quotient map is bijective on
ordinary cohomology in all degrees. -/
theorem sub_zero_of_bijective (h : ShortExact ι π) (hbij : ∀ q, Function.Bijective (Hmap π q))
    (q : ℕ) (z : H K' q) : z = 0 := by
  have h1 : Hmap ι q z = 0 :=
    (hbij q).1 ((comp_zero_ordinary h q z).trans (map_zero (Hmap π q)).symm)
  cases q with
  | zero => exact Hmap_zero_injective h (h1.trans (map_zero _).symm)
  | succ q =>
    obtain ⟨y, hy⟩ := Finsler.OrdinaryDelta.exact_sub h q z h1
    obtain ⟨x, rfl⟩ := (hbij q).2 y
    rw [← hy, delta_comp_zero_ordinary]

/-- Reflection Borel cohomology vanishes from degree i on if ordinary cohomology does and
reflection Borel cohomology vanishes in high degrees. -/
theorem HR_zero_above (K : InvComplex) {i Q : ℕ} (hH : ∀ q, i ≤ q → ∀ z : H K q, z = 0)
    (hQ : ∀ q, Q ≤ q → ∀ y : HR K q, y = 0) (y : HR K i) : y = 0 := by
  have hinj : ∀ q, i ≤ q → Function.Injective (w K q) := by
    intro q hq
    rw [← LinearMap.ker_eq_bot, ← Finsler.GysinCount.range_transfer, LinearMap.range_eq_bot]
    refine LinearMap.ext fun z => ?_
    rw [hH q hq z, map_zero]
    rfl
  have step : ∀ q, i ≤ q → (∀ y : HR K (q + 1), y = 0) → ∀ y : HR K q, y = 0 :=
    fun q hq h0 y => hinj q hq (by rw [h0 (w K q y), map_zero])
  have key : ∀ d q, i ≤ q → Q ≤ q + d → ∀ y : HR K q, y = 0 := by
    intro d
    induction d with
    | zero =>
      intro q _ hq y
      exact hQ q (by omega) y
    | succ d ih =>
      intro q hiq hq y
      exact step q hiq (ih (q + 1) (by omega) (by omega)) y
  exact key Q i le_rfl (by omega) y

end Algebra

variable {n : ℕ} (F : ReversibleMetric n)

/-- **The ordinary crossing of a regular strip vanishes.** -/
theorem cross_zero_regular (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hreg : ∀ x ∈ Icc a b, x ∉ crit F) (q : ℕ) (z : H (crossComplex F hab) q) : z = 0 :=
  sub_zero_of_bijective (shortExact F hab)
    (fun q => Finsler.OrdinaryRestriction.cut_bijective_of_regular F hn ha hab hreg q) q z

/-- The reflection Borel cohomology of a crossing pair at regular cuts vanishes in high
degrees. -/
theorem exists_crossHR_high (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hac : a ∉ crit F) (hbc : b ∉ crit F) :
    ∃ Q : ℕ, ∀ q, Q ≤ q → ∀ y : HR (crossComplex F hab) q, y = 0 := by
  obtain ⟨ka, -, hza⟩ := Finsler.FiniteCut.exists_finite_HR F hn hfin ha hac
  obtain ⟨kb, -, hzb⟩ := Finsler.FiniteCut.exists_finite_HR F hn hfin (ha.trans_le hab) hbc
  refine ⟨max ka kb + 1, fun q hq y => ?_⟩
  exact Finsler.CutFinite.sub_eq_zero_of_zero (shortExact F hab) q
    (fun x => hzb q (by have := le_max_right ka kb; omega) x)
    (fun p hp x => hza p (by have := le_max_left ka kb; omega) x) y


/-- The ordinary crossing pair and the trivial pair have the same ordinary cohomology. -/
def crossEquiv {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    H (crossComplex F hab) q ≃ₗ[ZMod 2] H (triv (pairOf (lev_mono F hab))) q :=
  ofPairEquiv (crossPair F hab) (revCross_sq F hab) (Category.comp_id _) q

open Classical in
/-- The slope of a label: mean index over length. -/
def slope (ℓ : Set (Sphere n) × Bool) : ℝ :=
  if h : ℓ.1 ∈ primeImages F then
    (iterData (labelGeod F ℓ h)).Δ / Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 h).loop)
  else 0

set_option maxHeartbeats 3200000 in
/-- **The support of a single crossing near the slope lines.** With finitely many prime closed
geodesic images there are A and the finite set of slopes (0 and mean index over length of the
prime closed geodesics) such that the ordinary groups of a single crossing at regular cuts are
nonzero only in degrees i within A of s c₀ for a critical level c₀ of the crossing and a slope
s. -/
theorem exists_single_support (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
      (∃ z : H (crossComplex F hab') i, z ≠ 0) →
      ∃ c₀ ∈ crit F ∩ Icc a' b', ∃ s ∈ insert (0 : ℝ) ((labels F hfin).image (slope F)),
        |(i : ℝ) - s * c₀| ≤ A := by
  classical
  obtain ⟨B, A, hBA⟩ := exists_level_bounds F hn hfin
  refine ⟨A + n, fun a' b' hab' ha' hac hbc hsub i ⟨z, hz⟩ => ?_⟩
  by_cases hreg : ∀ x ∈ Icc a' b', x ∉ crit F
  · exact absurd (cross_zero_regular F hn ha' hab' hreg i z) hz
  · push Not at hreg
    obtain ⟨c₀, ⟨h1', h2'⟩, hc₀⟩ := hreg
    have h1 : a' < c₀ := lt_of_le_of_ne h1' fun h => hac (h ▸ hc₀)
    have h2 : c₀ < b' := lt_of_le_of_ne h2' fun h => hbc (h.symm ▸ hc₀)
    have hone : ∀ c' ∈ crit F, a' ≤ c' → c' ≤ b' → c' = c₀ := fun c' hc' h3 h4 =>
      hsub ⟨hc', h3, h4⟩ ⟨hc₀, h1', h2'⟩
    have hz' : crossEquiv F hab' i z ≠ 0 := fun h =>
      hz ((crossEquiv F hab' i).map_eq_zero_iff.mp h)
    obtain ⟨-, hwin⟩ := hBA hab' ha' h1 h2 hone
    obtain ⟨ℓ, hℓ, k, hk, hq1, hq2⟩ := hwin i ⟨_, hz'⟩
    have hp := (mem_labels F hfin ℓ).mp hℓ
    have hEpos := Finsler.OrientedCritical.chosen_energy_pos F ℓ.1 hp
    have hc₀pos : 0 < c₀ := ha'.trans h1
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, Nat.cast_zero, zero_mul] at hk
        linarith
      · exact h0
    have hmean := (iterData (labelGeod F ℓ hp)).mean k hk1
    have hs : slope F ℓ * c₀ = (k : ℝ) * (iterData (labelGeod F ℓ hp)).Δ := by
      unfold slope
      rw [dite_eq_left hp, ← hk]
      field_simp
    refine ⟨c₀, ⟨hc₀, h1', h2'⟩, slope F ℓ,
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hℓ), ?_⟩
    rw [hs]
    have hq1' : (i : ℝ) ≤ ((iterData (labelGeod F ℓ hp)).I k : ℝ) + A := by exact_mod_cast hq1
    have hq2' : ((iterData (labelGeod F ℓ hp)).I k : ℝ) ≤ (i : ℝ) + A := by exact_mod_cast hq2
    rw [abs_le] at hmean ⊢
    push_cast
    constructor <;> linarith [hmean.1, hmean.2]

set_option maxHeartbeats 3200000 in
/-- **Single crossings and slope lines.** -/
theorem exists_crossing_slopes (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ (B : ℕ) (S : Finset ℝ), (0 : ℝ) ∈ S ∧ (∀ s ∈ S, 0 ≤ s) ∧
      (∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → a' ∉ crit F → b' ∉ crit F →
        (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
          finrank (ZMod 2) (H (crossComplex F hab') i) ≤ B ∧
            finrank (ZMod 2) (HR (crossComplex F hab') i) ≤ B) ∧
      ∀ D : ℝ, 0 ≤ D → ∃ c : ℝ, 0 ≤ c ∧
        (∀ (a a' b' : ℝ) (hab' : a' ≤ b'), 0 < a → a ≤ a' → b' ≤ a + D + 1 →
          a' ∉ crit F → b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
          (∀ s ∈ S, c < |(i : ℝ) - s * a|) → ∀ z : H (crossComplex F hab') i, z = 0) ∧
        (∀ (a a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → b' ≤ a →
          a' ∉ crit F → b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ,
          (∀ s ∈ S, s * a + c < (i : ℝ)) → ∀ z : HR (crossComplex F hab') i, z = 0) := by
  classical
  obtain ⟨B, A, hBA⟩ := exists_level_bounds F hn hfin
  set S : Finset ℝ := insert 0 ((labels F hfin).image (slope F)) with hSdef
  have hslope : ∀ ℓ, 0 ≤ slope F ℓ := by
    intro ℓ
    unfold slope
    split_ifs with h
    · exact div_nonneg (iterData (labelGeod F ℓ h)).mean_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have hSnn : ∀ s ∈ S, 0 ≤ s := by
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact le_rfl
    · obtain ⟨ℓ, -, rfl⟩ := Finset.mem_image.mp hs
      exact hslope ℓ
  -- a single crossing at regular cuts: the regular case and the case of one critical level
  have hcases : ∀ (a' b' : ℝ), 0 < a' → a' ≤ b' → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton →
      (∀ x ∈ Icc a' b', x ∉ crit F) ∨
        ∃ c₀, a' < c₀ ∧ c₀ < b' ∧ c₀ ∈ crit F ∧ ∀ c' ∈ crit F, a' ≤ c' → c' ≤ b' → c' = c₀ := by
    intro a' b' ha' hab' hac hbc hsub
    by_cases hreg : ∀ x ∈ Icc a' b', x ∉ crit F
    · exact Or.inl hreg
    · right
      push Not at hreg
      obtain ⟨c₀, ⟨h1, h2⟩, hc₀⟩ := hreg
      refine ⟨c₀, lt_of_le_of_ne h1 fun h => hac (h ▸ hc₀), lt_of_le_of_ne h2 fun h => hbc (h.symm ▸ hc₀),
        hc₀, fun c' hc' h3 h4 => hsub ⟨hc', h3, h4⟩ ⟨hc₀, h1, h2⟩⟩
  -- the support of a single crossing near the slope lines
  have hsupp : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton → ∀ i : ℕ, (∃ z : H (crossComplex F hab') i, z ≠ 0) →
      ∃ c₀ ∈ Icc a' b', ∃ s ∈ S, |(i : ℝ) - s * c₀| ≤ A + n := by
    intro a' b' hab' ha' hac hbc hsub i ⟨z, hz⟩
    rcases hcases a' b' ha' hab' hac hbc hsub with hreg | ⟨c₀, h1, h2, -, hone⟩
    · exact absurd (cross_zero_regular F hn ha' hab' hreg i z) hz
    · have hz' : crossEquiv F hab' i z ≠ 0 := fun h => hz ((crossEquiv F hab' i).map_eq_zero_iff.mp h)
      obtain ⟨-, hwin⟩ := hBA hab' ha' h1 h2 hone
      obtain ⟨ℓ, hℓ, k, hk, hq1, hq2⟩ := hwin i ⟨_, hz'⟩
      have hp := (mem_labels F hfin ℓ).mp hℓ
      have hEpos := Finsler.OrientedCritical.chosen_energy_pos F ℓ.1 hp
      have hc₀pos : 0 < c₀ := ha'.trans h1
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.cast_zero, zero_mul] at hk
          linarith
        · exact h0
      have hmean := (iterData (labelGeod F ℓ hp)).mean k hk1
      have hs : slope F ℓ * c₀ = (k : ℝ) * (iterData (labelGeod F ℓ hp)).Δ := by
        unfold slope
        rw [dite_eq_left hp, ← hk]
        field_simp
      refine ⟨c₀, ⟨h1.le, h2.le⟩, slope F ℓ, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hℓ), ?_⟩
      rw [hs]
      have hq1' : (i : ℝ) ≤ ((iterData (labelGeod F ℓ hp)).I k : ℝ) + A := by exact_mod_cast hq1
      have hq2' : ((iterData (labelGeod F ℓ hp)).I k : ℝ) ≤ (i : ℝ) + A := by exact_mod_cast hq2
      rw [abs_le] at hmean ⊢
      constructor <;> linarith [hmean.1, hmean.2]
  set sS : ℝ := ∑ s ∈ S, s with hsS
  have hsSle : ∀ s ∈ S, s ≤ sS := fun s hs =>
    Finset.single_le_sum (f := fun s => s) (fun s hs => hSnn s hs) hs
  have hsSnn : 0 ≤ sS := Finset.sum_nonneg fun s hs => hSnn s hs
  refine ⟨B, S, Finset.mem_insert_self _ _, hSnn, ?_, fun D hD => ⟨A + n + (D + 1) * sS, by positivity, ?_, ?_⟩⟩
  · -- the rank bounds
    intro a' b' hab' ha' hac hbc hsub i
    obtain ⟨-, hfinX, -⟩ := cross_finite F hn hfin ha' hab' hac hbc
    have hfinC : ∀ q, Module.Finite (ZMod 2) (H (crossComplex F hab') q) := fun q => by
      have := hfinX q
      exact Module.Finite.equiv (crossEquiv F hab' q).symm
    -- the total of the ordinary crossing is at most B
    have htot : ∀ Q, ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (crossComplex F hab') q) ≤ B := by
      intro Q
      rcases hcases a' b' ha' hab' hac hbc hsub with hreg | ⟨c₀, h1, h2, -, hone⟩
      · have : ∀ q, finrank (ZMod 2) (H (crossComplex F hab') q) = 0 := fun q => by
          have : Subsingleton (H (crossComplex F hab') q) :=
            ⟨fun x y => (cross_zero_regular F hn ha' hab' hreg q x).trans
              (cross_zero_regular F hn ha' hab' hreg q y).symm⟩
          exact finrank_zero_of_subsingleton
        simp only [this, Finset.sum_const_zero, Nat.zero_le]
      · obtain ⟨htot, -⟩ := hBA hab' ha' h1 h2 hone
        calc ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (crossComplex F hab') q)
            = ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (triv (pairOf (lev_mono F hab'))) q) :=
              Finset.sum_congr rfl fun q _ => (crossEquiv F hab' q).finrank_eq
          _ ≤ B := htot Q
    refine ⟨?_, ?_⟩
    · calc finrank (ZMod 2) (H (crossComplex F hab') i)
          ≤ ∑ q ∈ Finset.range (i + 1), finrank (ZMod 2) (H (crossComplex F hab') q) :=
            Finset.single_le_sum (f := fun q => finrank (ZMod 2) (H (crossComplex F hab') q))
              (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self i))
        _ ≤ B := htot (i + 1)
    · exact (Finsler.BandRank.finrank_HR_le_sum (crossComplex F hab') hfinC i).trans (htot (i + 1))
  · -- the ordinary groups vanish away from the slope lines
    intro a a' b' hab' ha haa' hb' hac hbc hsub i hfar z
    by_contra hz
    obtain ⟨c₀, ⟨h1, h2⟩, s, hs, hle⟩ := hsupp a' b' hab' (ha.trans_le haa') hac hbc hsub i ⟨z, hz⟩
    have hfs := hfar s hs
    have hsn := hSnn s hs
    have hsl := hsSle s hs
    have hc0 : |s * c₀ - s * a| ≤ s * (D + 1) := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hsn]
      apply mul_le_mul_of_nonneg_left _ hsn
      rw [abs_le]
      constructor <;> linarith
    have htri : |(i : ℝ) - s * a| ≤ |(i : ℝ) - s * c₀| + |s * c₀ - s * a| := by
      have := abs_sub_le (i : ℝ) (s * c₀) (s * a)
      linarith
    have hsD : s * (D + 1) ≤ (D + 1) * sS := by nlinarith
    linarith
  · -- the reflection Borel groups vanish above the slope lines
    intro a a' b' hab' ha' hb'a hac hbc hsub i habove z
    obtain ⟨Q, hQ⟩ := exists_crossHR_high F hn hfin ha' hab' hac hbc
    refine HR_zero_above (crossComplex F hab') (fun q hq z' => ?_) hQ z
    by_contra hz
    obtain ⟨c₀, ⟨h1, h2⟩, s, hs, hle⟩ := hsupp a' b' hab' ha' hac hbc hsub q ⟨z', hz⟩
    have hab := habove s hs
    have hsn := hSnn s hs
    have hc0a : s * c₀ ≤ s * a := mul_le_mul_of_nonneg_left (h2.trans hb'a) hsn
    have hqi : (i : ℝ) ≤ q := by exact_mod_cast hq
    rw [abs_le] at hle
    have : 0 ≤ (D + 1) * sS := by positivity
    linarith [hle.2]

end

end Finsler.CrossingSlopes
