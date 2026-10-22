module

public import Finsler.Topology.CrossLocalize

/-! The cutoffs near a single crossing and the far conditions from a windowed localization. For
regular cuts 2a ≤ 2b with one critical level c₀ between them, the ordinary groups of the crossing
pair live near the lines s·c₀ (s a slope of a label or zero) and those of the crossing pair at
half the cuts near s·c₀/2; since the reflection Borel groups of a single crossing embed into its
ordinary groups, the reflection Borel groups of the fixed crossing pair vanish in root degrees l
with 2l away from the lines. The windowed localization (`WindowLoc`) says: in every degree q
away from the lines s·c₀ the total normalized restriction of the K-Borel crossing group is
injective with image the families of root degrees at most q/2. A cutoff k is near if 2k + 2 is
close to some s·c₀; there are at most |S|·(⌈R⌉ + 1) of them. At a cutoff which is not near, the
fixed groups of root degrees k + 1 and k + 2 vanish and the degrees 2k + 1, 2k + 2, 2k + 3 are
away from the lines, so the far conditions hold; without critical level all groups vanish.
Hence the local bounds of the events follow from the windowed localization. Above all lines the
windowed localization holds (`CrossLocalize`: restriction to the fixed crossing is bijective
above the reflection Borel groups, and the fixed groups vanish in root degrees above q/2), so it
suffices to know it in the degrees below some line (`GapLoc`). That part (K-equivariant local
Morse theory of a single critical level: splitting into critical orbits and localization at the
loops fixed by the half rotation for each orbit) is not proved here. -/

@[expose] public section

namespace Finsler.EventFar

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelFixed Finsler.FixedLadder Finsler.CutPotential Finsler.AvoidPoint
open Finsler.BorelIterate Finsler.BorelCrossingK Finsler.GradedLadder
open Finsler.CriticalLevels Finsler.CrossingSlopes Finsler.LevelBounds Finsler.LevelUniform
open Finsler.IntervalSobolev Finsler.SobolevReverse Finsler.PairTriple
open Finsler.EventRanks Finsler.EventSum Finsler.BorelK Finsler.TotalExact
open Finsler.CriticalCircles

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-! ### Windows of cutoffs -/

/-- The cutoffs k with 2k + 2 within R of x. -/
def win (x R : ℝ) : Finset ℕ :=
  (Finset.range (⌈x + R⌉₊ + 1)).filter fun k => |(2 * (k : ℝ) + 2) - x| ≤ R

theorem mem_win {x R : ℝ} {k : ℕ} : k ∈ win x R ↔ |(2 * (k : ℝ) + 2) - x| ≤ R := by
  unfold win
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have h1 := (abs_le.mp h).2
    have h2 : (k : ℝ) ≤ ⌈x + R⌉₊ := by
      have := Nat.le_ceil (x + R)
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have : k ≤ ⌈x + R⌉₊ := by exact_mod_cast h2
    omega

/-- A window contains at most ⌈R⌉ + 1 cutoffs. -/
theorem card_win (x R : ℝ) : (win x R).card ≤ ⌈R⌉₊ + 1 := by
  set lo := ⌈(x - R - 2) / 2⌉₊
  have hsub : win x R ⊆ Finset.Icc lo (lo + ⌈R⌉₊) := by
    intro k hk
    have h := abs_le.mp (mem_win.mp hk)
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.ceil_le.mpr (by linarith [h.1])
    · have h1 : (x - R - 2) / 2 ≤ (lo : ℝ) := Nat.le_ceil _
      have h2 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
      have h3 : (k : ℝ) ≤ (lo : ℝ) + ⌈R⌉₊ := by linarith [h.2]
      exact_mod_cast h3
  calc (win x R).card ≤ (Finset.Icc lo (lo + ⌈R⌉₊)).card := Finset.card_le_card hsub
    _ = ⌈R⌉₊ + 1 := by rw [Nat.card_Icc]; omega

open Classical in
/-- The cutoffs near the crossing of the cuts 2a and 2b: those k with 2k + 2 within R of s·c₀
for a critical level c₀ between the cuts and some s ∈ S. -/
def near (S : Finset ℝ) (R a b : ℝ) : Finset ℕ :=
  if h : ∃ c₀, c₀ ∈ crit F ∩ Icc (2 * a) (2 * b) then S.biUnion fun s => win (s * h.choose) R
  else ∅

/-- There are at most |S|·(⌈R⌉ + 1) cutoffs near a crossing. -/
theorem card_near (S : Finset ℝ) (R a b : ℝ) : (near F S R a b).card ≤ S.card * (⌈R⌉₊ + 1) := by
  unfold near
  split_ifs with h
  · calc _ ≤ ∑ s ∈ S, (win (s * h.choose) R).card := Finset.card_biUnion_le
      _ ≤ ∑ s ∈ S, (⌈R⌉₊ + 1) := Finset.sum_le_sum fun s _ => card_win _ _
      _ = S.card * (⌈R⌉₊ + 1) := by rw [Finset.sum_const, smul_eq_mul]
  · simp

/-- A cutoff which is not near a crossing with a critical level is far from all lines. -/
theorem lt_of_not_mem_near {S : Finset ℝ} {R a b : ℝ}
    (h : ∃ c₀, c₀ ∈ crit F ∩ Icc (2 * a) (2 * b)) {k : ℕ} (hk : k ∉ near F S R a b) :
    ∀ s ∈ S, R < |(2 * (k : ℝ) + 2) - s * h.choose| := by
  intro s hs
  by_contra hle
  apply hk
  unfold near
  rw [dite_eq_left h]
  exact Finset.mem_biUnion.mpr ⟨s, hs, mem_win.mpr (not_lt.mp hle)⟩

/-! ### Vanishing of the fixed crossing groups -/

/-- With finitely many prime closed geodesic images, the reflection Borel groups of a single
crossing embed into its ordinary groups in every degree. -/
theorem forget_cross_injective (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit F) (hbc : b ∉ crit F)
    (hsub : (crit F ∩ Icc a b).Subsingleton) (q : ℕ) :
    Function.Injective (forget (crossComplex F hab) q) := by
  cases q with
  | zero => exact Finsler.BorelQuasiIso.forget_zero_injective _
  | succ q => exact Finsler.CrossingW.cross_forget_injective F hn hfin hab ha hac hbc hsub q

/-- A single crossing at the cuts 2a, 2b is a single crossing at the cuts a, b. -/
theorem half_sub {a b : ℝ} (hsub : (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton) :
    (crit F ∩ Icc a b).Subsingleton := by
  intro x hx y hy
  have h := hsub ⟨crit_double F hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
    ⟨crit_double F hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  linarith

/-- **Vanishing of the fixed crossing groups away from the lines.** With finitely many prime
closed geodesic images there is A such that at a single crossing of regular cuts 2a, 2b with
critical level c₀ the reflection Borel groups of the fixed crossing pair vanish in every root
degree l with 2l farther than 2A from all s·c₀ (s a slope of a label or zero). -/
theorem exists_crossR_zero (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, ∀ (a b : ℝ) (hab2 : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
      (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
      ∀ l : ℕ, (∀ s ∈ insert (0 : ℝ) ((labels F hfin).image (slope F)),
        (2 * A : ℝ) < |2 * (l : ℝ) - s * c₀|) → ∀ x : crossR F hab2 l, x = 0 := by
  obtain ⟨A, hA⟩ := exists_single_support F hn hfin
  refine ⟨A, fun a b hab2 ha h2a h2b hsub c₀ hc₀ l hl x => ?_⟩
  have hab : a ≤ b := by linarith
  have hac : a ∉ crit F := fun h => h2a (crit_double F h)
  have hbc : b ∉ crit F := fun h => h2b (crit_double F h)
  have hsub' := half_sub F hsub
  by_contra hx
  have hy0 : (crossDoublingEquiv F hab hab2 l).symm x ≠ 0 := by
    intro h
    apply hx
    rw [← (crossDoublingEquiv F hab hab2 l).apply_symm_apply x, h, map_zero]
  have hz : forget (crossComplex F hab) l ((crossDoublingEquiv F hab hab2 l).symm x) ≠ 0 := by
    intro h
    exact hy0 (forget_cross_injective F hn hfin hab ha hac hbc hsub' l
      (h.trans (map_zero _).symm))
  obtain ⟨c', hc', s, hs, hle⟩ := hA a b hab ha hac hbc hsub' l ⟨_, hz⟩
  have hc2 : 2 * c' = c₀ :=
    hsub ⟨crit_double F hc'.1, by linarith [hc'.2.1], by linarith [hc'.2.2]⟩ hc₀
  have h1 := hl s hs
  have e : 2 * (l : ℝ) - s * c₀ = 2 * ((l : ℝ) - s * c') := by rw [← hc2]; ring
  rw [e, abs_mul, abs_two] at h1
  linarith

/-- Without critical level between the cuts the fixed crossing groups vanish. -/
theorem crossR_zero_regular (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (hab2 : 2 * a ≤ 2 * b) (ha : 0 < a) (hreg : ∀ x ∈ Icc (2 * a) (2 * b), x ∉ crit F) (l : ℕ)
    (x : crossR F hab2 l) : x = 0 := by
  have hab : a ≤ b := by linarith
  have hreg' : ∀ x ∈ Icc a b, x ∉ crit F := fun x hx hc =>
    hreg (2 * x) ⟨by linarith [hx.1], by linarith [hx.2]⟩ (crit_double F hc)
  have hac : a ∉ crit F := hreg' a ⟨le_rfl, hab⟩
  have hbc : b ∉ crit F := hreg' b ⟨hab, le_rfl⟩
  have hsub' : (crit F ∩ Icc a b).Subsingleton := fun x hx => absurd hx.1 (hreg' x hx.2)
  apply (crossDoublingEquiv F hab hab2 l).symm.injective
  apply forget_cross_injective F hn hfin hab ha hac hbc hsub' l
  rw [map_zero, map_zero]
  exact cross_zero_regular F hn ha hab hreg' l _

/-- Without critical level between the cuts the K-Borel crossing groups vanish. -/
theorem crossK_zero_regular (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (hab2 : 2 * a ≤ 2 * b) (ha : 0 < a) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F)
    (hreg : ∀ x ∈ Icc (2 * a) (2 * b), x ∉ crit F) (q : ℕ) (x : crossK F hab2 q) : x = 0 :=
  Finsler.CrossLocalize.crossK_zero_low F hn hfin hab2 ha h2a h2b
    (fun x hx => absurd hx.1 (hreg x hx.2))
    (fun i _ z => cross_zero_regular F hn (by linarith) hab2 hreg i z) x

omit F in
/-- If a graded family vanishes in the degrees l with j' < l ≤ j, the truncations to the degrees
at most j and at most j' have the same image. -/
theorem range_cut_eq (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
    {j' j : ℕ} (hjj : j' ≤ j) (hz : ∀ l, j' < l → l ≤ j → ∀ x : G l, x = 0) :
    LinearMap.range (cut G j) = LinearMap.range (cut G j') := by
  ext x
  rw [mem_range_cut, mem_range_cut]
  constructor
  · intro h l hl
    rcases Nat.lt_or_ge j l with h' | h'
    · exact h l h'
    · exact hz l hl h' _
  · intro h l hl
    exact h l (by omega)

omit F in
/-- If a graded family vanishes in degree j + 1, the truncations to the degrees at most j + 1
and at most j have the same image. -/
theorem range_cut_succ (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
    (j : ℕ) (hz : ∀ x : G (j + 1), x = 0) :
    LinearMap.range (cut G (j + 1)) = LinearMap.range (cut G j) :=
  range_cut_eq G (Nat.le_succ j) fun l h1 h2 => by
    obtain rfl : l = j + 1 := by omega
    exact hz

/-! ### The windowed localization -/

/-- **Windowed localization of single crossings** (not proved here). There are a finite set S of
slopes and a margin D such that for regular cuts 2a ≤ 2b, a > 0, with one critical level c₀
between them, in every degree q farther than D from all s·c₀ (s ∈ S) the total normalized
restriction of the K-Borel crossing group into the reflection Borel groups of the fixed crossing
pair is injective with image the families of root degrees at most q/2. -/
structure WindowLoc where
  /-- the slopes of the lines -/
  S : Finset ℝ
  /-- the margin around the lines -/
  D : ℝ
  loc : ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
    ∀ q : ℕ, (∀ s ∈ S, D < |(q : ℝ) - s * c₀|) →
      Function.Injective (crossEps F hab q) ∧
        LinearMap.range (crossEps F hab q) = LinearMap.range (cut (crossR F hab) (q / 2))

/-- **The local bounds of the events from the windowed localization.** With finitely many prime
closed geodesic images, the windowed localization of single crossings gives the local bounds of
the events: the near cutoffs are those k with 2k + 2 close to a line s·c₀, at most
|S|·(⌈R⌉ + 1) of them, and the far conditions hold at all others. -/
theorem nonempty_eventBounds_of_loc (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (L : WindowLoc F) : Nonempty (EventBounds F) := by
  classical
  obtain ⟨A, hA⟩ := exists_crossR_zero F hn hfin
  set S₀ : Finset ℝ := insert (0 : ℝ) ((labels F hfin).image (slope F)) with hS₀
  set S : Finset ℝ := L.S ∪ S₀ with hS
  set R : ℝ := max (2 * (A : ℝ) + 2) (L.D + 1) with hR
  have hRA : 2 * (A : ℝ) + 2 ≤ R := le_max_left _ _
  have hRD : L.D + 1 ≤ R := le_max_right _ _
  refine nonempty_eventBounds F hn hfin (N := S.card * (⌈R⌉₊ + 1)) (near F S R)
    (fun a b => card_near F S R a b) ?_
  intro a b hab2 ha h2a h2b hsub k hk
  by_cases hc : ∃ c₀, c₀ ∈ crit F ∩ Icc (2 * a) (2 * b)
  · have hfar := lt_of_not_mem_near F hc hk
    have hc₀ : hc.choose ∈ crit F ∩ Icc (2 * a) (2 * b) := hc.choose_spec
    set c₀ := hc.choose with hc₀def
    have hR1 : ∀ x : crossR F hab2 (k + 1), x = 0 :=
      hA a b hab2 ha h2a h2b hsub c₀ hc₀ (k + 1) fun s hs => by
        have h1 := hfar s (Finset.mem_union_right _ hs)
        push_cast
        have e : 2 * ((k : ℝ) + 1) - s * c₀ = (2 * (k : ℝ) + 2) - s * c₀ := by ring
        rw [e]
        linarith
    have hR2 : ∀ x : crossR F hab2 (k + 1 + 1), x = 0 :=
      hA a b hab2 ha h2a h2b hsub c₀ hc₀ (k + 1 + 1) fun s hs => by
        have h1 := hfar s (Finset.mem_union_right _ hs)
        have h2 : |(2 * (k : ℝ) + 2) - s * c₀| ≤ |2 * (((k + 1 + 1 : ℕ) : ℝ)) - s * c₀| + 2 := by
          have e : (2 * (k : ℝ) + 2) - s * c₀ = (2 * (((k + 1 + 1 : ℕ) : ℝ)) - s * c₀) + (-2) := by
            push_cast
            ring
          rw [e]
          calc |(2 * (((k + 1 + 1 : ℕ) : ℝ)) - s * c₀) + (-2)|
              ≤ |2 * (((k + 1 + 1 : ℕ) : ℝ)) - s * c₀| + |(-2 : ℝ)| := abs_add_le _ _
            _ = |2 * (((k + 1 + 1 : ℕ) : ℝ)) - s * c₀| + 2 := by norm_num
        linarith
    have hq : ∀ q : ℕ, (q : ℝ) = 2 * (k : ℝ) + 1 ∨ (q : ℝ) = 2 * (k : ℝ) + 2 ∨
        (q : ℝ) = 2 * (k : ℝ) + 3 → ∀ s ∈ L.S, L.D < |(q : ℝ) - s * c₀| := by
      intro q hq s hs
      have h1 := hfar s (Finset.mem_union_left _ hs)
      have h2 : |(2 * (k : ℝ) + 2) - s * c₀| ≤ |(q : ℝ) - s * c₀| + 1 := by
        have e : (2 * (k : ℝ) + 2) - s * c₀ = ((q : ℝ) - s * c₀) + ((2 * (k : ℝ) + 2) - q) := by
          ring
        rw [e]
        have h3 : |(2 * (k : ℝ) + 2) - (q : ℝ)| ≤ 1 := by
          rcases hq with h | h | h <;> rw [h] <;> norm_num
        linarith [abs_add_le ((q : ℝ) - s * c₀) ((2 * (k : ℝ) + 2) - q)]
      linarith
    obtain ⟨-, hr1⟩ := L.loc a b hab2 ha h2a h2b hsub c₀ hc₀ (2 * k + 1)
      (hq _ (Or.inl (by push_cast; ring)))
    obtain ⟨hi2, hr2⟩ := L.loc a b hab2 ha h2a h2b hsub c₀ hc₀ (2 * k + 1 + 1)
      (hq _ (Or.inr (Or.inl (by push_cast; ring))))
    obtain ⟨hi3, hr3⟩ := L.loc a b hab2 ha h2a h2b hsub c₀ hc₀ (2 * k + 1 + 1 + 1)
      (hq _ (Or.inr (Or.inr (by push_cast; ring))))
    have e1 : (2 * k + 1) / 2 = k := by omega
    have e2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have e3 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
    rw [e1] at hr1
    rw [e2] at hr2
    rw [e3] at hr3
    have hcut := range_cut_succ (crossR F hab2) k hR1
    refine ⟨fun x => hR2 _, ?_, hi2, hr2, hi3, hr3.le⟩
    rw [hcut, hr1]
  · have hreg : ∀ x ∈ Icc (2 * a) (2 * b), x ∉ crit F := fun x hx hx' => hc ⟨x, hx', hx⟩
    have hRz : ∀ l (x : crossR F hab2 l), x = 0 := crossR_zero_regular F hn hfin hab2 ha hreg
    have hKz : ∀ q (x : crossK F hab2 q), x = 0 :=
      crossK_zero_regular F hn hfin hab2 ha h2a h2b hreg
    have hT : Subsingleton ((l : ℕ) → crossR F hab2 l) :=
      ⟨fun x y => funext fun l => (hRz l (x l)).trans (hRz l (y l)).symm⟩
    have hinj : ∀ q, Function.Injective (crossEps F hab2 q) := fun q x y _ =>
      (hKz q x).trans (hKz q y).symm
    refine ⟨fun x => hRz _ _, le_of_eq (Subsingleton.elim _ _), hinj _, Subsingleton.elim _ _,
      hinj _, le_of_eq (Subsingleton.elim _ _)⟩

/-! ### Localization below the lines suffices -/

/-- **Windowed localization below the lines** (not proved here). There is a margin D such that
for regular cuts 2a ≤ 2b, a > 0, with one critical level c₀ between them, in every degree q
farther than D from all lines s·c₀ (s a slope of a label or zero) and below one of them, the
total normalized restriction of the K-Borel crossing group is injective with image the families
of root degrees at most q/2. -/
structure GapLoc (hfin : (primeImages F).Finite) where
  /-- the margin around the lines -/
  D : ℝ
  loc : ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ c₀ ∈ crit F ∩ Icc (2 * a) (2 * b),
    ∀ q : ℕ, (∀ s ∈ insert (0 : ℝ) ((labels F hfin).image (slope F)), D < |(q : ℝ) - s * c₀|) →
    (∃ s ∈ insert (0 : ℝ) ((labels F hfin).image (slope F)), (q : ℝ) < s * c₀) →
      Function.Injective (crossEps F hab q) ∧
        LinearMap.range (crossEps F hab q) = LinearMap.range (cut (crossR F hab) (q / 2))

/-- **The windowed localization from its part below the lines.** Above all lines the ordinary
and reflection Borel groups of the crossing pair and the fixed groups vanish from q on, so
restriction to the fixed crossing is bijective there, and the fixed groups vanish in the root
degrees between q/2 and q. -/
theorem windowLoc_of_gap (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (G : GapLoc F hfin) :
    Nonempty (WindowLoc F) := by
  classical
  obtain ⟨A₁, hA₁⟩ := exists_single_support F hn hfin
  obtain ⟨A₂, hA₂⟩ := exists_crossR_zero F hn hfin
  set S₀ : Finset ℝ := insert (0 : ℝ) ((labels F hfin).image (slope F)) with hS₀
  set D : ℝ := max G.D (max (A₁ : ℝ) (2 * (A₂ : ℝ))) with hD
  have hD₀ : G.D ≤ D := le_max_left _ _
  have hD₁ : (A₁ : ℝ) ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD₂ : 2 * (A₂ : ℝ) ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  have hA0 : (0 : ℝ) ≤ A₂ := Nat.cast_nonneg _
  refine ⟨⟨S₀, D, fun a b hab2 ha h2a h2b hsub c₀ hc₀ q hq => ?_⟩⟩
  by_cases hlow : ∃ s ∈ S₀, (q : ℝ) < s * c₀
  · exact G.loc a b hab2 ha h2a h2b hsub c₀ hc₀ q (fun s hs => lt_of_le_of_lt hD₀ (hq s hs)) hlow
  · push Not at hlow
    have habove : ∀ s ∈ S₀, s * c₀ + D < q := fun s hs => by
      have h1 := hq s hs
      have h2 := hlow s hs
      rw [abs_of_nonneg (by linarith)] at h1
      linarith
    have h0 : 0 < 2 * a := by linarith
    have hX : ∀ i, q ≤ i → ∀ z : HR (crossComplex F hab2) i, z = 0 := by
      intro i hi z
      by_contra hz
      have hz' : forget (crossComplex F hab2) i z ≠ 0 := fun h =>
        hz (forget_cross_injective F hn hfin hab2 h0 h2a h2b hsub i (h.trans (map_zero _).symm))
      obtain ⟨c', hc', s, hs, hle⟩ := hA₁ (2 * a) (2 * b) hab2 h0 h2a h2b hsub i ⟨_, hz'⟩
      have hcc : c' = c₀ := hsub hc' hc₀
      rw [hcc] at hle
      have h3 := habove s hs
      have h4 : (q : ℝ) ≤ i := by exact_mod_cast hi
      have h5 := (abs_le.mp hle).2
      linarith
    have hB : ∀ i, q ≤ i → ∀ z : crossR F hab2 i, z = 0 := by
      intro i hi
      refine hA₂ a b hab2 ha h2a h2b hsub c₀ hc₀ i fun s hs => ?_
      have h3 := habove s hs
      have h4 : (q : ℝ) ≤ i := by exact_mod_cast hi
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      rw [abs_of_nonneg (by linarith)]
      linarith
    obtain ⟨hinj, hrange⟩ :=
      Finsler.CrossLocalize.crossEps_high F hn hfin ha hab2 h2a h2b hX hB q le_rfl
    refine ⟨hinj, hrange.trans (range_cut_eq (crossR F hab2) (Nat.div_le_self q 2)
      fun l hl1 _ => ?_)⟩
    refine hA₂ a b hab2 ha h2a h2b hsub c₀ hc₀ l fun s hs => ?_
    have h3 := habove s hs
    have h4 : (q : ℝ) < 2 * (l : ℝ) := by
      have : q < 2 * l := by omega
      exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The local bounds of the events from the localization below the lines.** -/
theorem nonempty_eventBounds_of_gap (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    (G : GapLoc F hfin) : Nonempty (EventBounds F) := by
  obtain ⟨L⟩ := windowLoc_of_gap F hn hfin G
  exact nonempty_eventBounds_of_loc F hn hfin L

end

end Finsler.EventFar
