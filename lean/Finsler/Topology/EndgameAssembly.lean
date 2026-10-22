module

public import Finsler.Topology.Endgame
public import Finsler.Algebra.MaximalCut
public import Finsler.Algebra.Progression
public import Finsler.Topology.Detection

/-! The last section of the argument from lemma-level inputs, with actual groups. `Core` and
`Inputs` list what the geometric stages must prove for a metric with finitely many prime closed
geodesic images: a locally finite set of critical levels closed under doubling; a defect T which is
bounded and constant between critical levels; at every regular cut a doubling rank budget
relating T at the cut and at half the cut; the detection band of the global reflection Borel
classes; nonzero odd bottom classes in degrees (4t + 1)(n − 1) whose labels have bottom indicator
one when visible and partner indicator zero when the e-multiple vanishes; and (the field of
`Inputs` beyond `Core`) vanishing of e on crossing groups between regular cuts enclosing at most
one critical level. From these inputs the
file derives a contradiction: T attains its maximum near a regular cut, doubling keeps the
maximum on all doublings of a neighbourhood, a doubling of the neighbourhood contains the
detection window of an odd bottom class, the class is zero at the lower end and nonzero at the
upper end, and at the first crossing where it appears the equality case of the doubling budget
fails. None of the inputs is proved here. -/

@[expose] public section

namespace Finsler.EndgameAssembly

open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelCrossing
open Set

noncomputable section

variable {n : ℕ}

/-- The lemma-level inputs of the final section for one reversible metric, except for the
vanishing of e on single crossings. -/
structure Core (F : ReversibleMetric n) (hn : 1 ≤ n) where
  /-- critical levels -/
  crit : Set ℝ
  crit_finite : ∀ a b : ℝ, (crit ∩ Icc a b).Finite
  crit_double : ∀ x, x ∈ crit → 2 * x ∈ crit
  /-- total defect at a cut -/
  T : ℝ → ℕ
  bound : ℕ
  T_le : ∀ a, 0 < a → a ∉ crit → T a ≤ bound
  T_const : ∀ a b, 0 < a → a ≤ b → (∀ x ∈ Icc a b, x ∉ crit) → T a = T b
  /-- labels of the doubling formula -/
  ι : Type
  budget : ℝ → Finsler.PartnerRank.Data ι
  budget_T : ∀ x, 0 < x → x ∉ crit → (budget x).T = (T (x / 2) : ℤ)
  budget_Tdouble : ∀ x, 0 < x → x ∉ crit → (budget x).Tdouble = (T x : ℤ)
  /-- detection band -/
  α : ℝ
  α_pos : 0 < α
  C : ℝ
  q₀ : ℕ
  det_inj : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → (q : ℝ) < α * a - C →
    Function.Injective (HRmap (resHom F a) q)
  det_zero : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → α * a + C < (q : ℝ) →
    ∀ x, HRmap (resHom F a) q x = 0
  /-- odd bottom classes -/
  bottom : ∀ t : ℕ, HR (fullComplex n) ((4 * t + 1) * (n - 1))
  bottom_ne : ∀ t, bottom t ≠ 0
  label : ℕ → ι
  label_mem : ∀ t x, 0 < x → x ∉ crit → HRmap (resHom F x) _ (bottom t) ≠ 0 →
    label t ∈ (budget x).labels
  label_bottom : ∀ t x, 0 < x → x ∉ crit → HRmap (resHom F x) _ (bottom t) ≠ 0 →
    (budget x).bottom (label t) = 1
  label_partner : ∀ t x, 0 < x → x ∉ crit →
    BorelCanonicalEvaluation.levE F x hn _ (HRmap (resHom F x) _ (bottom t)) = 0 →
    (budget x).partner (label t) ≤ 0

/-- The lemma-level inputs of the final section for one reversible metric. -/
structure Inputs (F : ReversibleMetric n) (hn : 1 ≤ n) extends Core F hn where
  /-- vanishing of e on single crossings -/
  e_zero : ∀ (a b : ℝ) (hab : a ≤ b), 0 < a → a ∉ crit → b ∉ crit →
    (crit ∩ Icc a b).Subsingleton →
    ∀ (q : ℕ) (z : HR (crossComplex F hab) q), crossE F hab hn q z = 0

variable {F : ReversibleMetric n} {hn : 1 ≤ n} (I : Inputs F hn)

/-- Every nonempty open interval contains a noncritical level. -/
theorem exists_regular_between {p r : ℝ} (hpr : p < r) : ∃ y, p < y ∧ y < r ∧ y ∉ I.crit := by
  obtain ⟨y, hy, hny⟩ := ((Ioo_infinite hpr).sdiff (I.crit_finite p r)).nonempty
  exact ⟨y, hy.1, hy.2, fun hc => hny ⟨hc, Ioo_subset_Icc_self hy⟩⟩

/-- Half of a noncritical level is noncritical. -/
theorem half_notMem {x : ℝ} (hx : x ∉ I.crit) : x / 2 ∉ I.crit := by
  intro h
  apply hx
  have h2 := I.crit_double (x / 2) h
  have he : 2 * (x / 2) = x := by ring
  rwa [he] at h2

/-- Restriction to a smaller cut factors through a larger one. -/
theorem cut_res {a b : ℝ} (hab : a ≤ b) (q : ℕ) (y : HR (fullComplex n) q) :
    HRmap (cutHom F hab) q (HRmap (resHom F b) q y) = HRmap (resHom F a) q y := by
  rw [← HRmap_comp]
  exact HRmap_congr (cut_res_f F hab) q y

/-- One crossing on a doubling plateau: an odd bottom class which is zero at the lower regular cut
is zero at the upper regular cut. -/
theorem step (t : ℕ) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ I.crit) (hbc : b ∉ I.crit)
    (htight : (I.crit ∩ Icc a b).Subsingleton) (hplateau : I.T b = I.T (b / 2))
    (hzero : HRmap (resHom F a) _ (I.bottom t) = 0) :
    HRmap (resHom F b) _ (I.bottom t) = 0 := by
  by_contra hne
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hcut : HRmap (cutHom F hab) _ (HRmap (resHom F b) _ (I.bottom t)) = 0 :=
    (cut_res hab _ (I.bottom t)).trans hzero
  obtain ⟨z, hz⟩ := exact_crossing F hab _ _ hcut
  have he : BorelCanonicalEvaluation.levE F b hn _ (HRmap (resHom F b) _ (I.bottom t)) = 0 := by
    rw [← hz, ← crossE_rel, I.e_zero a b hab ha hac hbc htight, map_zero]
  have hmem := I.label_mem t b hb hbc hne
  have hbot := I.label_bottom t b hb hbc hne
  have hpart := I.label_partner t b hb hbc he
  have heq : (I.budget b).Tdouble = (I.budget b).T := by
    rw [I.budget_T b hb hbc, I.budget_Tdouble b hb hbc, hplateau]
  have hforce := Finsler.PartnerRank.equality_forces_partner (I.budget b) heq (I.label t) hmem
  rw [hforce, hbot] at hpart
  norm_num at hpart

/-- Finitely many crossings on a doubling plateau: induction on the number of critical levels
between the cuts, splitting at a noncritical level between two of them. -/
theorem many (t : ℕ) (lo hi : ℝ)
    (hplateau : ∀ x, x ∉ I.crit → lo ≤ x → x ≤ hi → I.T x = I.T (x / 2)) :
    ∀ (N : ℕ) (a b : ℝ), a ≤ b → 0 < a → a ∉ I.crit → b ∉ I.crit → lo ≤ a → b ≤ hi →
      (I.crit ∩ Icc a b).ncard ≤ N → HRmap (resHom F a) _ (I.bottom t) = 0 →
      HRmap (resHom F b) _ (I.bottom t) = 0 := by
  intro N
  induction N with
  | zero =>
    intro a b hab ha hac hbc hlo hhi hN hzero
    have hempty : I.crit ∩ Icc a b = ∅ :=
      (ncard_eq_zero (I.crit_finite a b)).mp (Nat.le_zero.mp hN)
    refine step I t hab ha hac hbc ?_ (hplateau b hbc (hlo.trans hab) hhi) hzero
    rw [hempty]
    exact subsingleton_empty
  | succ N ih =>
    intro a b hab ha hac hbc hlo hhi hN hzero
    by_cases hsub : (I.crit ∩ Icc a b).Subsingleton
    · exact step I t hab ha hac hbc hsub (hplateau b hbc (hlo.trans hab) hhi) hzero
    · obtain ⟨y, hy, y', hy', hlt⟩ := (not_subsingleton_iff.mp hsub).exists_lt
      obtain ⟨z, hyz, hzy', hzc⟩ := exists_regular_between I hlt
      have haz : a ≤ z := hy.2.1.trans hyz.le
      have hzb : z ≤ b := hzy'.le.trans hy'.2.2
      have hz0 : 0 < z := lt_of_lt_of_le ha haz
      have h1 : (I.crit ∩ Icc a z).ncard ≤ N := by
        have hss : I.crit ∩ Icc a z ⊂ I.crit ∩ Icc a b := by
          refine ⟨fun x hx => ⟨hx.1, hx.2.1, hx.2.2.trans hzb⟩, fun hsup => ?_⟩
          have := hsup hy'
          exact absurd this.2.2 (not_le.mpr hzy')
        have := ncard_lt_ncard hss (I.crit_finite a b)
        omega
      have h2 : (I.crit ∩ Icc z b).ncard ≤ N := by
        have hss : I.crit ∩ Icc z b ⊂ I.crit ∩ Icc a b := by
          refine ⟨fun x hx => ⟨hx.1, haz.trans hx.2.1, hx.2.2⟩, fun hsup => ?_⟩
          have := hsup hy
          exact absurd this.2.1 (not_le.mpr hyz)
        have := ncard_lt_ncard hss (I.crit_finite a b)
        omega
      have hmid := ih a z haz ha hac hzc hlo (hzb.trans hhi) h1 hzero
      exact ih z b hzb hz0 hzc hbc (hlo.trans haz) hhi h2 hmid

/-- The inputs of the final section are contradictory. -/
theorem false_of_inputs (h2 : 2 ≤ n) (I : Inputs F hn) : False := by
  -- a regular cut where the defect is maximal
  obtain ⟨a₁, ha₁, _, ha₁c⟩ := exists_regular_between I (one_lt_two (α := ℝ))
  let Reg := {x : ℝ // 0 < x ∧ x ∉ I.crit}
  have hne : Nonempty Reg := ⟨⟨a₁, by linarith, ha₁c⟩⟩
  obtain ⟨a₀, hmax⟩ := Finsler.MaximalCut.exists_maximizer (fun x : Reg => I.T x.1) I.bound
    (fun x => I.T_le x.1 x.2.1 x.2.2)
  have ha₀ : 0 < a₀.1 := a₀.2.1
  have ha₀c : a₀.1 ∉ I.crit := a₀.2.2
  -- a closed interval around it without critical levels
  have hclosed : IsClosed (I.crit ∩ Icc (a₀.1 / 2) (2 * a₀.1)) := (I.crit_finite _ _).isClosed
  have hmem : a₀.1 ∈ (I.crit ∩ Icc (a₀.1 / 2) (2 * a₀.1))ᶜ := fun h => ha₀c h.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl a₀.1 hmem
  let δ := min (ε / 2) (a₀.1 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδa : δ ≤ a₀.1 / 4 := min_le_right _ _
  let u := a₀.1 - δ
  let v := a₀.1 + δ
  have hu : 0 < u := by change 0 < a₀.1 - δ; linarith
  have huv : u < v := by change a₀.1 - δ < a₀.1 + δ; linarith
  have hfree : ∀ y ∈ Icc u v, y ∉ I.crit := by
    intro y hy hc
    have hy1 : a₀.1 - δ ≤ y := hy.1
    have hy2 : y ≤ a₀.1 + δ := hy.2
    have hyball : y ∈ Metric.ball a₀.1 ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact hball hyball ⟨hc, by constructor <;> linarith⟩
  have hconst : ∀ y ∈ Icc u v, I.T y = I.T a₀.1 := by
    intro y hy
    have hy1 : a₀.1 - δ ≤ y := hy.1
    have hy2 : y ≤ a₀.1 + δ := hy.2
    rcases le_total y a₀.1 with hle | hle
    · exact I.T_const y a₀.1 (by linarith) hle
        (fun x hx => hfree x ⟨hy.1.trans hx.1, hx.2.trans (by change a₀.1 ≤ a₀.1 + δ; linarith)⟩)
    · exact (I.T_const a₀.1 y ha₀ hle
        (fun x hx => hfree x ⟨(by change a₀.1 - δ ≤ a₀.1; linarith : u ≤ a₀.1).trans hx.1,
          hx.2.trans hy.2⟩)).symm
  -- doubling keeps the maximum
  have hpl : ∀ (k : ℕ) (x : ℝ), x ∉ I.crit → x / 2 ^ k ∈ Icc u v → I.T x = I.T a₀.1 := by
    intro k
    induction k with
    | zero =>
      intro x _ hx
      rw [pow_zero, div_one] at hx
      exact hconst x hx
    | succ k ih =>
      intro x hxc hx
      have he : x / 2 ^ (k + 1) = x / 2 / 2 ^ k := by rw [pow_succ]; field_simp
      have hx0 : 0 < x := by
        have h1 : 0 < x / 2 ^ (k + 1) := lt_of_lt_of_le hu hx.1
        have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
        exact (div_pos_iff_of_pos_right h2).mp h1
      have hhalf : I.T (x / 2) = I.T a₀.1 := ih (x / 2) (half_notMem I hxc) (he ▸ hx)
      have hmono := Finsler.PartnerRank.doubling_monotone (I.budget x)
      rw [I.budget_T x hx0 hxc, I.budget_Tdouble x hx0 hxc] at hmono
      have hmono' : I.T (x / 2) ≤ I.T x := by exact_mod_cast hmono
      have hle : I.T x ≤ I.T a₀.1 := hmax ⟨x, hx0, hxc⟩
      omega
  -- the detection window of an odd bottom class inside a doubling of the interval
  have hd : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
    linarith
  obtain ⟨k, t, hk, hthr, hlow, hhigh⟩ := Finsler.Progression.exists_odd_degree I.α u v I.C
    ((n : ℝ) - 1) (I.q₀ : ℝ) I.α_pos hu huv hd
  have hcast : (((4 * t + 1) * (n - 1) : ℕ) : ℝ) = (4 * (t : ℝ) + 1) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have hq₀ : I.q₀ ≤ (4 * t + 1) * (n - 1) := by
    have : (I.q₀ : ℝ) < (((4 * t + 1) * (n - 1) : ℕ) : ℝ) := by rw [hcast]; exact hthr
    exact le_of_lt (by exact_mod_cast this)
  have hP : (0 : ℝ) < 2 ^ k := by positivity
  have hαP : 0 < I.α := I.α_pos
  -- lower cut: the class is zero
  have hx1ex : (2 : ℝ) ^ k * u < min ((((4 * t + 1) * (n - 1) : ℕ) - I.C) / I.α) (2 ^ k * v) := by
    refine lt_min ?_ (by nlinarith)
    rw [lt_div_iff₀ hαP, hcast]
    nlinarith
  obtain ⟨x1, hx1l, hx1r, hx1c⟩ := exists_regular_between I hx1ex
  have hx1pos : 0 < x1 := lt_trans (by positivity) hx1l
  have hx1a : I.α * x1 + I.C < (((4 * t + 1) * (n - 1) : ℕ) : ℝ) := by
    have := (lt_div_iff₀ hαP).mp (lt_of_lt_of_le hx1r (min_le_left _ _))
    linarith
  have hx1v : x1 < 2 ^ k * v := lt_of_lt_of_le hx1r (min_le_right _ _)
  -- upper cut: the class is nonzero
  have hx2ex : max ((((4 * t + 1) * (n - 1) : ℕ) + I.C) / I.α) x1 < 2 ^ k * v := by
    refine max_lt ?_ hx1v
    rw [div_lt_iff₀ hαP, hcast]
    nlinarith
  obtain ⟨x2, hx2l, hx2r, hx2c⟩ := exists_regular_between I hx2ex
  have hx12 : x1 < x2 := lt_of_le_of_lt (le_max_right _ _) hx2l
  have hx2pos : 0 < x2 := lt_trans hx1pos hx12
  have hx2a : (((4 * t + 1) * (n - 1) : ℕ) : ℝ) < I.α * x2 - I.C := by
    have := (div_lt_iff₀ hαP).mp (lt_of_le_of_lt (le_max_left _ _) hx2l)
    linarith
  have hzero : HRmap (resHom F x1) _ (I.bottom t) = 0 :=
    I.det_zero _ x1 hq₀ hx1pos hx1a (I.bottom t)
  have hnonzero : HRmap (resHom F x2) _ (I.bottom t) ≠ 0 := by
    intro h0
    exact I.bottom_ne t (I.det_inj _ x2 hq₀ hx2pos hx2a (h0.trans (map_zero _).symm))
  -- the plateau between the two cuts
  have hplateau : ∀ x, x ∉ I.crit → x1 ≤ x → x ≤ x2 → I.T x = I.T (x / 2) := by
    intro x hxc hx1 hx2
    have hin : x / 2 ^ k ∈ Icc u v := by
      constructor
      · rw [le_div_iff₀ hP]
        nlinarith
      · rw [div_le_iff₀ hP]
        nlinarith
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have he : x / 2 ^ (j + 1) = x / 2 / 2 ^ j := by rw [pow_succ]; field_simp
    rw [hpl (j + 1) x hxc hin, hpl j (x / 2) (half_notMem I hxc) (he ▸ hin)]
  exact hnonzero (many I t x1 x2 hplateau _ x1 x2 hx12.le hx1pos hx1c hx2c le_rfl le_rfl le_rfl
    hzero)

/-- If finiteness of the prime closed geodesic images yields the lemma-level inputs, there are
infinitely many prime closed geodesic images. -/
theorem infinite_of_inputs (F : ReversibleMetric n) (h2 : 2 ≤ n)
    (h : (primeImages F).Finite → Nonempty (Inputs F (le_trans (by norm_num) h2))) :
    (primeImages F).Infinite := by
  intro hfin
  obtain ⟨I⟩ := h hfin
  exact false_of_inputs h2 I

/-- Reduction of the candidate main assertion to the lemma-level inputs. -/
theorem assertion_of_inputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (Inputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  fun n h3 F => infinite_of_inputs F (le_trans (by norm_num) h3) (h n h3 F)

/-- The detection band for the actual reflection Borel groups of the Finsler sublevels, from the
three inputs of the abstract detection theorem: stabilization of the ordinary image after a
shift D, the ordinary resonance bands, and nilpotence of w on the global groups. With N + 1 = n
this is the detection input of `Inputs` with threshold 2n + 1 and margin C + α(n − 1)D. -/
theorem detection_actual (F : ReversibleMetric n) (α D C : ℝ) (hD : 0 ≤ D) (N : ℕ)
    (image : ∀ a b (hgap : a + D ≤ b), ∀ q (z : H (levComplex F b) q),
      ∃ zGlobal : H (fullComplex n) q,
        Hmap (resHom F a) q zGlobal = Hmap (cutHom F (by linarith : a ≤ b)) q z)
    (ordinary_inj : ∀ c q, N + 3 ≤ q → (q : ℝ) < α * c - C →
      Function.Injective (Hmap (resHom F c) q))
    (ordinary_zero : ∀ c q, N + 3 ≤ q → α * c + C < (q : ℝ) → ∀ z, Hmap (resHom F c) q z = 0)
    (nilpotent : ∀ lo (x : HR (fullComplex n) lo),
      Finsler.Gysin.word (V := fun i => HR (fullComplex n) (lo + i))
        (fun i => (w (fullComplex n) (lo + i)).toAddMonoidHom) (N + 1) x = 0) :
    (∀ (q : ℕ) (a : ℝ), 2 * (N + 1) + 1 ≤ q → (q : ℝ) < α * a - (C + α * (N : ℝ) * D) →
      Function.Injective (HRmap (resHom F a) q)) ∧
    (∀ (q : ℕ) (a : ℝ), 2 * (N + 1) + 1 ≤ q → α * a + (C + α * (N : ℝ) * D) < (q : ℝ) →
      ∀ x, HRmap (resHom F a) q x = 0) :=
  ⟨fun q a hq hlt => Finsler.FilteredGysin.detection_injective (gysinData F) α D C a hD N q
      image ordinary_inj nilpotent hq hlt,
    fun q a hq hlt => Finsler.FilteredGysin.detection_zero (gysinData F) α D C a hD N q
      image ordinary_zero nilpotent hq hlt⟩

end

end Finsler.EndgameAssembly
