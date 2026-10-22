module

public import Finsler.Topology.BorelLens
public import Finsler.Analysis.IntervalH1EnergyZero

/-! Regular intervals and the reduction of E-ZERO to two statements about a descending flow. A
level deformation for a ≤ a' ≤ b is a homotopy of t_b from the identity which does not increase
energy and ends in a map taking t_{a'} into t_a. Such a homotopy keeps every sublevel and the
constant loops. For a' = b it makes the restriction B_b → B_a an isomorphism and the crossing
group of (t_b, t_a) zero; in general it makes restriction from (t_b, t_{a'}) to (t_b, t_a) an
isomorphism. If e acts as zero on the crossing group of tight cuts a' ≤ b' inside a ≤ b, and the
intervals [a, a'] and [b', b] carry level deformations, then e acts as zero on the crossing
group of (t_b, t_a). Consequently, for a set of critical levels such that intervals without
critical levels carry level deformations and tight cuts around each critical level carry
lenses, e acts as zero on the crossing group of any two regular cuts with at most one critical
level between them. The existence of level deformations and lenses is geometric and is not
proved here. -/

@[expose] public section

namespace Finsler.RegularInterval

open CategoryTheory Set Topology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevReverse Finsler.SobolevReflectionAction
open Finsler.BorelDeformation Finsler.AvoidPoint Finsler.BorelLens

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (F : ReversibleMetric n)

/-- A loop of energy at most that of a loop of t_c lies in t_c. -/
theorem mem_lev_of_energy_le {c : ℝ} {u v : SphereLoop n} (h : energy F v ≤ energy F u)
    (hu : u ∈ lev F c) : v ∈ lev F c := by
  rcases hu with hu | hu
  · exact Or.inl (lt_of_le_of_lt (Real.sqrt_le_sqrt h) hu)
  · obtain ⟨x, rfl⟩ := hu
    have h0 : energy F v = 0 :=
      le_antisymm (h.trans (energy_constantSphereLoop F x).le) (energy_nonneg F v)
    obtain ⟨y, rfl⟩ := (energy_eq_zero_iff_constant F v).mp h0
    exact Or.inr ⟨y, rfl⟩

/-- A level deformation: a homotopy of t_b from the identity which does not increase energy and
ends in a map taking t_{a'} into t_a. -/
structure LevelDeformation (F : ReversibleMetric n) (a a' b : ℝ) where
  r : C(lev F b, lev F b)
  H : (ContinuousMap.id (lev F b)).Homotopy r
  energy_le : ∀ (τ : _root_.unitInterval) (x : lev F b),
    energy F (H (τ, x) : SphereLoop n) ≤ energy F (x : SphereLoop n)
  r_mem : ∀ x : lev F b, (x : Loops n) ∈ lev F a' → (r x : Loops n) ∈ lev F a

section Deformations

variable {F} {a a' b : ℝ}

/-- A level deformation keeps every sublevel. -/
theorem keep_lev (D : LevelDeformation F a a' b) (c : ℝ) (τ : _root_.unitInterval) (x : lev F b)
    (hx : (x : Loops n) ∈ lev F c) : (D.H (τ, x) : Loops n) ∈ lev F c :=
  mem_lev_of_energy_le F (D.energy_le τ x) hx

/-- A level deformation keeps the constant loops. -/
theorem keep_consts (D : LevelDeformation F a a' b) (τ : _root_.unitInterval) (x : lev F b)
    (hx : (x : Loops n) ∈ consts n) : (D.H (τ, x) : Loops n) ∈ consts n := by
  obtain ⟨y, hy⟩ := hx
  have h0 : energy F (D.H (τ, x) : SphereLoop n) = 0 := by
    refine le_antisymm ((D.energy_le τ x).trans ?_) (energy_nonneg F _)
    rw [← hy]
    exact (energy_constantSphereLoop F y).le
  obtain ⟨z, hz⟩ := (energy_eq_zero_iff_constant F _).mp h0
  exact ⟨z, hz.symm⟩

/-- For a' = b: a deformation of t_b into t_a keeping t_c and t_a. -/
def toDeformation (D : LevelDeformation F a b b) (c : ℝ) :
    Deformation (lev F c) (lev F a) (lev F b) where
  r := D.r
  H := D.H
  r_mem x := D.r_mem x x.2
  keep_s τ x hx := keep_lev D c τ x hx
  keep_t τ x hx := keep_lev D a τ x hx

/-- For a' = b: a deformation of t_b into t_a keeping the constant loops and t_a. -/
def toDeformationConsts (D : LevelDeformation F a b b) :
    Deformation (consts n) (lev F a) (lev F b) where
  r := D.r
  H := D.H
  r_mem x := D.r_mem x x.2
  keep_s τ x hx := keep_consts D τ x hx
  keep_t τ x hx := keep_lev D a τ x hx

/-- A deformation of the pair (t_b, t_{a'}) into the pair (t_b, t_a). -/
def toPairDeformation (D : LevelDeformation F a a' b) :
    PairDeformation (lev F a) (lev F b) (lev F a') (lev F b) where
  r := D.r
  H := D.H
  r_mem x := (D.r x).2
  r_sub x hx := D.r_mem x hx
  keep_sub' τ x hx := keep_lev D a' τ x hx
  keep τ x _ := (D.H (τ, x)).2
  keep_sub τ x hx := keep_lev D a τ x hx

end Deformations

/-- If the restriction B_b → B_a is an isomorphism in all degrees, the reflection Borel
cohomology of the crossing pair (t_b, t_a) is zero. -/
theorem crossing_eq_zero_of_cut_bijective {a b : ℝ} (hab : a ≤ b)
    (hbij : ∀ q, Function.Bijective (HRmap (cutHom F hab) q)) (q : ℕ)
    (z : HR (crossComplex F hab) q) : z = 0 := by
  have hrel : HRmap (relHom F hab) q z = 0 := by
    apply (hbij q).1
    rw [crossing_cut_zero, map_zero]
  cases q with
  | zero =>
    apply BorelExact.injective_zero (BorelCrossing.shortExact F hab)
    rw [hrel, map_zero]
  | succ k =>
    obtain ⟨x, rfl⟩ := exact_crossing_sub F hab k z hrel
    obtain ⟨y, rfl⟩ := (hbij k).2 x
    exact crossDelta_cut F hab k y

/-- On an interval carrying a level deformation the restriction B_b → B_a is an isomorphism. -/
theorem cut_bijective_of_levelDeformation {a b : ℝ} (hab : a ≤ b)
    (D : LevelDeformation F a b b) (q : ℕ) : Function.Bijective (HRmap (cutHom F hab) q) :=
  BorelDeformation.cut_bijective F hab (toDeformationConsts D) q

/-- On an interval carrying a level deformation the crossing group is zero. -/
theorem crossing_eq_zero {a b : ℝ} (hab : a ≤ b) (D : LevelDeformation F a b b) (q : ℕ)
    (z : HR (crossComplex F hab) q) : z = 0 :=
  crossing_eq_zero_of_cut_bijective F hab
    (fun k => cut_bijective_of_levelDeformation F hab D k) q z

/-- From tight cuts to wide cuts. Let a ≤ a' ≤ b' ≤ b. If [a, a'] carries a level deformation
of t_{b'}, [b', b] carries a level deformation, and e acts as zero on the crossing group of
(t_{b'}, t_{a'}), then e acts as zero on the crossing group of (t_b, t_a). -/
theorem crossE_zero_of_tight {a a' b' b : ℝ} (haa : a ≤ a') (hab' : a' ≤ b') (hbb : b' ≤ b)
    (hn : 1 ≤ n) (D₁ : LevelDeformation F a a' b') (D₂ : LevelDeformation F b' b b) (q : ℕ)
    (htight : ∀ z' : HR (crossComplex F hab') q, crossE F hab' hn q z' = 0)
    (z : HR (crossComplex F (haa.trans (hab'.trans hbb))) q) :
    crossE F (haa.trans (hab'.trans hbb)) hn q z = 0 := by
  have hst : lev F a ⊆ lev F b' := lev_mono F (haa.trans hab')
  have hs : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have ht : ∀ u : SphereLoop n, u ∈ lev F b' → reverseSphere u ∈ lev F b' :=
    fun _ hu => reverse_mem_lev F hu
  -- restriction from (t_b, t_a) to (t_{b'}, t_a)
  have h1 := BorelInvariance.bijective_HRmap (revSub_sq hst hs ht)
    (revCross_sq F (haa.trans (hab'.trans hbb)))
    (toCross hst F (haa.trans (hab'.trans hbb)) subset_rfl (lev_mono F hbb))
    (toCross_equivariant hst hs ht F (haa.trans (hab'.trans hbb)) subset_rfl (lev_mono F hbb))
    (fun k => bijective_nativePull hst (lev_mono F hbb) (toDeformation D₂ a) k)
  -- restriction from (t_{b'}, t_{a'}) to (t_{b'}, t_a)
  have h2 := BorelInvariance.bijective_HRmap (revSub_sq hst hs ht) (revCross_sq F hab')
    (toCross hst F hab' (lev_mono F haa) subset_rfl)
    (toCross_equivariant hst hs ht F hab' (lev_mono F haa) subset_rfl)
    (fun k => bijective_nativePull_inclPair hst (lev_mono F hab') (lev_mono F haa) subset_rfl
      (toPairDeformation D₁) k)
  obtain ⟨z', hz'⟩ := (h2 q).2
    (HRmap (toCrossHom hst hs ht F (haa.trans (hab'.trans hbb)) subset_rfl (lev_mono F hbb)) q z)
  apply (h1 (n + q)).1
  rw [crossE_toCross, ← hz', ← crossE_toCross, htight, map_zero, map_zero]

/-- E-ZERO from level deformations and lenses. Let crit be a set of levels such that every
interval [a, a'] without points of crit carries level deformations of every t_b with a' ≤ b,
and such that tight cuts around each point of crit carry lenses for a point p. Then for regular
cuts 0 < a ≤ b with at most one point of crit between them, e acts as zero on the reflection
Borel cohomology of the crossing pair (t_b, t_a). -/
theorem crossE_zero_of_flow (hn : 1 ≤ n) (p : Sphere n) (crit : Set ℝ)
    (hreg : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
      Nonempty (LevelDeformation F a a' b))
    (hlens : ∀ c ∈ crit, ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε →
      Nonempty (Lens F a b p))
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit) (hbc : b ∉ crit)
    (hsub : (crit ∩ Icc a b).Subsingleton) (q : ℕ) (z : HR (crossComplex F hab) q) :
    crossE F hab hn q z = 0 := by
  by_cases hne : (crit ∩ Icc a b).Nonempty
  · obtain ⟨c, hc, hcab⟩ := hne
    have hac' : a < c := lt_of_le_of_ne hcab.1 (fun h => hac (h ▸ hc))
    have hcb' : c < b := lt_of_le_of_ne hcab.2 (fun h => hbc (h ▸ hc))
    obtain ⟨ε, hε, hL⟩ := hlens c hc
    -- tight cuts a' and b'
    obtain ⟨a', ha'1, ha'2⟩ := exists_between (max_lt hac' (sub_lt_self c hε))
    obtain ⟨b', hb'1, hb'2⟩ := exists_between (lt_min hcb' (lt_add_of_pos_right c hε))
    have haa : a ≤ a' := (le_max_left _ _).trans ha'1.le
    have hbb : b' ≤ b := hb'2.le.trans (min_le_left _ _)
    have hab' : a' ≤ b' := (ha'2.trans hb'1).le
    have hreg₁ : ∀ x ∈ Icc a a', x ∉ crit := by
      intro x hx hxc
      have hxe : x = c := hsub ⟨hxc, hx.1, hx.2.trans (ha'2.le.trans hcb'.le)⟩ ⟨hc, hcab⟩
      rw [hxe] at hx
      exact absurd hx.2 (not_le.mpr ha'2)
    have hreg₂ : ∀ x ∈ Icc b' b, x ∉ crit := by
      intro x hx hxc
      have hxe : x = c := hsub ⟨hxc, (hac'.le.trans hb'1.le).trans hx.1, hx.2⟩ ⟨hc, hcab⟩
      rw [hxe] at hx
      exact absurd hx.1 (not_le.mpr hb'1)
    obtain ⟨D₁⟩ := hreg a a' b' ha haa hab' hreg₁
    obtain ⟨D₂⟩ := hreg b' b b (ha.trans_le (haa.trans hab')) hbb le_rfl hreg₂
    obtain ⟨L⟩ := hL a' b' ((le_max_right _ _).trans_lt ha'1) ha'2 hb'1
      (hb'2.trans_le (min_le_right _ _))
    exact crossE_zero_of_tight F haa hab' hbb hn D₁ D₂ q
      (fun z' => crossE_zero_of_lens F hab' hn p L q z') z
  · have hreg₀ : ∀ x ∈ Icc a b, x ∉ crit := fun x hx hxc => hne ⟨x, hxc, hx⟩
    obtain ⟨D⟩ := hreg a b b ha hab le_rfl hreg₀
    rw [crossing_eq_zero F hab D q z, map_zero]

end

end Finsler.RegularInterval
