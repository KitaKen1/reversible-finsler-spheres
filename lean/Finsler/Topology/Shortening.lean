module

public import Finsler.Topology.RegularInterval

/-! Shortenings of sublevels. A shortening of t_b is a map D of t_b commuting with reversal,
with a homotopy from the identity along which energy does not increase; the homotopy need not
commute with reversal, and D need not be the time-one map of a flow (a discrete curve
shortening process is the intended example). The iterates of D are homotopic to the identity
through energy-nonincreasing homotopies. If some iterate takes t_{a'} into t_a, the shortening
gives a level deformation for a ≤ a' ≤ b. If the loops x of t_b with √E(D x) > a' avoid a point,
then for a' < a ≤ b with a > 0 the sets Y = {√E ∘ D < a} and N = {√E ∘ D > a'} form a lens for
(a, b). Hence, for a set of positive critical levels, shortenings with a descent property on
intervals without critical levels and shortenings with a localization property at tight cuts
around critical levels give the level deformations and lenses of the flow inputs. The
existence of shortenings with these two properties is geometric and is not proved here. -/

@[expose] public section

namespace Finsler.Shortening

open Set Topology
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevReverse Finsler.SobolevReflectionAction
open Finsler.BorelDeformation Finsler.AvoidPoint Finsler.BorelLens Finsler.RegularInterval

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- A shortening of the sublevel t_b: a map of t_b commuting with reversal, with a homotopy
from the identity along which energy does not increase. -/
structure Data (F : ReversibleMetric n) (b : ℝ) where
  D : C(lev F b, lev F b)
  G : (ContinuousMap.id (lev F b)).Homotopy D
  energy_le : ∀ (τ : _root_.unitInterval) (x : lev F b),
    energy F (G (τ, x) : SphereLoop n) ≤ energy F (x : SphereLoop n)
  rev : ∀ x : lev F b,
    (D ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : Loops n) =
      reverseSphere (D x : SphereLoop n)

variable {F : ReversibleMetric n} {b : ℝ} (S : Data F b)

/-- A shortening does not increase energy. -/
theorem energy_D_le (x : lev F b) :
    energy F (S.D x : SphereLoop n) ≤ energy F (x : SphereLoop n) := by
  have h := S.energy_le 1 x
  rwa [S.G.apply_one] at h

/-- The iterates of a shortening. -/
def iter : ℕ → C(lev F b, lev F b)
  | 0 => ContinuousMap.id _
  | k + 1 => S.D.comp (iter k)

theorem energy_iter_le (k : ℕ) (x : lev F b) :
    energy F (iter S k x : SphereLoop n) ≤ energy F (x : SphereLoop n) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (energy_D_le S (iter S k x)).trans ih

/-- The homotopy from the k-th iterate to the next one. -/
def stepHomotopy (k : ℕ) : (iter S k).Homotopy (iter S (k + 1)) where
  toFun p := S.G (p.1, iter S k p.2)
  continuous_toFun :=
    S.G.continuous.comp (continuous_fst.prodMk ((iter S k).continuous.comp continuous_snd))
  map_zero_left x := S.G.apply_zero (iter S k x)
  map_one_left x := S.G.apply_one (iter S k x)

/-- The homotopy from the identity to the k-th iterate. -/
def iterHomotopy : (k : ℕ) → (ContinuousMap.id (lev F b)).Homotopy (iter S k)
  | 0 => ContinuousMap.Homotopy.refl _
  | k + 1 => (iterHomotopy k).trans (stepHomotopy S k)

/-- Energy does not increase along the homotopy to an iterate. -/
theorem energy_iterHomotopy_le (k : ℕ) (τ : _root_.unitInterval) (x : lev F b) :
    energy F (iterHomotopy S k (τ, x) : SphereLoop n) ≤ energy F (x : SphereLoop n) := by
  induction k generalizing τ with
  | zero => exact le_rfl
  | succ k ih =>
    change energy F (((iterHomotopy S k).trans (stepHomotopy S k)) (τ, x) : SphereLoop n) ≤ _
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with h
    · exact ih _
    · exact (S.energy_le _ (iter S k x)).trans (energy_iter_le S k x)

/-- If the k-th iterate of a shortening takes t_{a'} into t_a, the shortening gives a level
deformation. -/
def levelDeformation {a a' : ℝ} (k : ℕ)
    (hk : ∀ x : lev F b, (x : Loops n) ∈ lev F a' → (iter S k x : Loops n) ∈ lev F a) :
    LevelDeformation F a a' b where
  r := iter S k
  H := iterHomotopy S k
  energy_le := energy_iterHomotopy_le S k
  r_mem := hk

/-- The square root of the energy after one shortening step is continuous on t_b. -/
theorem continuous_sqrt_energy_D :
    Continuous fun x : lev F b => Real.sqrt (energy F (S.D x : SphereLoop n)) :=
  (Finsler.SobolevEnergy.sqrt_energy_continuous F).comp
    (continuous_subtype_val.comp S.D.continuous)

/-- The lens of a shortening: for a' < a ≤ b with a > 0, if the loops x of t_b with
√E(D x) > a' avoid the point p, then Y = {√E ∘ D < a} and N = {√E ∘ D > a'} form a lens. -/
def lens {a a' : ℝ} (p : Sphere n) (ha : 0 < a) (ha' : a' < a) (hab : a ≤ b)
    (hloc : ∀ x : lev F b, a' < Real.sqrt (energy F (S.D x : SphereLoop n)) →
      (x : Loops n) ∈ avoid p) : Lens F a b p where
  Y := Subtype.val '' {x : lev F b | Real.sqrt (energy F (S.D x : SphereLoop n)) < a}
  N := Subtype.val '' {x : lev F b | a' < Real.sqrt (energy F (S.D x : SphereLoop n))}
  Y_open := (lev_isOpen F (ha.trans_le hab)).isOpenMap_subtype_val _
    (isOpen_lt (continuous_sqrt_energy_D S) continuous_const)
  N_open := (lev_isOpen F (ha.trans_le hab)).isOpenMap_subtype_val _
    (isOpen_lt continuous_const (continuous_sqrt_energy_D S))
  Y_rev := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
    change Real.sqrt (energy F (S.D ⟨reverseSphere (x : SphereLoop n),
      reverse_mem_lev F x.2⟩ : SphereLoop n)) < a
    rw [S.rev x, energy_reverseSphere]
    exact hx
  N_rev := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩, ?_, rfl⟩
    change a' < Real.sqrt (energy F (S.D ⟨reverseSphere (x : SphereLoop n),
      reverse_mem_lev F x.2⟩ : SphereLoop n))
    rw [S.rev x, energy_reverseSphere]
    exact hx
  lev_subset := by
    intro u hu
    refine ⟨⟨u, lev_mono F hab hu⟩, ?_, rfl⟩
    have hle : Real.sqrt (energy F (S.D ⟨u, lev_mono F hab hu⟩ : SphereLoop n)) ≤
        Real.sqrt (energy F u) := Real.sqrt_le_sqrt (energy_D_le S ⟨u, lev_mono F hab hu⟩)
    rcases hu with hu | ⟨y, rfl⟩
    · exact lt_of_le_of_lt hle hu
    · rw [energy_constantSphereLoop, Real.sqrt_zero] at hle
      exact lt_of_le_of_lt hle ha
  subset_lev := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  cover := by
    intro u hu
    rcases lt_or_ge (Real.sqrt (energy F (S.D ⟨u, hu⟩ : SphereLoop n))) a with h | h
    · exact Or.inl ⟨⟨u, hu⟩, h, rfl⟩
    · exact Or.inr ⟨⟨u, hu⟩, lt_of_lt_of_le ha' h, rfl⟩
  avoids := by
    rintro _ ⟨⟨x, hx, rfl⟩, -⟩
    exact hloc x hx
  retraction :=
    { r := S.D
      r_mem := by
        rintro x ⟨x', hx', hxx⟩
        have he : x' = x := Subtype.ext hxx
        rw [he] at hx'
        exact Or.inl hx'
      H := S.G
      keep := fun τ x hx => mem_lev_of_energy_le F (S.energy_le τ x) hx }
  rev_comm := S.rev

/-- Level deformations and lenses from shortenings. Let crit be a set of positive levels such
that (descent) for an interval [a, a'] without critical levels and b ≥ a', some shortening of
t_b has an iterate taking t_{a'} into t_a, and (localization) for tight cuts a' < c < b around
a critical level c, some shortening D of t_b is such that the loops x of t_b with √E(D x) > a'
avoid the point p. Then intervals without critical levels carry level deformations and tight
cuts around critical levels carry lenses for p. The shortening may depend on the cuts. -/
theorem flow_of_shortening (F : ReversibleMetric n) (p : Sphere n) (crit : Set ℝ)
    (hpos : ∀ c ∈ crit, 0 < c)
    (hdesc : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
      ∃ (S : Data F b) (k : ℕ), ∀ x : lev F b, (x : Loops n) ∈ lev F a' →
        (iter S k x : Loops n) ∈ lev F a)
    (hloc : ∀ c ∈ crit, ∃ ε : ℝ, 0 < ε ∧ ∀ a' b : ℝ, c - ε < a' → a' < c → c < b → b < c + ε →
      ∃ S : Data F b, ∀ x : lev F b,
        a' < Real.sqrt (energy F (S.D x : SphereLoop n)) → (x : Loops n) ∈ avoid p) :
    (∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
      Nonempty (LevelDeformation F a a' b)) ∧
    (∀ c ∈ crit, ∃ ε : ℝ, 0 < ε ∧ ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε →
      Nonempty (Lens F a b p)) := by
  constructor
  · intro a a' b ha haa hab hreg
    obtain ⟨S, k, hk⟩ := hdesc a a' b ha haa hab hreg
    exact ⟨levelDeformation S k hk⟩
  · intro c hc
    obtain ⟨ε, hε, h⟩ := hloc c hc
    have hc0 : 0 < c := hpos c hc
    refine ⟨min ε c, lt_min hε hc0, ?_⟩
    intro a b ha1 ha2 hb1 hb2
    have ha0 : 0 < a := by
      have : c - min ε c ≥ 0 := sub_nonneg.mpr (min_le_right _ _)
      linarith
    have haε : c - ε < a := by
      have := min_le_left ε c
      linarith
    obtain ⟨a', ha'1, ha'2⟩ := exists_between haε
    have hbε : b < c + ε := by
      have := min_le_left ε c
      linarith
    obtain ⟨S, hS⟩ := h a' b ha'1 (ha'2.trans ha2) hb1 hbε
    exact ⟨lens S p ha0 ha'2 (ha2.trans hb1).le hS⟩

end

end Finsler.Shortening
