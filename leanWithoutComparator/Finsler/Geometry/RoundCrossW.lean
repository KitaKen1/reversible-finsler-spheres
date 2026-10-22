module

public import Finsler.Geometry.RoundLoopFourier
public import Finsler.Topology.CoverW
public import Finsler.Topology.CoverV
public import Finsler.Topology.CrossingWK

/-! Nilpotence of w and v on the crossing groups of the round sphere.

The critical levels of the round metric are the numbers 2πm, m ≥ 1 (a critical level is
2^j √E for a tangent critical loop, and these energies are (2πm)²). Near the critical loops of
the level 2πm, uniformly within 1/4, the Fourier coefficients A_m and B_m of a loop have norm at
least 1/4 (they are at least 3/4 at the critical loops and move by at most twice the uniform
distance). The n + 1 coordinates of B_m are odd under the reversal: the sets where a coordinate
is nonzero, split by its sign, are oriented and cover the lens set of a crossing; hence w^{n+1}
vanishes on the lens pairs and on the reflection Borel cohomology of every single crossing.
For m odd, the coordinates of A_m are odd under the half rotation and even under the reversal:
the sets where a coordinate is nonzero are split by the half rotation with pieces kept by the
reversal, so v^{n+1} vanishes on the K-Borel cohomology of the crossing. No equivariant Thom
isomorphism and no classification of the critical manifold is used. -/

@[expose] public section

namespace Finsler.RoundCrossW

open Set Topology
open Finsler.BorelCochain Finsler.BorelLoop Finsler.BorelCrossing Finsler.SphereGeometry
open Finsler.IntervalSobolev Finsler.SobolevReverse Finsler.BorelLocal Finsler.BorelLens
open Finsler.BorelIterate Finsler.BorelLocalK Finsler.BorelCoverK Finsler.NilpotentW
open Finsler.Geometry Finsler.CriticalLevels Finsler.OrientedCritical Finsler.BorelK
open Finsler.SobolevCurveVariation Finsler.RoundLoopFourier Finsler.SobolevCircleAction
open scoped Real

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Critical levels and the tube -/

/-- The critical levels of the round metric are multiples of 2π. -/
theorem crit_round {c : ℝ} (hc : c ∈ crit (roundMetric n)) :
    ∃ m : ℕ, 0 < m ∧ c = 2 * π * m := by
  obtain ⟨u, hu, hE, j, rfl⟩ := hc
  obtain ⟨m', hm', hEm⟩ := energy_eq_of_critical hu hE
  refine ⟨2 ^ j * m', Nat.mul_pos (Nat.pow_pos two_pos) hm', ?_⟩
  rw [hEm, Real.sqrt_sq (by positivity)]
  push_cast
  ring

/-- Near the critical loops of the level 2πm the m-th coefficients do not vanish. -/
theorem tube_coef_ne {m : ℕ} (hm : 0 < m) {u : SphereLoop n}
    (hu : (u : Loops n) ∈ tube (roundMetric n) (2 * π * m) (1 / 4)) :
    sinCoef m u ≠ 0 ∧ cosCoef m u ≠ 0 := by
  obtain ⟨γ, hγ, hE, hd⟩ := hu
  obtain ⟨hA, hB⟩ := coef_ge_of_critical hm hγ hE
  have hsA := norm_cosCoef_sub_le m u γ hd
  have hsB := norm_sinCoef_sub_le m u γ hd
  constructor
  · intro h0
    rw [h0, zero_sub, norm_neg] at hsB
    linarith
  · intro h0
    rw [h0, zero_sub, norm_neg] at hsA
    linarith

theorem exists_coord_ne {v : Ambient n} (hv : v ≠ 0) : ∃ i : Fin (n + 1), v i ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact hv (by ext i; simpa using hc i)

/-! ### Oriented sets from reversal-odd functionals -/

/-- The loops of an open invariant set on which a reversal-odd functional does not vanish, with
the orientation by its sign. -/
def orientedOf {X : Set (Loops n)} (hXo : IsOpen X) (hX : CoverW.RInv X)
    (ψ : SphereLoop n → ℝ) (hψc : Continuous ψ) (hψr : ∀ u, ψ (reverseSphere u) = -ψ u) :
    CoverW.Oriented n where
  V := X ∩ {u | 0 < |ψ u|}
  isOpen := hXo.inter (isOpen_lt continuous_const (continuous_abs.comp hψc))
  inv := fun u hu => ⟨hX u hu.1, by
    change 0 < |ψ (reverseSphere u)|
    rw [hψr, abs_neg]
    exact hu.2⟩
  orient :=
    { pos := {u | 0 < ψ u}
      neg := {u | ψ u < 0}
      pos_open := isOpen_lt continuous_const hψc
      neg_open := isOpen_lt hψc continuous_const
      cover := fun u hu => by
        have h2 : 0 < |ψ u| := hu.2
        rcases lt_abs.mp h2 with h | h
        · exact Or.inl h
        · exact Or.inr (show ψ u < 0 by linarith)
      disjoint := fun u _ h1 h2 => by
        have h1' : 0 < ψ u := h1
        have h2' : ψ u < 0 := h2
        linarith
      rev_pos := fun u hu => by
        have hu' : 0 < ψ u := hu
        change ψ (reverseSphere u) < 0
        rw [hψr]
        linarith
      rev_neg := fun u hu => by
        have hu' : ψ u < 0 := hu
        change 0 < ψ (reverseSphere u)
        rw [hψr]
        linarith }

theorem mem_unionOf_of_mem {N : Set (Loops n)} {l : List (CoverW.Oriented n)}
    {T : CoverW.Oriented n} (hT : T ∈ l) {u : SphereLoop n} (hu : u ∈ T.V) :
    u ∈ CoverW.unionOf N l := by
  induction l with
  | nil => exact absurd hT List.not_mem_nil
  | cons T' l ih =>
    rcases List.mem_cons.mp hT with h | h
    · subst h
      exact Or.inr hu
    · exact Or.inl (ih h)

theorem unionOf_subset {N X : Set (Loops n)} {l : List (CoverW.Oriented n)} (hN : N ⊆ X)
    (hl : ∀ T ∈ l, T.V ⊆ X) : CoverW.unionOf N l ⊆ X := by
  induction l with
  | nil => exact hN
  | cons T l ih =>
    exact union_subset (ih fun T' hT' => hl T' (List.mem_cons_of_mem T hT'))
      (hl T List.mem_cons_self)

/-- The coordinates of the sine coefficient as reversal-odd functionals. -/
theorem sinCoord_continuous (m : ℕ) (i : Fin (n + 1)) :
    Continuous (fun u : SphereLoop n => sinCoef m u i) :=
  (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp (continuous_sinCoef m))

theorem sinCoord_reverse (m : ℕ) (i : Fin (n + 1)) (u : SphereLoop n) :
    sinCoef m (reverseSphere u) i = -sinCoef m u i := by
  rw [sinCoef_reverse]
  simp

/-- On the lens pair of a local lens inside the tube around the critical loops of the level
2πm, w^{n+1} vanishes. -/
theorem lens_wPow_zero {m : ℕ} (hm : 0 < m) {a b : ℝ} (hb : 0 < b)
    (L : LocalLens (roundMetric n) a b (tube (roundMetric n) (2 * π * m) (1 / 4))) (q : ℕ)
    (y : HR (CoverW.rC (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩)) q) :
    wPow (CoverW.rC (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩)) q (n + 1) y = 0 := by
  have hXo : IsOpen (L.N ∩ lev (roundMetric n) b) := L.N_open.inter (lev_isOpen _ hb)
  have hX : CoverW.RInv (L.N ∩ lev (roundMetric n) b) :=
    fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩
  let l : List (CoverW.Oriented n) := List.ofFn fun i : Fin (n + 1) =>
    orientedOf hXo hX (fun u => sinCoef m u i) (sinCoord_continuous m i) (sinCoord_reverse m i)
  have hlen : l.length = n + 1 := List.length_ofFn
  have h1 : L.N ∩ lev (roundMetric n) b ⊆ CoverW.unionOf (L.N ∩ L.Y) l := by
    intro u hu
    have hne := (tube_coef_ne hm (L.inside hu)).1
    obtain ⟨i, hi⟩ := exists_coord_ne hne
    exact mem_unionOf_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩) ⟨hu, abs_pos.mpr hi⟩
  have h2 : CoverW.unionOf (L.N ∩ L.Y) l ⊆ L.N ∩ lev (roundMetric n) b := by
    refine unionOf_subset (inter_subset_inter_right L.N L.subset_lev) fun T hT => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact inter_subset_left
  have h := CoverW.wPow_of_cover (inter_subset_inter_right L.N L.subset_lev)
    (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩) hX (L.N_open.inter L.Y_open) l h1 h2 q y
  rw [hlen] at h
  exact h

/-- W-NIL for the round sphere: for regular cuts 0 < a ≤ b with at most one critical level
between them, w^{n+1} vanishes on the reflection Borel cohomology of the crossing pair. -/
theorem crossW_pow_zero (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hac : a ∉ crit (roundMetric n)) (hbc : b ∉ crit (roundMetric n))
    (hsub : (crit (roundMetric n) ∩ Icc a b).Subsingleton) (q : ℕ)
    (z : HR (crossComplex (roundMetric n) hab) q) :
    wPow (crossComplex (roundMetric n) hab) q (n + 1) z = 0 := by
  refine CoverW.crossW_pow_zero_of_flow (roundMetric n) (crit (roundMetric n)) (n + 1)
    (CrossingW.levelDeformation_of_regular _ hn) hab ha hac hbc hsub (fun c hc => ?_) q z
  obtain ⟨m, hm, rfl⟩ := crit_round hc.1
  have hc0 : 0 < 2 * π * m := by positivity
  obtain ⟨ε, hε, hL⟩ := localLens_of_shortening (roundMetric n) hc0
    (tube (roundMetric n) (2 * π * m) (1 / 4))
    (BirkhoffNear.exists_near (roundMetric n) hn hc0 (by norm_num))
  refine ⟨ε, hε, fun a' b' h1 h2 h3 h4 => ?_⟩
  obtain ⟨L⟩ := hL a' b' h1 h2 h3 h4
  exact ⟨_, L, fun q y => lens_wPow_zero hm (hc0.trans h3) L q y⟩

/-! ### The class v at odd stages -/

/-- The loops of an open invariant set on which a functional odd under the half rotation and even
under the reversal does not vanish, split by its sign. -/
def keptOf {X : Set (Loops n)} (hXo : IsOpen X) (hX : KInv X) (ψ : SphereLoop n → ℝ)
    (hψc : Continuous ψ) (hψh : ∀ u, ψ (half +ᵥ u) = -ψ u)
    (hψr : ∀ u, ψ (reverseSphere u) = ψ u) : CoverV.Kept n where
  V := X ∩ {u | 0 < |ψ u|}
  isOpen := hXo.inter (isOpen_lt continuous_const (continuous_abs.comp hψc))
  inv := kInv_inter hX
    ⟨fun u hu => by
        change 0 < |ψ (reverseSphere u)|
        rw [hψr]
        exact hu,
      fun u hu => by
        change 0 < |ψ (half +ᵥ u)|
        rw [hψh, abs_neg]
        exact hu⟩
  split :=
    { pos := {u | 0 < ψ u}
      neg := {u | ψ u < 0}
      pos_open := isOpen_lt continuous_const hψc
      neg_open := isOpen_lt hψc continuous_const
      cover := fun u hu => by
        have h2 : 0 < |ψ u| := hu.2
        rcases lt_abs.mp h2 with h | h
        · exact Or.inl h
        · exact Or.inr (show ψ u < 0 by linarith)
      disjoint := fun u _ h1 h2 => by
        have h1' : 0 < ψ u := h1
        have h2' : ψ u < 0 := h2
        linarith
      half_pos := fun u hu => by
        have hu' : 0 < ψ u := hu
        change ψ (half +ᵥ u) < 0
        rw [hψh]
        linarith
      half_neg := fun u hu => by
        have hu' : ψ u < 0 := hu
        change 0 < ψ (half +ᵥ u)
        rw [hψh]
        linarith }
  keeps :=
    ⟨fun u hu => by
        change 0 < ψ (reverseSphere u)
        rw [hψr]
        exact hu,
      fun u hu => by
        change ψ (reverseSphere u) < 0
        rw [hψr]
        exact hu⟩

theorem mem_unionOfV_of_mem {N : Set (Loops n)} {l : List (CoverV.Kept n)}
    {T : CoverV.Kept n} (hT : T ∈ l) {u : SphereLoop n} (hu : u ∈ T.V) :
    u ∈ CoverV.unionOf N l := by
  induction l with
  | nil => exact absurd hT List.not_mem_nil
  | cons T' l ih =>
    rcases List.mem_cons.mp hT with h | h
    · subst h
      exact Or.inr hu
    · exact Or.inl (ih h)

theorem unionOfV_subset {N X : Set (Loops n)} {l : List (CoverV.Kept n)} (hN : N ⊆ X)
    (hl : ∀ T ∈ l, T.V ⊆ X) : CoverV.unionOf N l ⊆ X := by
  induction l with
  | nil => exact hN
  | cons T l ih =>
    exact union_subset (ih fun T' hT' => hl T' (List.mem_cons_of_mem T hT'))
      (hl T List.mem_cons_self)

theorem cosCoord_continuous (m : ℕ) (i : Fin (n + 1)) :
    Continuous (fun u : SphereLoop n => cosCoef m u i) :=
  (continuous_apply i).comp ((PiLp.continuous_ofLp 2 _).comp (continuous_cosCoef m))

theorem cosCoord_reverse (m : ℕ) (i : Fin (n + 1)) (u : SphereLoop n) :
    cosCoef m (reverseSphere u) i = cosCoef m u i := by
  rw [cosCoef_reverse]

theorem cosCoord_half {m : ℕ} (hm : Odd m) (i : Fin (n + 1)) (u : SphereLoop n) :
    cosCoef m (half +ᵥ u) i = -cosCoef m u i := by
  rw [cosCoef_half, hm.neg_one_pow]
  simp

/-- On the K-lens pair of a local lens compatible with the half rotation inside the tube around
the critical loops of the level 2πm, m odd, v^{n+1} vanishes. -/
theorem lens_vPow_zero {m : ℕ} (hm : 0 < m) (hodd : Odd m) {a b : ℝ} (hb : 0 < b)
    (L : LocalLens (roundMetric n) a b (tube (roundMetric n) (2 * π * m) (1 / 4)))
    (hL : HalfLens (roundMetric n) L) (q : ℕ)
    (y : HR (borelInv (subCommuting (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩))) q) :
    wPow (borelInv (subCommuting (inter_subset_inter_right L.N L.subset_lev)
      (fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩)
      (fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩)
      (fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩))) q (n + 1) y = 0 := by
  have hXo : IsOpen (L.N ∩ lev (roundMetric n) b) := L.N_open.inter (lev_isOpen _ hb)
  have hX : KInv (L.N ∩ lev (roundMetric n) b) :=
    ⟨fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev _ hu.2⟩,
      fun u hu => ⟨hL.N_half u hu.1, half_mem_lev _ hu.2⟩⟩
  have hN : KInv (L.N ∩ L.Y) :=
    ⟨fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩,
      fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩⟩
  let l : List (CoverV.Kept n) := List.ofFn fun i : Fin (n + 1) =>
    keptOf hXo hX (fun u => cosCoef m u i) (cosCoord_continuous m i) (cosCoord_half hodd i)
      (cosCoord_reverse m i)
  have hlen : l.length = n + 1 := List.length_ofFn
  have h1 : L.N ∩ lev (roundMetric n) b ⊆ CoverV.unionOf (L.N ∩ L.Y) l := by
    intro u hu
    have hne := (tube_coef_ne hm (L.inside hu)).2
    obtain ⟨i, hi⟩ := exists_coord_ne hne
    exact mem_unionOfV_of_mem (List.mem_ofFn.mpr ⟨i, rfl⟩) ⟨hu, abs_pos.mpr hi⟩
  have h2 : CoverV.unionOf (L.N ∩ L.Y) l ⊆ L.N ∩ lev (roundMetric n) b := by
    refine unionOfV_subset (inter_subset_inter_right L.N L.subset_lev) fun T hT => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hT
    exact inter_subset_left
  have h := CoverV.vPow_of_cover (inter_subset_inter_right L.N L.subset_lev) hN hX
    (L.N_open.inter L.Y_open) l h1 h2 q y
  rw [hlen] at h
  exact h

/-- V-NIL for the round sphere at odd stages: for regular cuts 0 < a ≤ b with at most one
critical level between them, of the form 2πm with m odd, v^{n+1} vanishes on the K-Borel
cohomology of the crossing pair. -/
theorem crossV_pow_zero (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b) (ha : 0 < a)
    (hac : a ∉ crit (roundMetric n)) (hbc : b ∉ crit (roundMetric n))
    (hsub : (crit (roundMetric n) ∩ Icc a b).Subsingleton)
    (hodd : ∀ c ∈ crit (roundMetric n) ∩ Icc a b, ∃ m : ℕ, Odd m ∧ c = 2 * π * m) (q : ℕ)
    (z : HR (borelInv (crossCommuting (roundMetric n) hab)) q) :
    wPow (borelInv (crossCommuting (roundMetric n) hab)) q (n + 1) z = 0 := by
  refine CoverV.crossV_pow_zero_of_flow (roundMetric n) (crit (roundMetric n)) (n + 1)
    (CrossingW.levelDeformation_of_regular _ hn) hab ha hac hbc hsub (fun c hc => ?_) q z
  obtain ⟨m, hmo, rfl⟩ := hodd c hc
  have hm : 0 < m := hmo.pos
  have hc0 : 0 < 2 * π * m := by positivity
  obtain ⟨ε, hε, hL⟩ := CrossingWK.halfLens_of_shortening (roundMetric n) hc0
    (tube (roundMetric n) (2 * π * m) (1 / 4))
    (ShorteningK.exists_near_half (roundMetric n) hn hc0 (by norm_num))
  refine ⟨ε, hε, fun a' b' h1 h2 h3 h4 => ?_⟩
  obtain ⟨L, hLh⟩ := hL a' b' h1 h2 h3 h4
  exact ⟨_, L, hLh, fun q y => lens_vPow_zero hm hmo (hc0.trans h3) L hLh q y⟩

end

end Finsler.RoundCrossW
