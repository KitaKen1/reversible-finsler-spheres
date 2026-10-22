module

public import Finsler.Topology.BorelCoverK

/-! Covers by functionals which are odd under the half rotation. A continuous real functional ψ
on loops with ψ(τu) = −ψ(u) which is even or odd under the reversal splits the set
{η < |ψ|}, η ≥ 0, into the open pieces {η < ψ} and {ψ < −η}: the half rotation exchanges them,
and the reversal keeps or exchanges them. For an open invariant set X and a finite list of such
functionals, X is the union of the set N of the loops of X on which all the functionals are
smaller than η′ in absolute value and of the sets X ∩ {η < |ψ|}, for η < η′. Hence the power of
U = v(v + w) given by the number of functionals vanishes on the K-Borel cohomology of
(X, N). -/

@[expose] public section

namespace Finsler.FunctionalCover

open Set Topology
open Finsler.BorelCochain Finsler.BorelLoop Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelIterate Finsler.BorelK Finsler.BorelCoverK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- A continuous functional on loops which is odd under the half rotation and even or odd under
the reversal. -/
structure OddFunctional (n : ℕ) where
  ψ : SphereLoop n → ℝ
  continuous : Continuous ψ
  half_odd : ∀ u, ψ (half +ᵥ u) = -ψ u
  rev_parity : (∀ u, ψ (reverseSphere u) = ψ u) ∨ (∀ u, ψ (reverseSphere u) = -ψ u)

theorem oddFunctional_abs_half (f : OddFunctional n) (u : SphereLoop n) :
    |f.ψ (half +ᵥ u)| = |f.ψ u| := by
  rw [f.half_odd, abs_neg]

theorem oddFunctional_abs_rev (f : OddFunctional n) (u : SphereLoop n) :
    |f.ψ (reverseSphere u)| = |f.ψ u| := by
  rcases f.rev_parity with h | h
  · rw [h]
  · rw [h, abs_neg]

/-- The loops of an open invariant set on which a functional exceeds η in absolute value, as a
typed set. -/
def typedOf (f : OddFunctional n) {η : ℝ} (hη : 0 ≤ η) {X : Set (Loops n)} (hXo : IsOpen X)
    (hX : KInv X) : Typed n where
  V := X ∩ {u | η < |f.ψ u|}
  isOpen := hXo.inter (isOpen_lt continuous_const (continuous_abs.comp f.continuous))
  inv := kInv_inter hX
    ⟨fun u hu => by
        change η < |f.ψ (reverseSphere u)|
        rw [oddFunctional_abs_rev f]
        exact hu,
      fun u hu => by
        change η < |f.ψ (half +ᵥ u)|
        rw [oddFunctional_abs_half f]
        exact hu⟩
  split :=
    { pos := {u | η < f.ψ u}
      neg := {u | f.ψ u < -η}
      pos_open := isOpen_lt continuous_const f.continuous
      neg_open := isOpen_lt f.continuous continuous_const
      cover := fun u hu => by
        have h2 : η < |f.ψ u| := hu.2
        rcases lt_abs.mp h2 with h | h
        · exact Or.inl h
        · exact Or.inr (show f.ψ u < -η by linarith)
      disjoint := fun u _ h1 h2 => by
        have h1' : η < f.ψ u := h1
        have h2' : f.ψ u < -η := h2
        linarith
      half_pos := fun u hu => by
        have hu' : η < f.ψ u := hu
        change f.ψ (half +ᵥ u) < -η
        rw [f.half_odd]
        linarith
      half_neg := fun u hu => by
        have hu' : f.ψ u < -η := hu
        change η < f.ψ (half +ᵥ u)
        rw [f.half_odd]
        linarith }
  type := by
    rcases f.rev_parity with h | h
    · left
      exact ⟨fun u hu => by
          change η < f.ψ (reverseSphere u)
          rw [h]
          exact hu,
        fun u hu => by
          change f.ψ (reverseSphere u) < -η
          rw [h]
          exact hu⟩
    · right
      exact ⟨fun u hu => by
          have hu' : η < f.ψ u := hu
          change f.ψ (reverseSphere u) < -η
          rw [h]
          linarith,
        fun u hu => by
          have hu' : f.ψ u < -η := hu
          change η < f.ψ (reverseSphere u)
          rw [h]
          linarith⟩

theorem typedOf_V (f : OddFunctional n) {η : ℝ} (hη : 0 ≤ η) {X : Set (Loops n)}
    (hXo : IsOpen X) (hX : KInv X) : (typedOf f hη hXo hX).V = X ∩ {u | η < |f.ψ u|} := rfl

/-- The loops on which all functionals of a list are smaller than η′ in absolute value. -/
def nearSet : List (OddFunctional n) → ℝ → Set (Loops n)
  | [], _ => univ
  | f :: l, η' => {u | |f.ψ u| < η'} ∩ nearSet l η'

theorem isOpen_nearSet (l : List (OddFunctional n)) (η' : ℝ) : IsOpen (nearSet l η') := by
  induction l with
  | nil => exact isOpen_univ
  | cons f l ih =>
    exact (isOpen_lt (continuous_abs.comp f.continuous) continuous_const).inter ih

theorem nearSet_inv (l : List (OddFunctional n)) (η' : ℝ) : KInv (nearSet l η') := by
  induction l with
  | nil => exact ⟨fun _ _ => mem_univ _, fun _ _ => mem_univ _⟩
  | cons f l ih =>
    refine kInv_inter ⟨fun u hu => ?_, fun u hu => ?_⟩ ih
    · change |f.ψ (reverseSphere u)| < η'
      rw [oddFunctional_abs_rev f]
      exact hu
    · change |f.ψ (half +ᵥ u)| < η'
      rw [oddFunctional_abs_half f]
      exact hu

theorem mem_nearSet {l : List (OddFunctional n)} {η' : ℝ} {u : SphereLoop n}
    (h : ∀ f ∈ l, |f.ψ u| < η') : u ∈ nearSet l η' := by
  induction l with
  | nil => exact mem_univ _
  | cons f l ih =>
    exact ⟨h f List.mem_cons_self, ih fun g hg => h g (List.mem_cons_of_mem f hg)⟩

theorem mem_unionOf_of_mem {N : Set (Loops n)} {l : List (Typed n)} {T : Typed n} (hT : T ∈ l)
    {u : SphereLoop n} (hu : u ∈ T.V) : u ∈ unionOf N l := by
  induction l with
  | nil => exact absurd hT List.not_mem_nil
  | cons T' l ih =>
    rcases List.mem_cons.mp hT with h | h
    · subst h
      exact Or.inr hu
    · exact Or.inl (ih h)

theorem unionOf_subset {N X : Set (Loops n)} {l : List (Typed n)} (hN : N ⊆ X)
    (hl : ∀ T ∈ l, T.V ⊆ X) : unionOf N l ⊆ X := by
  induction l with
  | nil => exact hN
  | cons T l ih =>
    exact union_subset (ih fun T' hT' => hl T' (List.mem_cons_of_mem T hT'))
      (hl T List.mem_cons_self)

/-- For an open invariant set X and a finite list of functionals odd under the half rotation,
the power of U given by the number of functionals vanishes on the K-Borel cohomology of the
pair of X and the loops of X on which all functionals are smaller than η′ in absolute value. -/
theorem ann_of_functionals {X : Set (Loops n)} (hXo : IsOpen X) (hX : KInv X)
    (l : List (OddFunctional n)) {η' : ℝ} (hη' : 0 < η') (q : ℕ)
    (x : HR (borelInv (kCommuting (inter_subset_left : X ∩ nearSet l η' ⊆ X)
      (kInv_inter hX (nearSet_inv l η')) hX)) q) :
    Ann (kCommuting (inter_subset_left : X ∩ nearSet l η' ⊆ X)
      (kInv_inter hX (nearSet_inv l η')) hX) l.length q x := by
  have h := ann_of_cover (inter_subset_left : X ∩ nearSet l η' ⊆ X)
    (kInv_inter hX (nearSet_inv l η')) hX (hXo.inter (isOpen_nearSet l η'))
    (l.map fun f => typedOf f (le_refl (0 : ℝ)) hXo hX)
    (fun u hu => by
      by_cases hex : ∃ f ∈ l, 0 < |f.ψ u| ∧ η' ≤ |f.ψ u|
      · obtain ⟨f, hf, hpos, -⟩ := hex
        exact mem_unionOf_of_mem (List.mem_map.mpr ⟨f, hf, rfl⟩) ⟨hu, hpos⟩
      · refine subset_unionOf _ _ ⟨hu, mem_nearSet fun f hf => ?_⟩
        by_contra hge
        exact hex ⟨f, hf, hη'.trans_le (not_lt.mp hge), not_lt.mp hge⟩)
    (unionOf_subset inter_subset_left fun T hT => by
      obtain ⟨f, -, rfl⟩ := List.mem_map.mp hT
      exact inter_subset_left)
    q x
  rw [List.length_map] at h
  exact h

end

end Finsler.FunctionalCover
