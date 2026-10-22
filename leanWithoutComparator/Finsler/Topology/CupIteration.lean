module

public import Finsler.Topology.CupAssociativity

/-! Degree-one cup powers act on actual relative cohomology. The algebraic
iteration and nilpotence statements do not assume an equivariant realization. -/

@[expose] public section

namespace Finsler.CupIteration

open CategoryTheory SphereOddDegree Finsler.CochainComparison

noncomputable section

theorem absoluteCast_injective (X : TopCat.{0}) {m n : ℕ} (h : m = n) :
    Function.Injective (CupUnit.absoluteCast X h) := by
  subst n
  exact fun _ _ he => he

theorem relativeCast_injective (P : TopPair.{0}) {m n : ℕ} (h : m = n) :
    Function.Injective (CupBoundary.castClass P h) := by
  subst n
  exact fun _ _ he => he

/-- Addition of exponents for the actual degree-one absolute cup powers. -/
theorem power_add (X : TopCat.{0}) (a : cohomologyZMod2 X 1) (m n : ℕ) :
    cupPowZMod2 a (m + n) = cupZMod2 (cupPowZMod2 a m) (cupPowZMod2 a n) := by
  induction n with
  | zero => exact (CupUnit.absolute_one_right X m (cupPowZMod2 a m)).symm
  | succ n ih =>
      change cupZMod2 (cupPowZMod2 a (m + n)) a =
        cupZMod2 (cupPowZMod2 a m) (cupZMod2 (cupPowZMod2 a n) a)
      exact (congrArg (fun x => cupZMod2 x a) ih).trans
        (CupAssociativity.absolute_assoc X m n 1 (cupPowZMod2 a m) (cupPowZMod2 a n) a)

theorem power_nilpotent_add (X : TopCat.{0}) (a : cohomologyZMod2 X 1) (N k : ℕ)
    (hN : cupPowZMod2 a N = 0) : cupPowZMod2 a (N + k) = 0 := by
  rw [power_add, hN]
  exact map_zero _

theorem power_one (X : TopCat.{0}) (a : cohomologyZMod2 X 1) : cupPowZMod2 a 1 = a :=
  CupUnit.absolute_one_left X 1 a

theorem power_nilpotent_of_le (X : TopCat.{0}) (a : cohomologyZMod2 X 1) (N n : ℕ)
    (hN : cupPowZMod2 a N = 0) (hle : N ≤ n) : cupPowZMod2 a n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact power_nilpotent_add X a N k hN

def action (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (n q : ℕ)
    (b : RelativeCup.cohomology P q) : RelativeCup.cohomology P (n + q) :=
  RelativeCup.cup P n q (cupPowZMod2 a n) b

def actionLinear (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (n q : ℕ) :
    RelativeCup.cohomology P q →ₗ[ZMod 2] RelativeCup.cohomology P (n + q) :=
  RelativeCup.cupLinear P n q (cupPowZMod2 a n)

theorem actionLinear_apply (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (n q : ℕ)
    (b : RelativeCup.cohomology P q) : actionLinear P a n q b = action P a n q b := rfl

theorem action_add_right (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (n q : ℕ)
    (b c : RelativeCup.cohomology P q) :
    action P a n q (b + c) = action P a n q b + action P a n q c :=
  map_add (actionLinear P a n q) b c

theorem action_smul_right (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (n q : ℕ)
    (s : ZMod 2) (b : RelativeCup.cohomology P q) :
    action P a n q (s • b) = s • action P a n q b :=
  map_smul (actionLinear P a n q) s b

theorem action_zero_right (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (n q : ℕ) :
    action P a n q 0 = 0 := map_zero (actionLinear P a n q)

theorem action_zero (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (q : ℕ)
    (b : RelativeCup.cohomology P q) :
    CupBoundary.castClass P (Nat.zero_add q) (action P a 0 q b) = b :=
  CupUnit.relative_one_left P q b

/-- Iterating by m then n is multiplication by the (m+n)-th actual cup power. -/
theorem action_add (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (m n q : ℕ)
    (b : RelativeCup.cohomology P q) :
    CupBoundary.castClass P (Nat.add_assoc m n q) (action P a (m + n) q b) =
      action P a m (n + q) (action P a n q b) := by
  unfold action
  rw [power_add]
  exact CupAssociativity.relative_assoc P m n q (cupPowZMod2 a m) (cupPowZMod2 a n) b

theorem action_succ (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1) (n q : ℕ)
    (b : RelativeCup.cohomology P q) :
    CupBoundary.castClass P (Nat.add_assoc n 1 q) (action P a (n + 1) q b) =
      action P a n (1 + q) (RelativeCup.cup P 1 q a b) := by
  have h := action_add P a n 1 q b
  change _ = action P a n (1 + q) (RelativeCup.cup P 1 q (cupPowZMod2 a 1) b) at h
  rw [power_one] at h
  exact h

theorem action_natural {P Q : TopPair.{0}} (f : P ⟶ Q)
    (a : cohomologyZMod2 Q.fst 1) (n q : ℕ) (b : RelativeCup.cohomology Q q) :
    (TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f (n + q)).hom
        (action Q a n q b) =
      action P ((cohPullback (TopPair.Hom.fst f) 1).hom a) n q
        ((TopPair.singularCohomologyMap (R := coeff) (k := ZMod 2) (M := coeff) f q).hom b) := by
  unfold action
  rw [RelativeCup.naturality, cohPullback_cupPowZMod2]

theorem action_nilpotent_add (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1)
    (N k q : ℕ) (hN : cupPowZMod2 a N = 0) (b : RelativeCup.cohomology P q) :
    action P a (N + k) q b = 0 := by
  unfold action
  rw [power_nilpotent_add P.fst a N k hN]
  exact RelativeCup.zero_left P (N + k) q b

theorem action_nilpotent_of_le (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1)
    (N n q : ℕ) (hN : cupPowZMod2 a N = 0) (hle : N ≤ n)
    (b : RelativeCup.cohomology P q) : action P a n q b = 0 := by
  unfold action
  rw [power_nilpotent_of_le P.fst a N n hN hle]
  exact RelativeCup.zero_left P n q b

theorem action_nonzero_lt (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1)
    (N n q : ℕ) (hN : cupPowZMod2 a N = 0) (b : RelativeCup.cohomology P q)
    (hn : action P a n q b ≠ 0) : n < N := by
  by_contra h
  exact hn (action_nilpotent_of_le P a N n q hN (Nat.le_of_not_gt h) b)

theorem action_to_absolute (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1)
    (n q : ℕ) (b : RelativeCup.cohomology P q) :
    (relativeToPool P (n + q)).hom (action P a n q b) =
      cupZMod2 (cupPowZMod2 a n) ((relativeToPool P q).hom b) :=
  RelativeCup.relativeToPool_cup P n q (cupPowZMod2 a n) b

/-- The actual connecting morphism commutes with the power action over F₂. -/
theorem action_boundary (P : TopPair.{0}) (a : cohomologyZMod2 P.fst 1)
    (n q : ℕ) (b : cohomologyZMod2 P.snd q) :
    CupBoundary.boundary P (n + q)
        (cupZMod2 (cupPowZMod2 ((cohPullback P.map 1).hom a) n) b) =
      CupBoundary.castClass P (SphereOddDegree.AlexanderWhitney.aw_degree_right_succ n q)
        (action P a n (q + 1) (CupBoundary.boundary P q b)) := by
  have h := CupBoundary.boundary_cup P n q (cupPowZMod2 a n) b
  rw [cohPullback_cupPowZMod2] at h
  exact h

end

end Finsler.CupIteration
