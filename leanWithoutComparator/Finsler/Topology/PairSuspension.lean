module

public import Finsler.Topology.PairTriple

/-! The suspension isomorphism for ordinary F₂ cohomology of pairs. For a subset P of a space X
and an open set O, the suspended pair in X × ℝ consists of the points over P, relative to those
with nonzero real coordinate or with base point in O. The points over P relative to those with
positive real coordinate or base point in O have vanishing cohomology (push the real coordinate
to 1), so the connecting map of the triple is bijective; the part with negative real coordinate
or base point in O is an excision of the suspended subspace relative to the positive part, and
it deforms onto the copy of (P, P ∩ O) at height −1. Hence the cohomology of the suspended pair
in degree n + 1 is that of (P, P ∩ O) in degree n, and it vanishes in degree zero. Iterating,
the b-fold suspended pair has the cohomology of (P, P ∩ O) shifted by b, and no cohomology in
degrees below b. No product structure of cohomology is used. -/

@[expose] public section

namespace Finsler.PairSuspension

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelExact
open Finsler.BorelLoop Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The product of a space with the real line. -/
abbrev Cyl (X : TopCat.{0}) : TopCat.{0} := TopCat.of (X × ℝ)

variable {X : TopCat.{0}} (P O : Set X)

/-- The points over P. -/
def cyl : Set (Cyl X) := {y | y.1 ∈ P}

/-- The points with nonzero real coordinate or base point in O. -/
def suspO : Set (Cyl X) := {y | y.2 ≠ 0 ∨ y.1 ∈ O}

/-- The points with positive real coordinate or base point in O. -/
def upO : Set (Cyl X) := {y | 0 < y.2 ∨ y.1 ∈ O}

/-- The points with negative real coordinate or base point in O. -/
def dnO : Set (Cyl X) := {y | y.2 < 0 ∨ y.1 ∈ O}

variable {O}

theorem suspO_isOpen (hO : IsOpen O) : IsOpen (suspO O) :=
  (isOpen_ne_fun continuous_snd continuous_const).union (hO.preimage continuous_fst)

theorem upO_isOpen (hO : IsOpen O) : IsOpen (upO O) :=
  (isOpen_lt continuous_const continuous_snd).union (hO.preimage continuous_fst)

theorem dnO_isOpen (hO : IsOpen O) : IsOpen (dnO O) :=
  (isOpen_lt continuous_snd continuous_const).union (hO.preimage continuous_fst)

variable (O)

theorem up_sub_susp : cyl P ∩ upO O ⊆ cyl P ∩ suspO O :=
  fun _ hy => ⟨hy.1, hy.2.imp (fun h => ne_of_gt h) id⟩

theorem dn_sub_susp : cyl P ∩ dnO O ⊆ cyl P ∩ suspO O :=
  fun _ hy => ⟨hy.1, hy.2.imp (fun h => ne_of_lt h) id⟩

theorem base_sub_dn : cyl P ∩ cyl O ⊆ cyl P ∩ dnO O :=
  fun _ hy => ⟨hy.1, Or.inr hy.2⟩

theorem base_sub_up : cyl P ∩ cyl O ⊆ cyl P ∩ upO O :=
  fun _ hy => ⟨hy.1, Or.inr hy.2⟩

/-- A convex combination of a positive number and 1 is positive. -/
theorem pos_of_combination {s : ℝ} (hs : 0 < s) (τ : unitInterval) :
    0 < (1 - (τ : ℝ)) * s + τ := by
  rcases eq_or_lt_of_le τ.2.1 with h | h
  · rw [← h]
    simpa using hs
  · have := mul_nonneg (sub_nonneg.mpr τ.2.2) hs.le
    linarith

/-- A convex combination of a negative number and −1 is negative. -/
theorem neg_of_combination {s : ℝ} (hs : s < 0) (τ : unitInterval) :
    (τ : ℝ) * s - (1 - τ) < 0 := by
  rcases eq_or_lt_of_le τ.2.2 with h | h
  · rw [h]
    simpa using hs
  · have := mul_nonneg τ.2.1 (neg_nonneg.mpr hs.le)
    nlinarith

/-- The map pushing the real coordinate to 1. -/
def topMap : C(cyl P, cyl P) :=
  ⟨fun y => ⟨((y : X × ℝ).1, 1), y.2⟩,
    ((continuous_fst.comp continuous_subtype_val).prodMk continuous_const).subtype_mk _⟩

/-- The homotopy pushing the real coordinate to 1. -/
def topHomotopy : (ContinuousMap.id (cyl P)).Homotopy (topMap P) where
  toFun p := ⟨((p.2 : X × ℝ).1, (1 - (p.1 : ℝ)) * (p.2 : X × ℝ).2 + p.1), p.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk ?_
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).add
      (continuous_subtype_val.comp continuous_fst)
  map_zero_left y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (1 - ((0 : unitInterval) : ℝ)) * (y : X × ℝ).2 + ((0 : unitInterval) : ℝ) =
        (y : X × ℝ).2
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_mul, add_zero]
  map_one_left y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (1 - ((1 : unitInterval) : ℝ)) * (y : X × ℝ).2 + ((1 : unitInterval) : ℝ) = 1
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_mul, zero_add]

theorem topHomotopy_mem (τ : unitInterval) (y : cyl P) (hy : (y : Cyl X) ∈ cyl P ∩ upO O) :
    (topHomotopy P (τ, y) : Cyl X) ∈ cyl P ∩ upO O := by
  refine ⟨hy.1, ?_⟩
  rcases hy.2 with h | h
  · exact Or.inl (pos_of_combination h τ)
  · exact Or.inr h

/-- The points over P deform into the positive part, keeping it. -/
def topDeformation :
    PairDeformation (cyl P ∩ upO O) (cyl P ∩ upO O) (cyl P ∩ upO O) (cyl P) where
  r := topMap P
  H := topHomotopy P
  r_mem y := ⟨y.2, Or.inl one_pos⟩
  r_sub y _ := ⟨y.2, Or.inl one_pos⟩
  keep_sub' := topHomotopy_mem P O
  keep := topHomotopy_mem P O
  keep_sub := topHomotopy_mem P O

/-- The cohomology of the points over P relative to the positive part vanishes. -/
theorem up_eq_zero (n : ℕ)
    (x : H (triv (pairOf ((up_sub_susp P O).trans inter_subset_left))) n) : x = 0 := by
  have hb := PairTriple.bijective_Hmap _ (fun k => bijective_nativePull_inclPair
    (subset_refl (cyl P ∩ upO O)) ((up_sub_susp P O).trans inter_subset_left)
    (subset_refl _) ((up_sub_susp P O).trans inter_subset_left) (topDeformation P O) k) n
  apply hb.1
  rw [map_zero]
  exact H_self_eq_zero _ n _

/-- The connecting map of the triple of the positive part, the suspended subspace and the
points over P is bijective. -/
theorem delta_bijective (n : ℕ) :
    Function.Bijective (tripleDelta (up_sub_susp P O)
      (inter_subset_left : cyl P ∩ suspO O ⊆ cyl P) n) :=
  tripleDelta_bijective _ _ n (up_eq_zero P O n) (up_eq_zero P O (n + 1))

/-- The cohomology of the suspended pair vanishes in degree zero. -/
theorem susp_zero (z : H (triv (pairOf (inter_subset_left : cyl P ∩ suspO O ⊆ cyl P))) 0) :
    z = 0 :=
  triple_zero (up_sub_susp P O) inter_subset_left (up_eq_zero P O 0) z

/-- The negative part relative to the points over P ∩ O is an excision of the suspended
subspace relative to the positive part. -/
theorem exc_bijective (hO : IsOpen O) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (base_sub_dn P O) (up_sub_susp P O)
      (base_sub_up P O) (dn_sub_susp P O))) n) := by
  refine bijective_Hmap_excision _ _ _ _ ?_ (upO O) (dnO O) (upO_isOpen hO) (dnO_isOpen hO)
    ?_ ?_ ?_ n
  · rintro y ⟨hyP, hyd⟩ ⟨_, hyu⟩
    refine ⟨hyP, ?_⟩
    rcases hyd with hd | hd
    · rcases hyu with hu | hu
      · exact absurd hu (lt_asymm hd)
      · exact hu
    · exact hd
  · rintro y ⟨_, hy⟩
    rcases hy with hy | hy
    · rcases lt_or_gt_of_ne hy with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr hy)
  · exact fun y hy => ⟨hy.2.1, hy.1⟩
  · exact fun y hy => ⟨hy.2.1, hy.1⟩

/-- The projection of the negative part to P. -/
def projMap : C(↥(cyl P ∩ dnO O), P) :=
  ⟨fun y => ⟨((y : X × ℝ).1 : X), y.2.1⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩

/-- The copy of P at height −1. -/
def botMap : C(P, ↥(cyl P ∩ dnO O)) :=
  ⟨fun x => ⟨((x : X), (-1 : ℝ)), x.2, Or.inl (by norm_num)⟩,
    (continuous_subtype_val.prodMk continuous_const).subtype_mk _⟩

/-- The homotopy pushing the real coordinate of the negative part to −1. -/
def botHomotopy : ((botMap P O).comp (projMap P O)).Homotopy
    (ContinuousMap.id ↥(cyl P ∩ dnO O)) where
  toFun p := ⟨((p.2 : X × ℝ).1, (p.1 : ℝ) * (p.2 : X × ℝ).2 - (1 - (p.1 : ℝ))), p.2.2.1, by
    rcases p.2.2.2 with h | h
    · exact Or.inl (neg_of_combination h p.1)
    · exact Or.inr h⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk ?_
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))).sub
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
  map_zero_left y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change ((0 : unitInterval) : ℝ) * (y : X × ℝ).2 - (1 - ((0 : unitInterval) : ℝ)) = -1
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, zero_mul, sub_zero, zero_sub]
  map_one_left y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change ((1 : unitInterval) : ℝ) * (y : X × ℝ).2 - (1 - ((1 : unitInterval) : ℝ)) =
        (y : X × ℝ).2
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, one_mul, sub_self, sub_zero]

/-- The projection of the negative part relative to the points over P ∩ O onto (P, P ∩ O) is
bijective on cohomology. -/
theorem proj_bijective (n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX (base_sub_dn P O)
      (inter_subset_left : P ∩ O ⊆ P) (projMap P O) (fun _ hy => ⟨hy.1, hy.2⟩))) n) :=
  bijective_Hmap_of_section (base_sub_dn P O) inter_subset_left (projMap P O) (botMap P O)
    (fun _ hy => ⟨hy.1, hy.2⟩) (fun _ hx => ⟨hx.1, hx.2⟩) (by ext x; rfl) (botHomotopy P O)
    (fun _ _ hy => ⟨hy.1, hy.2⟩) n

/-- The suspension isomorphism: the cohomology of (P, P ∩ O) in degree n is the cohomology of
the suspended pair in degree n + 1. -/
def suspEquiv (hO : IsOpen O) (n : ℕ) :
    H (triv (pairOf (inter_subset_left : P ∩ O ⊆ P))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_left : cyl P ∩ suspO O ⊆ cyl P))) (n + 1) :=
  ((LinearEquiv.ofBijective _ (proj_bijective P O n)).trans
    (LinearEquiv.ofBijective _ (exc_bijective P O hO n)).symm).trans
    (LinearEquiv.ofBijective _ (delta_bijective P O n))

/-- The b-fold product of a space with the real line. -/
def iterSpace (X : TopCat.{0}) : ℕ → TopCat.{0}
  | 0 => X
  | b + 1 => Cyl (iterSpace X b)

/-- The points of the b-fold product over P. -/
def iterCyl : (b : ℕ) → Set (iterSpace X b)
  | 0 => P
  | b + 1 => cyl (iterCyl b)

/-- The open set of the b-fold suspension: some real coordinate is nonzero or the base point
lies in O. -/
def iterOpen : (b : ℕ) → Set (iterSpace X b)
  | 0 => O
  | b + 1 => suspO (iterOpen b)

variable {O}

theorem iterOpen_isOpen (hO : IsOpen O) : ∀ b, IsOpen (iterOpen O b)
  | 0 => hO
  | b + 1 => suspO_isOpen (iterOpen_isOpen hO b)

/-- The b-fold suspension isomorphism. -/
def iterEquiv (hO : IsOpen O) : (b n : ℕ) →
    H (triv (pairOf (inter_subset_left : P ∩ O ⊆ P))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_left : iterCyl P b ∩ iterOpen O b ⊆ iterCyl P b))) (n + b)
  | 0, _ => LinearEquiv.refl _ _
  | b + 1, n => (iterEquiv hO b n).trans
      (suspEquiv (iterCyl P b) (iterOpen O b) (iterOpen_isOpen hO b) (n + b))

/-- The cohomology of the b-fold suspended pair vanishes in the degrees below b. -/
theorem iter_eq_zero (hO : IsOpen O) : ∀ (b n : ℕ), n < b →
    ∀ z : H (triv (pairOf (inter_subset_left : iterCyl P b ∩ iterOpen O b ⊆ iterCyl P b))) n,
      z = 0
  | 0, n, hn, _ => absurd hn (Nat.not_lt_zero n)
  | b + 1, 0, _, z => susp_zero (iterCyl P b) (iterOpen O b) z
  | b + 1, n + 1, hn, z => by
      let e := suspEquiv (iterCyl P b) (iterOpen O b) (iterOpen_isOpen hO b) n
      have h0 : e.symm z = 0 := iter_eq_zero hO b n (Nat.lt_of_succ_lt_succ hn) _
      calc z = e (e.symm z) := (e.apply_symm_apply z).symm
        _ = e 0 := by rw [h0]
        _ = 0 := e.map_zero

/-- The cohomology of the b-fold suspended pair in degree n + b has the dimension of the
cohomology of (P, P ∩ O) in degree n. -/
theorem finrank_iter (hO : IsOpen O) (b n : ℕ) :
    Module.finrank (ZMod 2)
        (H (triv (pairOf (inter_subset_left :
          iterCyl P b ∩ iterOpen O b ⊆ iterCyl P b))) (n + b)) =
      Module.finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : P ∩ O ⊆ P))) n) :=
  (iterEquiv P hO b n).finrank_eq.symm

end

end Finsler.PairSuspension
