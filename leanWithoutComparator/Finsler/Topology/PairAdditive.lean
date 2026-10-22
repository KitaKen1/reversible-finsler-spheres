module

public import Finsler.Topology.PairTriple

/-! Additivity of the ordinary cohomology of a pair over two disjoint open sets. Let s ⊆ t be
subsets of a space and O₁, O₂ disjoint open sets covering t. Then the two restrictions map the
cohomology of (t, s) bijectively onto the product of the cohomologies of the parts
(t ∩ O₁, s ∩ O₁) and (t ∩ O₂, s ∩ O₂). The part in O₁ is an excision of (t, s ∪ (t ∩ O₂)), and the
part in O₂ is an excision of (s ∪ (t ∩ O₂), s); so in the exact sequence of the triple
s ⊆ s ∪ (t ∩ O₂) ⊆ t a class restricting to zero on the part in O₂ comes from the cohomology of
(t, s ∪ (t ∩ O₂)), where it is determined by its restriction to the part in O₁, and every class
of the part in O₁ extends to a class of (t, s) which restricts to zero on the part in O₂. In
particular each restriction is surjective, and the cohomology of (t, s) vanishes in a degree
in which the cohomologies of both parts vanish. -/

@[expose] public section

namespace Finsler.PairAdditive

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelExact
open Finsler.BorelLoop Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The map on cohomology of a composite of maps of pairs. -/
theorem Hmap_comp_apply {P Q R : TopPair.{0}} (f : P ⟶ Q) (g : Q ⟶ R) (n : ℕ)
    (x : H (triv R) n) :
    Hmap (trivHom (f ≫ g)) n x = Hmap (trivHom f) n (Hmap (trivHom g) n x) := by
  rw [BorelInvariance.Hmap_pullHom, BorelInvariance.Hmap_pullHom, BorelInvariance.Hmap_pullHom,
    LinearEquiv.apply_symm_apply, Finsler.BorelLens.nativePull_comp]

variable {X : TopCat.{0}} {s t : Set X}

theorem part_sub (hst : s ⊆ t) (O₁ : Set X) : s ∩ O₁ ⊆ t ∩ O₁ :=
  inter_subset_inter_left O₁ hst

theorem sub_mid (O₂ : Set X) : s ⊆ s ∪ t ∩ O₂ := subset_union_left

theorem mid_sub (hst : s ⊆ t) (O₂ : Set X) : s ∪ t ∩ O₂ ⊆ t :=
  union_subset hst inter_subset_left

variable (hst : s ⊆ t) (O₁ O₂ : Set X)

/-- The restriction to the part in an open set. -/
abbrev restr (n : ℕ) :
    H (triv (pairOf hst)) n →ₗ[ZMod 2] H (triv (pairOf (part_sub hst O₁))) n :=
  Hmap (trivHom (inclPair (part_sub hst O₁) hst inter_subset_left inter_subset_left)) n

variable {O₁ O₂} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hdis : Disjoint O₁ O₂)
  (hcov : t ⊆ O₁ ∪ O₂)

include hO₁ hO₂ hdis hcov in
/-- The part in O₁ is an excision of (t, s ∪ (t ∩ O₂)). -/
theorem exc_one (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (part_sub hst O₁) (mid_sub hst O₂)
      (inter_subset_left.trans (sub_mid O₂)) inter_subset_left)) n) := by
  refine bijective_Hmap_excision _ _ _ _ ?_ O₂ O₁ hO₂ hO₁ ?_ ?_ ?_ n
  · rintro x hx (hx' | hx')
    · exact ⟨hx', hx.2⟩
    · exact absurd hx'.2 (Set.disjoint_left.mp hdis hx.2)
  · exact fun x hx => (hcov hx).symm
  · exact fun x hx => Or.inr ⟨hx.2, hx.1⟩
  · exact fun x hx => ⟨hx.2, hx.1⟩

include hO₁ hO₂ hdis hcov in
/-- The part in O₂ is an excision of (s ∪ (t ∩ O₂), s). -/
theorem exc_two (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (part_sub hst O₂) (sub_mid (s := s) (t := t) O₂)
      inter_subset_left subset_union_right)) n) := by
  refine bijective_Hmap_excision _ _ _ _ ?_ O₁ O₂ hO₁ hO₂ ?_ ?_ ?_ n
  · exact fun x hx hx' => ⟨hx', hx.2⟩
  · exact fun x hx => hcov (mid_sub hst O₂ hx)
  · rintro x ⟨hx, hx' | hx'⟩
    · exact hx'
    · exact absurd hx'.2 (Set.disjoint_left.mp hdis hx)
  · rintro x ⟨hx, hx' | hx'⟩
    · exact ⟨hst hx', hx⟩
    · exact hx'

include hO₁ hO₂ hdis hcov in
/-- A class which restricts to zero on both parts is zero. -/
theorem eq_zero_of_restr (n : ℕ) (x : H (triv (pairOf hst)) n)
    (h₁ : restr hst O₁ n x = 0) (h₂ : restr hst O₂ n x = 0) : x = 0 := by
  have e2 : inclPair (part_sub hst O₂) (sub_mid (s := s) (t := t) O₂) inter_subset_left
      subset_union_right ≫ incPair (sub_mid O₂) (mid_sub hst O₂) =
      inclPair (part_sub hst O₂) hst inter_subset_left inter_subset_left := by
    ext : 2 <;> rfl
  have hmid : Hmap (trivHom (incPair (sub_mid O₂) (mid_sub hst O₂))) n x = 0 := by
    apply (exc_two hst hO₁ hO₂ hdis hcov n).1
    rw [map_zero, ← Hmap_comp_apply, e2]
    exact h₂
  obtain ⟨y, rfl⟩ := exact_mid_ordinary (tripleExact (sub_mid O₂) (mid_sub hst O₂)) n x hmid
  have e1 : inclPair (part_sub hst O₁) hst inter_subset_left inter_subset_left ≫
      relPair (sub_mid O₂) (mid_sub hst O₂) =
      inclPair (part_sub hst O₁) (mid_sub hst O₂)
        (inter_subset_left.trans (sub_mid O₂)) inter_subset_left := by
    ext : 2 <;> rfl
  have hy : y = 0 := by
    apply (exc_one hst hO₁ hO₂ hdis hcov n).1
    rw [map_zero, ← e1, Hmap_comp_apply]
    exact h₁
  rw [hy, map_zero]

include hO₁ hO₂ hdis hcov in
/-- Every class of the part in O₁ extends to a class of (t, s) which restricts to zero on the
part in O₂. -/
theorem exists_extend (n : ℕ) (x₁ : H (triv (pairOf (part_sub hst O₁))) n) :
    ∃ z : H (triv (pairOf hst)) n, restr hst O₁ n z = x₁ ∧ restr hst O₂ n z = 0 := by
  obtain ⟨y, hy⟩ := (exc_one hst hO₁ hO₂ hdis hcov n).2 x₁
  refine ⟨Hmap (trivHom (relPair (sub_mid O₂) (mid_sub hst O₂))) n y, ?_, ?_⟩
  · have e1 : inclPair (part_sub hst O₁) hst inter_subset_left inter_subset_left ≫
        relPair (sub_mid O₂) (mid_sub hst O₂) =
        inclPair (part_sub hst O₁) (mid_sub hst O₂)
          (inter_subset_left.trans (sub_mid O₂)) inter_subset_left := by
      ext : 2 <;> rfl
    rw [restr, ← Hmap_comp_apply, e1]
    exact hy
  · have e3 : inclPair (part_sub hst O₂) hst inter_subset_left inter_subset_left ≫
        relPair (sub_mid O₂) (mid_sub hst O₂) =
        inclPair (part_sub hst O₂) (subset_refl (t ∩ O₂)) (part_sub hst O₂) subset_rfl ≫
          inclPair (subset_refl (t ∩ O₂)) (mid_sub hst O₂) subset_union_right
            inter_subset_left := by
      ext : 2 <;> rfl
    rw [restr, ← Hmap_comp_apply, e3, Hmap_comp_apply,
      H_self_eq_zero (t ∩ O₂) n (Hmap _ n y), map_zero]

include hO₁ hO₂ hdis hcov in
/-- The restriction to the part in O₁ is surjective. -/
theorem restr_surjective (n : ℕ) : Function.Surjective (restr hst O₁ n) := fun x₁ => by
  obtain ⟨z, hz, -⟩ := exists_extend hst hO₁ hO₂ hdis hcov n x₁
  exact ⟨z, hz⟩

include hO₁ hO₂ hdis hcov in
/-- Additivity: the two restrictions map the cohomology of (t, s) bijectively onto the product
of the cohomologies of the two parts. -/
theorem restr_bijective (n : ℕ) :
    Function.Bijective ((restr hst O₁ n).prod (restr hst O₂ n)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h := Prod.mk.inj hx
    exact eq_zero_of_restr hst hO₁ hO₂ hdis hcov n x h.1 h.2
  · rintro ⟨x₁, x₂⟩
    obtain ⟨z₁, h11, h12⟩ := exists_extend hst hO₁ hO₂ hdis hcov n x₁
    obtain ⟨z₂, h22, h21⟩ := exists_extend hst hO₂ hO₁ hdis.symm
      (fun x hx => (hcov hx).symm) n x₂
    refine ⟨z₁ + z₂, ?_⟩
    change (restr hst O₁ n (z₁ + z₂), restr hst O₂ n (z₁ + z₂)) = (x₁, x₂)
    rw [map_add, map_add, h11, h12, h21, h22, add_zero, zero_add]

include hO₁ hO₂ hdis hcov in
/-- The cohomology of (t, s) vanishes in a degree in which the cohomologies of both parts
vanish. -/
theorem eq_zero_of_parts (n : ℕ) (h₁ : ∀ x : H (triv (pairOf (part_sub hst O₁))) n, x = 0)
    (h₂ : ∀ x : H (triv (pairOf (part_sub hst O₂))) n, x = 0) (x : H (triv (pairOf hst)) n) :
    x = 0 :=
  eq_zero_of_restr hst hO₁ hO₂ hdis hcov n x (h₁ _) (h₂ _)

end

end Finsler.PairAdditive
