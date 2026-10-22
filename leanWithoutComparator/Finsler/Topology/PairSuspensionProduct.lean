module

public import Finsler.Topology.PairSuspension

/-! The suspension isomorphism for products with ℝ^b. The product Z × ℝ^b is homeomorphic to the
b-fold product of Z with the real line (split off the last coordinate), and under this
homeomorphism the points over P correspond to the points over P and the points with a nonzero
vector or base point in O to the open set of the b-fold suspension. Hence, for an open set O,
the cohomology of the points of Z × ℝ^b over P relative to those with nonzero vector or base
point in O is the cohomology of (P, P ∩ O) shifted by b: it has the same dimension in degree
n + b as the latter in degree n, and it vanishes in the degrees below b. -/

@[expose] public section

namespace Finsler.PairSuspensionProduct

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.PairSuspension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {Z : TopCat.{0}}

/-- The product of a space with ℝ^b. -/
abbrev Prd (Z : TopCat.{0}) (b : ℕ) : TopCat.{0} := TopCat.of (Z × (Fin b → ℝ))

/-- Splitting off the last coordinate. -/
def splitLast (Z : TopCat.{0}) (b : ℕ) : (Z × (Fin (b + 1) → ℝ)) ≃ₜ (Z × (Fin b → ℝ)) × ℝ where
  toFun p := ((p.1, fun i => p.2 (Fin.castSucc i)), p.2 (Fin.last b))
  invFun q := (q.1.1, Fin.snoc (α := fun _ => ℝ) q.1.2 q.2)
  left_inv p := by
    refine Prod.ext rfl ?_
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.snoc_last (α := fun _ => ℝ) _ _
    · exact Fin.snoc_castSucc (α := fun _ => ℝ) _ _ j
  right_inv q := by
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · funext j
      exact Fin.snoc_castSucc (α := fun _ => ℝ) _ _ j
    · exact Fin.snoc_last (α := fun _ => ℝ) _ _
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_pi fun i =>
      (continuous_apply (Fin.castSucc i)).comp continuous_snd)).prodMk
      ((continuous_apply (Fin.last b)).comp continuous_snd)
  continuous_invFun :=
    (continuous_fst.comp continuous_fst).prodMk
      (Continuous.finSnoc (A := fun _ => ℝ) (continuous_snd.comp continuous_fst) continuous_snd)

/-- The homeomorphism of Z × ℝ^b with the b-fold product of Z with the real line. -/
def iterHomeo (Z : TopCat.{0}) : (b : ℕ) → (Z × (Fin b → ℝ)) ≃ₜ iterSpace Z b
  | 0 => Homeomorph.prodUnique Z (Fin 0 → ℝ)
  | b + 1 => (splitLast Z b).trans ((iterHomeo Z b).prodCongr (Homeomorph.refl ℝ))

theorem iterHomeo_succ (b : ℕ) (p : Z × (Fin (b + 1) → ℝ)) :
    iterHomeo Z (b + 1) p =
      (iterHomeo Z b (p.1, fun i => p.2 (Fin.castSucc i)), p.2 (Fin.last b)) := rfl

/-- A vector vanishes if its last coordinate and its other coordinates vanish. -/
theorem eq_zero_iff_init_last {b : ℕ} (u : Fin (b + 1) → ℝ) :
    u = 0 ↔ (fun i => u (Fin.castSucc i)) = 0 ∧ u (Fin.last b) = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    funext i
    refine Fin.lastCases h₂ (fun j => ?_) i
    exact congrFun h₁ j

variable (P O : Set Z)

theorem iterHomeo_mem_cyl : ∀ (b : ℕ) (p : Z × (Fin b → ℝ)),
    iterHomeo Z b p ∈ iterCyl P b ↔ p.1 ∈ P
  | 0, _ => Iff.rfl
  | b + 1, p => iterHomeo_mem_cyl b (p.1, fun i => p.2 (Fin.castSucc i))

theorem iterHomeo_mem_open : ∀ (b : ℕ) (p : Z × (Fin b → ℝ)),
    iterHomeo Z b p ∈ iterOpen O b ↔ (p.2 ≠ 0 ∨ p.1 ∈ O)
  | 0, p => by
    constructor
    · exact fun h => Or.inr h
    · rintro (h | h)
      · exact absurd (Subsingleton.elim _ _) h
      · exact h
  | b + 1, p => by
    have ih := iterHomeo_mem_open b (p.1, fun i => p.2 (Fin.castSucc i))
    change (p.2 (Fin.last b) ≠ 0 ∨
      iterHomeo Z b (p.1, fun i => p.2 (Fin.castSucc i)) ∈ iterOpen O b) ↔ _
    rw [ih]
    constructor
    · rintro (h | h | h)
      · exact Or.inl fun h' => h ((eq_zero_iff_init_last p.2).mp h').2
      · exact Or.inl fun h' => h ((eq_zero_iff_init_last p.2).mp h').1
      · exact Or.inr h
    · rintro (h | h)
      · by_cases h2 : p.2 (Fin.last b) = 0
        · exact Or.inr (Or.inl fun h1 => h ((eq_zero_iff_init_last p.2).mpr ⟨h1, h2⟩))
        · exact Or.inl h2
      · exact Or.inr (Or.inr h)

/-- The points of Z × ℝ^b over P. -/
def prodCyl (b : ℕ) : Set (Prd Z b) := {p | p.1 ∈ P}

/-- The points of Z × ℝ^b with nonzero vector or base point in O. -/
def prodOpen (b : ℕ) : Set (Prd Z b) := {p | p.2 ≠ 0 ∨ p.1 ∈ O}

/-- The homeomorphism with the b-fold product is bijective on the cohomology of the pairs. -/
theorem prod_bijective (b n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX
      (inter_subset_left : prodCyl P b ∩ prodOpen O b ⊆ prodCyl P b)
      (inter_subset_left : iterCyl P b ∩ iterOpen O b ⊆ iterCyl P b)
      (restrictMap (X := Prd Z b) (Y := iterSpace Z b) (iterHomeo Z b)
        fun p hp => (iterHomeo_mem_cyl P b p).mpr hp)
      (fun p hp => ⟨(iterHomeo_mem_cyl P b p).mpr hp.1,
        (iterHomeo_mem_open O b p).mpr hp.2⟩))) n) := by
  have h := bijective_Hmap_of_homeomorph (X := Prd Z b) (Y := iterSpace Z b)
    (inter_subset_left : prodCyl P b ∩ prodOpen O b ⊆ prodCyl P b)
    (inter_subset_left : iterCyl P b ∩ iterOpen O b ⊆ iterCyl P b) (iterHomeo Z b)
    (fun p => (iterHomeo_mem_cyl P b p).symm)
    (fun p => ⟨fun hp => ⟨(iterHomeo_mem_cyl P b p).mpr hp.1,
      (iterHomeo_mem_open O b p).mpr hp.2⟩, fun hp => ⟨(iterHomeo_mem_cyl P b p).mp hp.1,
      (iterHomeo_mem_open O b p).mp hp.2⟩⟩) n
  exact h

variable {O}

/-- The suspension isomorphism for the product with ℝ^b. -/
def prodEquiv (hO : IsOpen O) (b n : ℕ) :
    H (triv (pairOf (inter_subset_left : P ∩ O ⊆ P))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_left : prodCyl P b ∩ prodOpen O b ⊆ prodCyl P b)))
        (n + b) :=
  (iterEquiv P hO b n).trans (LinearEquiv.ofBijective _ (prod_bijective P O b (n + b)))

/-- The cohomology of the points of Z × ℝ^b over P relative to those with nonzero vector or
base point in O has in degree n + b the dimension of the cohomology of (P, P ∩ O) in
degree n. -/
theorem finrank_prod (hO : IsOpen O) (b n : ℕ) :
    Module.finrank (ZMod 2)
        (H (triv (pairOf (inter_subset_left :
          prodCyl P b ∩ prodOpen O b ⊆ prodCyl P b))) (n + b)) =
      Module.finrank (ZMod 2) (H (triv (pairOf (inter_subset_left : P ∩ O ⊆ P))) n) :=
  (prodEquiv P hO b n).finrank_eq.symm

/-- It vanishes in the degrees below b. -/
theorem prod_eq_zero (hO : IsOpen O) (b n : ℕ) (hn : n < b)
    (z : H (triv (pairOf (inter_subset_left :
      prodCyl P b ∩ prodOpen O b ⊆ prodCyl P b))) n) : z = 0 := by
  obtain ⟨y, rfl⟩ := (prod_bijective P O b n).2 z
  rw [iter_eq_zero P hO b n hn y, map_zero]

end

end Finsler.PairSuspensionProduct
