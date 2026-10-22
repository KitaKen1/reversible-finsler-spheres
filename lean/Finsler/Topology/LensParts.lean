module

public import Finsler.Topology.LensLabels

/-! Lens pairs in unions of disjoint open sets. For a continuous function with a descent, cuts
a, b and a time T, the lens pair in the union of two disjoint open sets has the product of the
cohomologies of the lens pairs in the two sets (additivity; no trapping is needed). The lens
pair in the empty set has no cohomology. If every point below b which is not taken below a' in
time T lies in an open set 𝒲, the cohomology of the sublevel of b relative to the sublevel of a
is the cohomology of the lens pair in 𝒲 (𝒲 need not be open for this). So a crossing can be split into the lens pairs of
finitely many pairwise disjoint open sets one set at a time. -/

@[expose] public section

namespace Finsler.LensParts

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation
open Finsler.PairAdditive Finsler.LensLabels

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) {a b T : ℝ}

/-- The part of the lens pair of a union in one of the two sets is the lens pair of that
set. -/
theorem part_bijective (𝒲 𝒱 : Set W) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair
      (part_sub (partY_sub_partU g D (𝒲 ∪ 𝒱) a b T) 𝒲) (partY_sub_partU g D 𝒲 a b T)
      (fun _ hw => ⟨hw.1.1, hw.1.2.1, hw.2⟩) (fun _ hw => ⟨hw.1.1, hw.2⟩))) n) := by
  have hs : partY g D 𝒲 a b T ⊆ partY g D (𝒲 ∪ 𝒱) a b T ∩ 𝒲 :=
    fun _ hw => ⟨⟨hw.1, hw.2.1, Or.inl hw.2.2⟩, hw.2.2⟩
  have ht : partU g 𝒲 b ⊆ partU g (𝒲 ∪ 𝒱) b ∩ 𝒲 := fun _ hw => ⟨⟨hw.1, Or.inl hw.2⟩, hw.2⟩
  exact PairTriple.bijective_Hmap _ (fun k =>
    Finsler.BorelLens.bijective_nativePull_of_eq _ _ _ _ hs ht k) n

theorem part_bijective_right (𝒲 𝒱 : Set W) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair
      (part_sub (partY_sub_partU g D (𝒲 ∪ 𝒱) a b T) 𝒱) (partY_sub_partU g D 𝒱 a b T)
      (fun _ hw => ⟨hw.1.1, hw.1.2.1, hw.2⟩) (fun _ hw => ⟨hw.1.1, hw.2⟩))) n) := by
  have hs : partY g D 𝒱 a b T ⊆ partY g D (𝒲 ∪ 𝒱) a b T ∩ 𝒱 :=
    fun _ hw => ⟨⟨hw.1, hw.2.1, Or.inr hw.2.2⟩, hw.2.2⟩
  have ht : partU g 𝒱 b ⊆ partU g (𝒲 ∪ 𝒱) b ∩ 𝒱 := fun _ hw => ⟨⟨hw.1, Or.inr hw.2⟩, hw.2⟩
  exact PairTriple.bijective_Hmap _ (fun k =>
    Finsler.BorelLens.bijective_nativePull_of_eq _ _ _ _ hs ht k) n

variable {𝒲₁ 𝒲₂ : Set W}

/-- The lens pair in the union of two disjoint open sets has the product of the cohomologies of
the lens pairs in the two sets. -/
def unionEquiv (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂) (n : ℕ) :
    H (triv (pairOf (partY_sub_partU g D (𝒲₁ ∪ 𝒲₂) a b T))) n ≃ₗ[ZMod 2]
      (H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n ×
        H (triv (pairOf (partY_sub_partU g D 𝒲₂ a b T))) n) :=
  (LinearEquiv.ofBijective _ (restr_bijective (partY_sub_partU g D (𝒲₁ ∪ 𝒲₂) a b T) h₁ h₂ hdis
    (fun _ hw => hw.2) n)).trans
    ((LinearEquiv.ofBijective _ (part_bijective D 𝒲₁ 𝒲₂ n)).symm.prodCongr
      (LinearEquiv.ofBijective _ (part_bijective_right D 𝒲₁ 𝒲₂ n)).symm)

/-- The lens pair in the union has no cohomology in a degree in which the lens pairs in the two
sets have none. -/
theorem union_eq_zero (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂) (n : ℕ)
    (z₁ : ∀ x : H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n, x = 0)
    (z₂ : ∀ x : H (triv (pairOf (partY_sub_partU g D 𝒲₂ a b T))) n, x = 0)
    (x : H (triv (pairOf (partY_sub_partU g D (𝒲₁ ∪ 𝒲₂) a b T))) n) : x = 0 := by
  let e := unionEquiv D (a := a) (b := b) (T := T) h₁ h₂ hdis n
  have h0 : e x = 0 := Prod.ext (z₁ _) (z₂ _)
  calc x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm 0 := by rw [h0]
    _ = 0 := e.symm.map_zero

/-- The lens pair in the empty set has no cohomology. -/
theorem empty_eq_zero (n : ℕ)
    (x : H (triv (pairOf (partY_sub_partU g D (∅ : Set W) a b T))) n) : x = 0 := by
  have hb := PairTriple.bijective_Hmap _ (fun k =>
    Finsler.BorelLens.bijective_nativePull_of_eq
      (subset_refl (partU g (∅ : Set W) b)) (partY_sub_partU g D (∅ : Set W) a b T)
      (fun _ hw => absurd hw.2 (Set.notMem_empty _)) subset_rfl
      (partY_sub_partU g D (∅ : Set W) a b T) subset_rfl k) n
  apply hb.1
  rw [map_zero]
  exact H_self_eq_zero _ n _

/-- If every point below b which is not taken below a' in time T lies in the set 𝒲, the
cohomology of the sublevel of b relative to the sublevel of a is the cohomology of the lens
pair in 𝒲. -/
def crossingEquiv {a' : ℝ} {𝒲 : Set W} (hg : Continuous g) (hab : a ≤ b) (ha : a' < a)
    (hT : 0 ≤ T) (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ 𝒲)
    (n : ℕ) :
    H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n ≃ₗ[ZMod 2]
      H (triv (pairOf (partY_sub_partU g D 𝒲 a b T))) n :=
  ((LinearEquiv.ofBijective _ (lens_bijective D hab hT n)).symm.trans
    (LinearEquiv.ofBijective _ (lensN_bijective D hg ha n))).trans
    ((LinearEquiv.ofBijective _ (PairTriple.bijective_Hmap _ (fun k =>
      Finsler.BorelLens.bijective_nativePull_of_eq
        (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
        (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
        inter_subset_left inter_subset_left
        (fun w hw => ⟨hw, htrap w hw.2.1 (le_of_lt hw.1)⟩)
        (fun w hw => ⟨hw, htrap w hw.2 (le_of_lt hw.1)⟩) k) n)).trans
      (LinearEquiv.ofBijective _ (piece_bijective D hg ha 𝒲 n)).symm)

end

end Finsler.LensParts
