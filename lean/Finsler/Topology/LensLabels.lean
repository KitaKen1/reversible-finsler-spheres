module

public import Finsler.Topology.LensContinuation
public import Finsler.Topology.PairAdditive

/-! The decomposition of a crossing into the lens pairs of two disjoint open sets. Let g be a
continuous function with a descent, a' < a ≤ b cuts and T ≥ 0 a time, and let 𝒲₁, 𝒲₂ be disjoint
open sets containing every point below b which the flow does not take below a' in time T. Then
the cohomology of the sublevel of b relative to the sublevel of a is the product of the
cohomologies of the lens pairs in 𝒲₁ and in 𝒲₂,

  ({g < b} ∩ 𝒲ᵢ, {g < b, g ∘ flow_T < a} ∩ 𝒲ᵢ).

The crossing pair has the cohomology of the sublevel relative to the lens set; the points not
taken to energy at most a' form an excision of it, which lies in 𝒲₁ ∪ 𝒲₂ and so splits; and
each part is an excision of the lens pair in 𝒲ᵢ. Consequently every class of a lens pair in 𝒲ᵢ
comes from a class of the crossing pair, and the crossing pair has no cohomology in a degree
in which both lens pairs have none. -/

@[expose] public section

namespace Finsler.LensLabels

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.PairTriple Finsler.FlowLens
open Finsler.LensContinuation Finsler.PairAdditive

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) {a' a b T : ℝ}

/-- The part in an open set of the excised lens pair lies in the lens pair of the open set. -/
theorem piece_sub_partY (𝒲 : Set W) :
    (lensN D a' T ∩ lensY D a b T) ∩ 𝒲 ⊆ partY g D 𝒲 a b T :=
  fun _ hw => ⟨hw.1.2.1, hw.1.2.2, hw.2⟩

theorem piece_sub_partU (𝒲 : Set W) : (lensN D a' T ∩ sub g b) ∩ 𝒲 ⊆ partU g 𝒲 b :=
  fun _ hw => ⟨hw.1.2, hw.2⟩

/-- The part in an open set of the excised lens pair is an excision of the lens pair of the
open set. -/
theorem piece_bijective (hg : Continuous g) (ha : a' < a) (𝒲 : Set W) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair
      (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
      (partY_sub_partU g D 𝒲 a b T) (piece_sub_partY D 𝒲) (piece_sub_partU D 𝒲))) n) := by
  refine bijective_Hmap_excision _ _ _ _ ?_ (lensY D a b T) (lensN D a' T)
    (lensY_isOpen D hg a b T) (lensN_isOpen D hg a' T) ?_ ?_ ?_ n
  · exact fun w hw hw' => ⟨⟨hw.1.1, hw'.1, hw'.2.1⟩, hw.2⟩
  · intro w hw
    by_cases h : g (D.flow T w) < a
    · exact Or.inl ⟨hw.1, h⟩
    · exact Or.inr (lt_of_lt_of_le ha (not_lt.mp h))
  · exact fun w hw => ⟨hw.1.1, hw.1.2, hw.2.2⟩
  · exact fun w hw => ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩

variable {𝒲₁ 𝒲₂ : Set W}

/-- The decomposition of the crossing: the cohomology of the sublevel of b relative to the
sublevel of a is the product of the cohomologies of the lens pairs in 𝒲₁ and 𝒲₂. -/
def labelEquiv (hg : Continuous g) (hab : a ≤ b) (ha : a' < a) (hT : 0 ≤ T)
    (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂)
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ 𝒲₁ ∪ 𝒲₂) (n : ℕ) :
    H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n ≃ₗ[ZMod 2]
      (H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n ×
        H (triv (pairOf (partY_sub_partU g D 𝒲₂ a b T))) n) :=
  (((LinearEquiv.ofBijective _ (lens_bijective D hab hT n)).symm.trans
    (LinearEquiv.ofBijective _ (lensN_bijective D hg ha n))).trans
    (LinearEquiv.ofBijective _ (restr_bijective
      (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) h₁ h₂ hdis
      (fun w hw => htrap w hw.2 (le_of_lt hw.1)) n))).trans
    ((LinearEquiv.ofBijective _ (piece_bijective D hg ha 𝒲₁ n)).symm.prodCongr
      (LinearEquiv.ofBijective _ (piece_bijective D hg ha 𝒲₂ n)).symm)

/-- The crossing pair has no cohomology in a degree in which both lens pairs have none. -/
theorem crossing_eq_zero (hg : Continuous g) (hab : a ≤ b) (ha : a' < a) (hT : 0 ≤ T)
    (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂)
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ 𝒲₁ ∪ 𝒲₂) (n : ℕ)
    (z₁ : ∀ x : H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n, x = 0)
    (z₂ : ∀ x : H (triv (pairOf (partY_sub_partU g D 𝒲₂ a b T))) n, x = 0)
    (x : H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n) :
    x = 0 := by
  let e := labelEquiv D hg hab ha hT h₁ h₂ hdis htrap n
  have h0 : e x = 0 := Prod.ext (z₁ _) (z₂ _)
  calc x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = e.symm 0 := by rw [h0]
    _ = 0 := e.symm.map_zero

/-- Every class of the lens pair in 𝒲₁ is the first component of a class of the crossing
pair. -/
theorem label_surjective (hg : Continuous g) (hab : a ≤ b) (ha : a' < a) (hT : 0 ≤ T)
    (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂)
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ 𝒲₁ ∪ 𝒲₂) (n : ℕ)
    (y : H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n) :
    ∃ x, (labelEquiv D hg hab ha hT h₁ h₂ hdis htrap n x).1 = y :=
  ⟨(labelEquiv D hg hab ha hT h₁ h₂ hdis htrap n).symm (y, 0), by
    rw [LinearEquiv.apply_symm_apply]⟩

/-- The lens pair in 𝒲₁ has finite-dimensional cohomology of at most the dimension of the
cohomology of the crossing pair, when the latter is finite dimensional. -/
theorem finrank_label_le (hg : Continuous g) (hab : a ≤ b) (ha : a' < a) (hT : 0 ≤ T)
    (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂)
    (htrap : ∀ w, g w < b → a' ≤ g (D.flow T w) → w ∈ 𝒲₁ ∪ 𝒲₂) (n : ℕ)
    [Module.Finite (ZMod 2)
      (H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n)] :
    Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n) ≤
      Module.finrank (ZMod 2)
        (H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n) := by
  let e := labelEquiv D hg hab ha hT h₁ h₂ hdis htrap n
  let f : H (triv (pairOf ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)))) n
      →ₗ[ZMod 2] H (triv (pairOf (partY_sub_partU g D 𝒲₁ a b T))) n :=
    (LinearMap.fst (ZMod 2) _ _).comp e.toLinearMap
  have hf : Function.Surjective f := fun y =>
    label_surjective D hg hab ha hT h₁ h₂ hdis htrap n y
  exact LinearMap.finrank_le_finrank_of_surjective hf

end

end Finsler.LensLabels
