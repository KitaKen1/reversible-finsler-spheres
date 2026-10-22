module

public import Finsler.Topology.SubspaceK
public import Finsler.Topology.StripK

/-! Equal-pair transport and inverse pair maps between intrinsic subspace pairs and ambient
intersection pairs, with unchanged ordinary cohomology support cutoffs. -/

@[expose] public section

namespace Finsler.SubspacePairs

open Set CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.BorelComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def equalHEquiv {W : TopCat.{0}} {S T S' T' : Set W} (hs : S = S') (ht : T = T')
    (h : S ⊆ T) (h' : S' ⊆ T') (q : ℕ) :
    H (triv (pairOf h)) q ≃ₗ[ZMod 2] H (triv (pairOf h')) q := by
  subst S'
  subst T'
  exact LinearEquiv.refl _ _

variable {X : TopCat.{0}} (Z : Set X) {S T : Set X} (hST : S ⊆ T)

def intoIntersection (A : Set X) : C(↥(Subtype.val ⁻¹' A : Set Z), ↥(A ∩ Z)) :=
  ⟨fun x => ⟨x.1.1, x.2, x.1.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def fromIntersection (A : Set X) : C(↥(A ∩ Z), ↥(Subtype.val ⁻¹' A : Set Z)) :=
  ⟨fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩,
    (continuous_subtype_val.subtype_mk _).subtype_mk _⟩

def intoPair : pairOf (X := TopCat.of Z) (preimage_mono hST : (Subtype.val ⁻¹' S : Set Z) ⊆ Subtype.val ⁻¹' T) ⟶
    pairOf (inter_subset_inter_left Z hST) :=
  pairMapX _ _ (intoIntersection Z T) fun x hx => ⟨hx, x.1.2⟩

def fromPair : pairOf (inter_subset_inter_left Z hST) ⟶
    pairOf (X := TopCat.of Z) (preimage_mono hST : (Subtype.val ⁻¹' S : Set Z) ⊆ Subtype.val ⁻¹' T) :=
  pairMapX _ _ (fromIntersection Z T) fun _ hx => hx.1

theorem into_from : intoPair Z hST ≫ fromPair Z hST = 𝟙 _ := by
  ext x <;> rfl

theorem from_into : fromPair Z hST ≫ intoPair Z hST = 𝟙 _ := by
  ext x <;> rfl

def insideHEquiv (q : ℕ) :
    H (triv (pairOf (X := TopCat.of Z) (preimage_mono hST : (Subtype.val ⁻¹' S : Set Z) ⊆ Subtype.val ⁻¹' T))) q ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_inter_left Z hST))) q :=
  (ordinaryEquiv _ _ (Category.comp_id _) q).trans
    ((LinearEquiv.ofBijective (nativePull (fromPair Z hST) q)
      (Finsler.StripK.nativePull_bijective_of_inverse (fromPair Z hST) (intoPair Z hST)
        (from_into Z hST) (into_from Z hST) q)).trans
      (ordinaryEquiv _ _ (Category.comp_id _) q).symm)

theorem support_inside (D : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (H (triv (pairOf (inter_subset_inter_left Z hST))) q))
    (hz : ∀ q, D ≤ q → ∀ x : H (triv (pairOf (inter_subset_inter_left Z hST))) q, x = 0) :
    (∀ q, Module.Finite (ZMod 2)
      (H (triv (pairOf (X := TopCat.of Z) (preimage_mono hST : (Subtype.val ⁻¹' S : Set Z) ⊆ Subtype.val ⁻¹' T))) q)) ∧
      ∀ q, D ≤ q → ∀ x :
        H (triv (pairOf (X := TopCat.of Z) (preimage_mono hST : (Subtype.val ⁻¹' S : Set Z) ⊆ Subtype.val ⁻¹' T))) q, x = 0 := by
  constructor
  · intro q
    have := hf q
    exact Module.Finite.equiv (insideHEquiv Z hST q).symm
  · intro q hq x
    exact (insideHEquiv Z hST q).injective
      ((hz q hq ((insideHEquiv Z hST q) x)).trans (insideHEquiv Z hST q).map_zero.symm)

end

end Finsler.SubspacePairs

