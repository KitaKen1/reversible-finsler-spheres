module

public import Finsler.Topology.LensK

/-! Lens decompositions inside a set kept by the flow. Excision holds for sets which are only open
relative to the ambient set of the pair. If the flow of a descent keeps a set Z (for instance the
polygons fixed by the half rotation, for an equivariant descent), the time-T map deforms the
sublevel of b inside Z, taking the lens set inside Z into the sublevel of a inside Z; so the
crossing pair inside Z has the cohomology of the sublevel inside Z relative to the lens set inside
Z, its part not taken below a' is an excision, and each part in an open set is an excision of the
lens pair inside Z. Restrictions between pairs of invariant sets compose. -/

@[expose] public section

namespace Finsler.LensFixed

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.PairAdditive Finsler.PieceAdditive
open Finsler.FlowLens Finsler.LensContinuation Finsler.LensLabels Finsler.InvPairs
open Finsler.BorelComparison Finsler.PairTriple Finsler.RelativeCohomology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section General

variable {X : TopCat.{0}} {A B : Set X} (N : Set X) (hAB : A ⊆ B)

/-- Excision for sets open relative to B: for A, N with A ⊆ B ⊆ A ∪ N, A and N ∩ B open in B, the
inclusion (N ∩ B, N ∩ A) → (B, A) is an isomorphism on actual relative cohomology. -/
theorem bijective_nativePull_excision_rel (hA : IsOpen (Subtype.val ⁻¹' A : Set ↥B))
    (hN : IsOpen (Subtype.val ⁻¹' N : Set ↥B)) (hcov : B ⊆ A ∪ N) (k : ℕ) :
    Function.Bijective (nativePull (inclPair (inter_subset_inter_right N hAB) hAB
      inter_subset_right inter_subset_right) k) := by
  have hemb : IsEmbedding (TopPair.Hom.fst (inclPair (inter_subset_inter_right N hAB) hAB
      inter_subset_right inter_subset_right)) :=
    IsEmbedding.inclusion inter_subset_right
  refine Finsler.BorelExcision.bijective_nativePull_of_homology _ k
    (TopPair.isIso_singularHomologyMap_of_open_cover coeff _ hemb ?_
      (fun i : Bool => bif i then (Subtype.val ⁻¹' A : Set ↥B)
        else (Subtype.val ⁻¹' N : Set ↥B)) ?_ ?_ ?_ k)
  · rintro x ⟨y, hy⟩
    have h : y.1 = x.1 := congrArg Subtype.val hy
    exact ⟨(⟨x.1, x.2.1, h ▸ y.2⟩ : ↥(N ∩ A)), Subtype.ext rfl⟩
  · rintro (_ | _)
    · exact hN
    · exact hA
  · apply eq_univ_of_forall
    rintro ⟨x, hx⟩
    rcases hcov hx with h | h
    · exact mem_iUnion.mpr ⟨true, h⟩
    · exact mem_iUnion.mpr ⟨false, h⟩
  · rintro (_ | _)
    · right
      rintro ⟨x, hx⟩ hxN
      exact ⟨(⟨x, hxN, hx⟩ : ↥(N ∩ B)), Subtype.ext rfl⟩
    · left
      rintro ⟨x, hx⟩ hxA
      exact ⟨(⟨x, hxA⟩ : ↥A), Subtype.ext rfl⟩

end General

section Flow

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) {Z : Set W}
  (hZ : ∀ s (w : W), 0 ≤ s → w ∈ Z → D.flow s w ∈ Z)

include hZ in
/-- The time-T map deforms the sublevel of b inside Z, taking the lens set inside Z into the
sublevel of a inside Z. -/
def lensDeformationIn {a b T : ℝ} (hT : 0 ≤ T) :
    PairDeformation (sub g a ∩ Z) (sub g b ∩ Z) (lensY D a b T ∩ Z) (sub g b ∩ Z) where
  r := ⟨fun w => ⟨D.flow T w, Set.mem_inter (sub_flow D b T w hT w.2.1) (hZ T w hT w.2.2)⟩,
    ((flow_continuous D T).comp continuous_subtype_val).subtype_mk _⟩
  H := flowHomotopy D (u := sub g b ∩ Z) T hT fun s w hs hw =>
    Set.mem_inter (sub_flow D b s w hs hw.1) (hZ s w hs hw.2)
  r_mem w := Set.mem_inter (sub_flow D b T w hT w.2.1) (hZ T w hT w.2.2)
  r_sub w hw := Set.mem_inter hw.1.2 (hZ T w hT w.2.2)
  keep_sub' τ w hw := Set.mem_inter (lensY_flow D hT _ w (mul_nonneg τ.2.1 hT) hw.1)
    (hZ _ w (mul_nonneg τ.2.1 hT) hw.2)
  keep τ w hw := Set.mem_inter (sub_flow D b _ w (mul_nonneg τ.2.1 hT) hw.1)
    (hZ _ w (mul_nonneg τ.2.1 hT) hw.2)
  keep_sub τ w hw := Set.mem_inter (sub_flow D a _ w (mul_nonneg τ.2.1 hT) hw.1)
    (hZ _ w (mul_nonneg τ.2.1 hT) hw.2)

theorem sub_inter_subset_lensY {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T) :
    sub g a ∩ Z ⊆ lensY D a b T ∩ Z :=
  fun _ hw => ⟨sub_subset_lensY D hab hT hw.1, hw.2⟩

theorem lensY_inter_subset {a b T : ℝ} : lensY D a b T ∩ Z ⊆ sub g b ∩ Z :=
  fun _ hw => ⟨lensY_subset D a b T hw.1, hw.2⟩

include hZ in
/-- The crossing pair inside Z and the pair relative to the lens set inside Z. -/
theorem lens_nativePull_in {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T) (k : ℕ) :
    Function.Bijective (nativePull (inclPair
      ((sub_inter_subset_lensY (Z := Z) D hab hT).trans (lensY_inter_subset (Z := Z) D))
      (lensY_inter_subset (Z := Z) D) (sub_inter_subset_lensY (Z := Z) D hab hT) subset_rfl) k) :=
  bijective_nativePull_inclPair _ _ _ _ (lensDeformationIn D hZ hT) k

/-- Excision to the points not taken below a', inside Z. -/
theorem lensN_nativePull_in (hg : Continuous g) {a' a b T : ℝ} (ha : a' < a) (k : ℕ) :
    Function.Bijective (nativePull (inclPair
      (inter_subset_inter_right (lensN D a' T) (lensY_inter_subset (Z := Z) D (a := a) (b := b)
        (T := T)))
      (lensY_inter_subset (Z := Z) D) inter_subset_right inter_subset_right) k) :=
  bijective_nativePull_excision_rel (lensN D a' T) (lensY_inter_subset (Z := Z) D)
    (by
      have e : (Subtype.val ⁻¹' (lensY D a b T ∩ Z) : Set ↥(sub g b ∩ Z)) =
          Subtype.val ⁻¹' lensY D a b T := by
        ext w
        exact ⟨fun h => h.1, fun h => ⟨h, w.2.2⟩⟩
      rw [e]
      exact (lensY_isOpen D hg a b T).preimage continuous_subtype_val)
    ((lensN_isOpen D hg a' T).preimage continuous_subtype_val)
    (fun w hw => by
      by_cases h : g (D.flow T w) < a
      · exact Or.inl ⟨⟨hw.1, h⟩, hw.2⟩
      · exact Or.inr (lt_of_lt_of_le ha (not_lt.mp h))) k

end Flow

end

end Finsler.LensFixed
