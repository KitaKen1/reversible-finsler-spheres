module

public import Finsler.Topology.InvPairs
public import Finsler.Topology.LensLabels

/-! The K-Borel decomposition of a crossing into lens pairs. Let a space carry two commuting
involutions, g be a continuous invariant function and D a descent of g commuting with both. Then
the sublevels, the lens set {g < b, g ∘ flow_T < a}, the set of points not taken below a' in time
T and the lens pairs in invariant sets are invariant. The ordinary isomorphisms of the lens
decomposition are induced by inclusions of these pairs: the crossing pair (sub b, sub a) and the
pair relative to the lens set (the flow deforms), the excision to the points not taken below a',
and the excision of each part to the lens pair of its open set. By the comparison principle they
are isomorphisms on the iterated Borel cohomology, and with additivity over pairwise disjoint
invariant open sets the K-Borel cohomology of the pair relative to the lens set is jointly the
product of the K-Borel cohomology of the parts, each of which is that of the lens pair of its
open set. -/

@[expose] public section

namespace Finsler.LensK

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.PairAdditive Finsler.PieceAdditive
open Finsler.FlowLens Finsler.LensContinuation Finsler.LensLabels Finsler.InvPairs
open Finsler.BorelComparison Finsler.PairTriple

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Bijectivity on the ordinary cohomology of the trivial involutive cochains is bijectivity on
actual relative cohomology. -/
theorem nativePull_bijective_of_Hmap {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ)
    (h : Function.Bijective (Hmap (trivHom f) n)) : Function.Bijective (nativePull f n) := by
  have e : ⇑(nativePull f n) = ⇑(ordinaryEquiv P (𝟙 P) (Category.comp_id _) n) ∘
      ⇑(Hmap (trivHom f) n) ∘ ⇑(ordinaryEquiv Q (𝟙 Q) (Category.comp_id _) n).symm := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, BorelInvariance.Hmap_pullHom,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e]
  exact (ordinaryEquiv P (𝟙 P) _ n).bijective.comp
    (h.comp (ordinaryEquiv Q (𝟙 Q) _ n).symm.bijective)

variable {W : TopCat.{0}} (k : KAct W) {g : W → ℝ} (hgρ : ∀ w, g (k.ρ w) = g w)
  (hgσ : ∀ w, g (k.σ w) = g w) (D : Descent W g)
  (hDρ : ∀ t w, D.flow t (k.ρ w) = k.ρ (D.flow t w))
  (hDσ : ∀ t w, D.flow t (k.σ w) = k.σ (D.flow t w))

include hgρ hgσ in
theorem inv_sub (c : ℝ) : Inv k (sub g c) :=
  ⟨fun w hw => by change g (k.ρ w) < c; rw [hgρ]; exact hw,
    fun w hw => by change g (k.σ w) < c; rw [hgσ]; exact hw⟩

include hgρ hgσ hDρ hDσ in
theorem inv_lensY (a b T : ℝ) : Inv k (lensY D a b T) :=
  ⟨fun w hw => ⟨by rw [hgρ]; exact hw.1, by rw [hDρ, hgρ]; exact hw.2⟩,
    fun w hw => ⟨by rw [hgσ]; exact hw.1, by rw [hDσ, hgσ]; exact hw.2⟩⟩

include hgρ hgσ hDρ hDσ in
theorem inv_lensN (a' T : ℝ) : Inv k (lensN D a' T) :=
  ⟨fun w hw => by change a' < g (D.flow T (k.ρ w)); rw [hDρ, hgρ]; exact hw,
    fun w hw => by change a' < g (D.flow T (k.σ w)); rw [hDσ, hgσ]; exact hw⟩

include hgρ hgσ in
theorem inv_partU {𝒲 : Set W} (h𝒲 : Inv k 𝒲) (b : ℝ) : Inv k (partU g 𝒲 b) :=
  ⟨fun w hw => ⟨by rw [hgρ]; exact hw.1, h𝒲.ρ_mem w hw.2⟩,
    fun w hw => ⟨by rw [hgσ]; exact hw.1, h𝒲.σ_mem w hw.2⟩⟩

include hgρ hgσ hDρ hDσ in
theorem inv_partY {𝒲 : Set W} (h𝒲 : Inv k 𝒲) (a b T : ℝ) : Inv k (partY g D 𝒲 a b T) :=
  ⟨fun w hw => ⟨by rw [hgρ]; exact hw.1, by rw [hDρ, hgρ]; exact hw.2.1, h𝒲.ρ_mem w hw.2.2⟩,
    fun w hw => ⟨by rw [hgσ]; exact hw.1, by rw [hDσ, hgσ]; exact hw.2.1, h𝒲.σ_mem w hw.2.2⟩⟩

include hgρ hgσ hDρ hDσ in
/-- **The crossing and the pair relative to the lens set.** Restriction from the sublevel of b
relative to the lens set to the crossing pair is bijective on K-Borel cohomology. -/
theorem HK_lens_bijective {a b T : ℝ} (hab : a ≤ b) (hT : 0 ≤ T) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k
      ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)) (inv_sub k hgρ hgσ a)
      (inv_sub k hgρ hgσ b) (lensY_subset D a b T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T)
      (inv_sub k hgρ hgσ b) (sub_subset_lensY D hab hT) subset_rfl)) q) :=
  bijective_gHom k _ _ _ _ _ _ _ _ (fun m => bijective_nativePull_inclPair
    ((sub_subset_lensY D hab hT).trans (lensY_subset D a b T)) (lensY_subset D a b T)
    (sub_subset_lensY D hab hT) subset_rfl (lensDeformation D hT) m) q

include hgρ hgσ hDρ hDσ in
/-- **Excision to the points not taken below a'.** -/
theorem HK_lensN_bijective (hg : Continuous g) {a' a b T : ℝ} (ha : a' < a) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k
      (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
      (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T))
      (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b))
      (lensY_subset D a b T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T) (inv_sub k hgρ hgσ b)
      inter_subset_right inter_subset_right)) q) :=
  bijective_gHom k _ _ _ _ _ _ _ _ (fun m => Finsler.BorelLens.bijective_nativePull_excision
    (lensN D a' T) (lensY_subset D a b T) (lensY_isOpen D hg a b T) (lensN_isOpen D hg a' T)
    (fun w hw => by
      by_cases h : g (D.flow T w) < a
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr (lt_of_lt_of_le ha (not_lt.mp h))) m) q

include hgρ hgσ hDρ hDσ in
/-- **Additivity over the open sets.** If every point below b not taken below a' in time T lies
in one of pairwise disjoint invariant open sets, restriction to the parts in them is jointly
bijective on K-Borel cohomology. -/
theorem HK_parts_lens {a' a b T : ℝ} {J : Type} (𝒲 : J → Set W) (h𝒲K : ∀ j, Inv k (𝒲 j))
    (h𝒲 : ∀ j, IsOpen (𝒲 j)) (hdis : Pairwise fun i j => Disjoint (𝒲 i) (𝒲 j))
    (htrap : ∀ w, g w < b → a' < g (D.flow T w) → ∃ j, w ∈ 𝒲 j) (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j => HRmap (borelHom (gHom k
      (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) (𝒲 j))
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
        (inv_lensY k hgρ hgσ D hDρ hDσ a b T)) (h𝒲K j))
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b))
        (h𝒲K j))
      (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
      (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T))
      (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b))
      inter_subset_left inter_subset_left)) q) :=
  HK_parts_bijective k _ _ _ 𝒲 h𝒲K h𝒲 hdis
    (fun w hw => mem_iUnion.mpr (htrap w hw.2 hw.1)) q

include hgρ hgσ hDρ hDσ in
/-- **The parts are the lens pairs.** The part in an invariant open set of the excised lens pair
is an excision of the lens pair of the open set, on K-Borel cohomology. -/
theorem HK_piece_bijective (hg : Continuous g) {a' a b T : ℝ} (ha : a' < a) {𝒲 : Set W}
    (h𝒲K : Inv k 𝒲) (q : ℕ) :
    Function.Bijective (HRmap (borelHom (gHom k
      (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) 𝒲)
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
        (inv_lensY k hgρ hgσ D hDρ hDσ a b T)) h𝒲K)
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b)) h𝒲K)
      (partY_sub_partU g D 𝒲 a b T) (inv_partY k hgρ hgσ D hDρ hDσ h𝒲K a b T)
      (inv_partU k hgρ hgσ h𝒲K b) (piece_sub_partY D 𝒲) (piece_sub_partU D 𝒲))) q) :=
  bijective_gHom k _ _ _ _ _ _ _ _
    (fun m => nativePull_bijective_of_Hmap _ m (piece_bijective D hg ha 𝒲 m)) q

end

end Finsler.LensK
