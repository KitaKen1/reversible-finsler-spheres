module

public import Finsler.Topology.LensFixed
public import Finsler.Topology.SubspaceK

/-! The splitting of a lens pair into the parts of invariant open sets. Let a space carry two
commuting involutions, Z be an invariant set on which the second involution is the identity, g an
invariant continuous function and D a descent commuting with both involutions and keeping Z. For
cuts a' < a ≤ b, a time T ≥ 0 and pairwise disjoint invariant open sets 𝒲_j containing every point
below b not taken below a' in time T, the pair (sub b, lensY) of the sublevel relative to the lens
set, restricted to Z, and the parts of its excision in the 𝒲_j (and their parts in Z) form a
splitting in the sense of `OrbitAssembly.Split`, once windows of the parts are given: restriction
to the parts is jointly bijective (excision and additivity, also inside Z where the excision is
relative), the second involution is trivial on the parts in Z, and all restrictions commute. -/

@[expose] public section

namespace Finsler.PolySplit

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelDeformation Finsler.BorelIterate Finsler.PairAdditive Finsler.PieceAdditive
open Finsler.FlowLens Finsler.LensContinuation Finsler.LensLabels Finsler.InvPairs
open Finsler.BorelComparison Finsler.PairTriple Finsler.LensK Finsler.LensFixed
open Finsler.FixedLadder Finsler.OrbitAssembly

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Restrictions between pairs of invariant sets compose. -/
theorem gHom_comp {X : TopCat.{0}} (k : KAct X) {s t s' t' s'' t'' : Set X} (hst : s ⊆ t)
    (hs : Inv k s) (ht : Inv k t) (hst' : s' ⊆ t') (hs' : Inv k s') (ht' : Inv k t')
    (hst'' : s'' ⊆ t'') (hs'' : Inv k s'') (ht'' : Inv k t'') (hss : s ⊆ s') (htt : t ⊆ t')
    (hss' : s' ⊆ s'') (htt' : t' ⊆ t'') (j : ℕ) (x : (cochains (pairOf hst'')).X j) :
    (gHom k hst hs ht hst' hs' ht' hss htt).φ.f j
        ((gHom k hst' hs' ht' hst'' hs'' ht'' hss' htt').φ.f j x) =
      (gHom k hst hs ht hst'' hs'' ht'' (hss.trans hss') (htt.trans htt')).φ.f j x := by
  have h := pull_comp_apply (inclPair hst hst' hss htt) (inclPair hst' hst'' hss' htt') j x
  have e : inclPair hst hst' hss htt ≫ inclPair hst' hst'' hss' htt' =
      inclPair hst hst'' (hss.trans hss') (htt.trans htt') := by
    ext : 2 <;> rfl
  rw [e] at h
  exact h.symm

/-- Composition of restrictions on the Borel cohomology of the iterated complexes. -/
theorem HK_gHom_comp {X : TopCat.{0}} (k : KAct X) {s t s' t' s'' t'' : Set X} (hst : s ⊆ t)
    (hs : Inv k s) (ht : Inv k t) (hst' : s' ⊆ t') (hs' : Inv k s') (ht' : Inv k t')
    (hst'' : s'' ⊆ t'') (hs'' : Inv k s'') (ht'' : Inv k t'') (hss : s ⊆ s') (htt : t ⊆ t')
    (hss' : s' ⊆ s'') (htt' : t' ⊆ t'') (q : ℕ) (x : HR (borelInv (gCommuting k hst'' hs'' ht'')) q) :
    HRmap (borelHom (gHom k hst hs ht hst' hs' ht' hss htt)) q
        (HRmap (borelHom (gHom k hst' hs' ht' hst'' hs'' ht'' hss' htt')) q x) =
      HRmap (borelHom (gHom k hst hs ht hst'' hs'' ht'' (hss.trans hss') (htt.trans htt'))) q x := by
  rw [← HRmap_comp]
  exact HRmap_congr (fun j y => by
    apply Subtype.ext
    funext m
    exact gHom_comp k hst hs ht hst' hs' ht' hst'' hs'' ht'' hss htt hss' htt' m _) q x

/-- Composition of restrictions on reflection Borel cohomology. -/
theorem HR_gHom_comp {X : TopCat.{0}} (k : KAct X) {s t s' t' s'' t'' : Set X} (hst : s ⊆ t)
    (hs : Inv k s) (ht : Inv k t) (hst' : s' ⊆ t') (hs' : Inv k s') (ht' : Inv k t')
    (hst'' : s'' ⊆ t'') (hs'' : Inv k s'') (ht'' : Inv k t'') (hss : s ⊆ s') (htt : t ⊆ t')
    (hss' : s' ⊆ s'') (htt' : t' ⊆ t'') (q : ℕ) (x : HR (gComplex k hst'' hs'' ht'') q) :
    HRmap (gHom k hst hs ht hst' hs' ht' hss htt).φ q
        (HRmap (gHom k hst' hs' ht' hst'' hs'' ht'' hss' htt').φ q x) =
      HRmap (gHom k hst hs ht hst'' hs'' ht'' (hss.trans hss') (htt.trans htt')).φ q x := by
  rw [← HRmap_comp]
  exact HRmap_congr (fun j y => gHom_comp k hst hs ht hst' hs' ht' hst'' hs'' ht'' hss htt hss'
    htt' j y) q x

section Split

variable {W : TopCat.{0}} (k : KAct W) {Z : Set W} (hZK : Inv k Z)
  {g : W → ℝ} (hgρ : ∀ w, g (k.ρ w) = g w) (hgσ : ∀ w, g (k.σ w) = g w) (D : Descent W g)
  (hDρ : ∀ t w, D.flow t (k.ρ w) = k.ρ (D.flow t w))
  (hDσ : ∀ t w, D.flow t (k.σ w) = k.σ (D.flow t w)) (a' a b T : ℝ) {J : Type}
  (𝒲 : J → Set W) (h𝒲K : ∀ j, Inv k (𝒲 j))

/-- The pair of the sublevel of b relative to the lens set. -/
abbrev mainS := gCommuting k (lensY_subset D a b T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T)
  (inv_sub k hgρ hgσ b)

/-- Its part in Z. -/
abbrev fixMainS := gCommuting k (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))
  (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK) (inv_inter (inv_sub k hgρ hgσ b) hZK)

/-- Restriction to the part in Z. -/
abbrev mainHom : CommHom (mainS k hgρ hgσ D hDρ hDσ a b T) (fixMainS k hZK hgρ hgσ D hDρ hDσ a b T) :=
  gHom k (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))
    (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK) (inv_inter (inv_sub k hgρ hgσ b) hZK)
    (lensY_subset D a b T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T) (inv_sub k hgρ hgσ b)
    inter_subset_left inter_subset_left

/-- The part of the excised pair in 𝒲 j. -/
abbrev partComplex (j : J) : InvComplex :=
  gComplex k (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) (𝒲 j))
    (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_lensY k hgρ hgσ D hDρ hDσ a b T)) (h𝒲K j))
    (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b)) (h𝒲K j))

/-- The part of the excised pair inside Z in 𝒲 j. -/
abbrev fixPartComplex (j : J) : InvComplex :=
  gComplex k (part_sub (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))) (𝒲 j))
    (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK)) (h𝒲K j))
    (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_sub k hgρ hgσ b) hZK)) (h𝒲K j))

/-- Restriction from the main pair to the part in 𝒲 j. -/
abbrev rMap (j : J) :
    CommHom (mainS k hgρ hgσ D hDρ hDσ a b T) (gCommuting k
      (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) (𝒲 j))
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
        (inv_lensY k hgρ hgσ D hDρ hDσ a b T)) (h𝒲K j))
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b))
        (h𝒲K j))) :=
  gHom k _ _ _ (lensY_subset D a b T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T)
    (inv_sub k hgρ hgσ b) (fun _ hw => hw.1.2) (fun _ hw => hw.1.2)

variable (hg : Continuous g) (ha : a' < a) (h𝒲 : ∀ j, IsOpen (𝒲 j))
  (hdis : Pairwise fun i j => Disjoint (𝒲 i) (𝒲 j))
  (htrap : ∀ w, g w < b → a' < g (D.flow T w) → ∃ j, w ∈ 𝒲 j)

include hg ha h𝒲 hdis htrap in
/-- Restriction to the parts is jointly bijective on K-Borel cohomology. -/
theorem HK_rMap_bijective (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j =>
      HRmap (borelHom (rMap k hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j)) q) := by
  have hexc := HK_lensN_bijective k hgρ hgσ D hDρ hDσ hg ha (b := b) (T := T) q
  have hparts := HK_parts_lens k hgρ hgσ D hDρ hDσ (a' := a') (a := a) (b := b) (T := T) 𝒲 h𝒲K
    h𝒲 hdis htrap q
  have heq : (LinearMap.pi fun j =>
      HRmap (borelHom (rMap k hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j)) q) =
      (LinearMap.pi fun j => HRmap (borelHom (gHom k
        (part_sub (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T)) (𝒲 j))
        (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
          (inv_lensY k hgρ hgσ D hDρ hDσ a b T)) (h𝒲K j))
        (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b))
          (h𝒲K j))
        (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
        (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T))
        (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b))
        inter_subset_left inter_subset_left)) q) ∘ₗ
      HRmap (borelHom (gHom k
        (inter_subset_inter_right (lensN D a' T) (lensY_subset D a b T))
        (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T))
        (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_sub k hgρ hgσ b))
        (lensY_subset D a b T) (inv_lensY k hgρ hgσ D hDρ hDσ a b T) (inv_sub k hgρ hgσ b)
        inter_subset_right inter_subset_right)) q := by
    refine LinearMap.ext fun x => funext fun j => ?_
    exact (HK_gHom_comp k _ _ _ _ _ _ _ _ _ inter_subset_left inter_subset_left
      inter_subset_right inter_subset_right q x).symm
  rw [heq]
  exact hparts.comp hexc

/-- Restriction from the main pair in Z to the part in Z of 𝒲 j. -/
abbrev rhMap (j : J) :
    CommHom (fixMainS k hZK hgρ hgσ D hDρ hDσ a b T) (gCommuting k
      (part_sub (inter_subset_inter_right (lensN D a' T)
        (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))) (𝒲 j))
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
        (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK)) (h𝒲K j))
      (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
        (inv_inter (inv_sub k hgρ hgσ b) hZK)) (h𝒲K j))) :=
  gHom k _ _ _ (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))
    (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK) (inv_inter (inv_sub k hgρ hgσ b) hZK)
    (fun _ hw => hw.1.2) (fun _ hw => hw.1.2)

/-- The excision inside Z. -/
abbrev fixExc :=
  gHom k (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T)))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_inter (inv_sub k hgρ hgσ b) hZK))
    (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))
    (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK) (inv_inter (inv_sub k hgρ hgσ b) hZK)
    inter_subset_right inter_subset_right

/-- The parts inside Z of the excision inside Z. -/
abbrev fixPartOfExc (j : J) :=
  gHom k (part_sub (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T))) (𝒲 j))
    (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK)) (h𝒲K j))
    (inv_inter (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_sub k hgρ hgσ b) hZK)) (h𝒲K j))
    (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T)))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_inter (inv_sub k hgρ hgσ b) hZK))
    inter_subset_left inter_subset_left

include hg ha h𝒲 hdis htrap in
/-- Restriction to the parts inside Z is jointly bijective on K-Borel cohomology. -/
theorem HK_rhMap_bijective (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j =>
      HRmap (borelHom (rhMap k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j)) q) := by
  have hexc : Function.Bijective (HRmap (borelHom
      (fixExc k hZK hgρ hgσ D hDρ hDσ a' a b T)) q) :=
    bijective_gHom k _ _ _ _ _ _ _ _ (fun m => lensN_nativePull_in (Z := Z) D hg ha m) q
  have hparts := InvPairs.HK_parts_bijective k
    (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T)))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_inter (inv_sub k hgρ hgσ b) hZK))
    𝒲 h𝒲K h𝒲 hdis (fun w hw => mem_iUnion.mpr (htrap w hw.2.1 hw.1)) q
  have heq : (LinearMap.pi fun j =>
      HRmap (borelHom (rhMap k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j)) q) =
      (LinearMap.pi fun j => HRmap (borelHom
        (fixPartOfExc k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j)) q) ∘ₗ
      HRmap (borelHom (fixExc k hZK hgρ hgσ D hDρ hDσ a' a b T)) q := by
    refine LinearMap.ext fun x => funext fun j => ?_
    exact (HK_gHom_comp k _ _ _ _ _ _ _ _ _ inter_subset_left inter_subset_left
      inter_subset_right inter_subset_right q x).symm
  rw [heq]
  exact hparts.comp hexc

include hg ha h𝒲 hdis htrap in
/-- Restriction to the parts inside Z is jointly bijective on reflection Borel cohomology. -/
theorem HR_rhMap_bijective (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j =>
      HRmap (rhMap k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j).φ q) := by
  have hexc : Function.Bijective (HRmap (fixExc k hZK hgρ hgσ D hDρ hDσ a' a b T).φ q) :=
    BorelInvariance.bijective_HRmap _ _ _
      (inclPair_restrict k.ρ _ _ _ _ _ _ _ _) (fun m => lensN_nativePull_in (Z := Z) D hg ha m) q
  have hparts := InvPairs.HR_parts_bijective k
    (inter_subset_inter_right (lensN D a' T)
      (lensY_inter_subset (Z := Z) D (a := a) (b := b) (T := T)))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T)
      (inv_inter (inv_lensY k hgρ hgσ D hDρ hDσ a b T) hZK))
    (inv_inter (inv_lensN k hgρ hgσ D hDρ hDσ a' T) (inv_inter (inv_sub k hgρ hgσ b) hZK))
    𝒲 h𝒲K h𝒲 hdis (fun w hw => mem_iUnion.mpr (htrap w hw.2.1 hw.1)) q
  have heq : (LinearMap.pi fun j =>
      HRmap (rhMap k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j).φ q) =
      (LinearMap.pi fun j => HRmap
        (fixPartOfExc k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j).φ q) ∘ₗ
      HRmap (fixExc k hZK hgρ hgσ D hDρ hDσ a' a b T).φ q := by
    refine LinearMap.ext fun x => funext fun j => ?_
    exact (HR_gHom_comp k _ _ _ _ _ _ _ _ _ inter_subset_left inter_subset_left
      inter_subset_right inter_subset_right q x).symm
  rw [heq]
  exact hparts.comp hexc

/-- **The splitting of the pair relative to the lens set into parts.** Given windows of the parts
and of their parts inside Z around the lines through c₀ with slopes in S, the pair of the
sublevel of b relative to the lens set and its part in Z split into the parts of the excision in
the open sets 𝒲 j. -/
def polySplit (hσZ : ∀ x ∈ Z, k.σ x = x) {c₀ A : ℝ} {S : Finset ℝ} (slope : J → ℝ)
    (hslope : ∀ j, slope j ∈ S)
    (hwin : ∀ j (i : ℕ), A < |(i : ℝ) - slope j * c₀| →
      ∀ z : HR (partComplex k hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j) i, z = 0)
    (hwinh : ∀ j (l : ℕ), 2 * A < |2 * (l : ℝ) - slope j * c₀| →
      ∀ z : HR (fixPartComplex k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K j) l, z = 0) :
    Split (mainHom k hZK hgρ hgσ D hDρ hDσ a b T) c₀ A S where
  J := J
  slope := slope
  slope_mem := hslope
  K := partComplex k hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K
  SK _ := gCommuting k _ _ _
  Kh := fixPartComplex k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K
  SKh _ := gCommuting k _ _ _
  triv _ := Finsler.SubspaceK.gCommuting_trivial k _ _ _ fun x hx => hσZ x hx.1.2.2
  ρ _ := gHom k _ _ _ _ _ _ (fun _ hw => ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2⟩)
    (fun _ hw => ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2⟩)
  r := rMap k hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K
  rh := rhMap k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K
  comm _ i x := (gHom_comp k _ _ _ _ _ _ _ _ _ _ _ _ _ i x).trans
    (gHom_comp k _ _ _ _ _ _ _ _ _ _ _ _ _ i x).symm
  bijK := HK_rMap_bijective k hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K hg ha h𝒲 hdis htrap
  bijKh := HK_rhMap_bijective k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K hg ha h𝒲 hdis htrap
  bijR := HR_rhMap_bijective k hZK hgρ hgσ D hDρ hDσ a' a b T 𝒲 h𝒲K hg ha h𝒲 hdis htrap
  win := hwin
  winh := hwinh

end Split

end

end Finsler.PolySplit
