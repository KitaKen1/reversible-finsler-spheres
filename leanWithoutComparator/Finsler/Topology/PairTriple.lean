module

public import Finsler.Topology.BorelLens
public import Finsler.Topology.OrdinaryDelta
public import Finsler.Topology.OrdinaryExact

/-! Ordinary F₂ cohomology of pairs of subsets: triples, trivial pairs, maps between pairs in
different spaces, and excision for traces of open sets. The relative cochains of a pair with the
identity as involution form an involutive complex whose ordinary cohomology is the actual
relative cohomology. For nested subsets s ⊆ t ⊆ u the cochains of (u, t), (u, s) and (t, s) form
a degreewise short exact sequence, so there is a connecting map from the cohomology of (t, s) to
that of (u, t); it is bijective in the degrees where the cohomology of (u, s) vanishes, and the
cohomology of (u, t) vanishes in degree zero if that of (u, s) does. The relative cochains of a
pair (t, t) vanish. A continuous map between subsets of two spaces which maps a subset into a
subset is a map of pairs, and a homotopy through such maps is a homotopy of maps of pairs. The
inclusion (t, s) → (t', s') is an isomorphism on cohomology if s is the trace of s' on t and t'
is covered by two open sets whose traces lie in s' and in t. A homeomorphism under which two
pairs correspond is an isomorphism on cohomology, and the map from the cohomology of (u, t) to
that of (u, s) is bijective where the cohomology of (t, s) vanishes. -/

@[expose] public section

namespace Finsler.PairTriple

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelExact
open Finsler.BorelLoop Finsler.BorelCrossing Finsler.BorelComparison Finsler.RelativeCohomology
open Finsler.RelativeCupCochain Finsler.BorelDeformation Finsler.SphereTopClass SphereOddDegree

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The relative cochains of a pair with the identity as involution. -/
abbrev triv (P : TopPair.{0}) : InvComplex := ofPair P (𝟙 P) (Category.comp_id _)

/-- The pullback of relative cochains along a map of pairs. -/
abbrev trivHom {P Q : TopPair.{0}} (f : P ⟶ Q) : InvHom (triv Q) (triv P) :=
  pullHom (Category.comp_id _) (Category.comp_id _) f
    ((Category.comp_id f).trans (Category.id_comp f).symm)

/-- A map of pairs which is bijective on actual relative cohomology is bijective on the
ordinary cohomology of the relative cochains. -/
theorem bijective_Hmap {P Q : TopPair.{0}} (f : P ⟶ Q)
    (h : ∀ n, Function.Bijective (nativePull f n)) (n : ℕ) :
    Function.Bijective (Hmap (trivHom f) n) :=
  BorelInvariance.bijective_Hmap _ _ f _ h n

section Triple

variable {X : TopCat.{0}} {s t u : Set X} (hst : s ⊆ t) (htu : t ⊆ u)

/-- The relative cochains of (u, t), (u, s) and (t, s) form a degreewise short exact
sequence. -/
theorem tripleExact :
    ShortExact (trivHom (relPair hst htu)) (trivHom (incPair hst htu)) where
  inj j := rel_injective hst htu j
  surj j := inc_surjective hst htu j
  zero j z := rel_inc_zero hst htu j z
  exact j x hx := inc_exact hst htu j x hx

/-- The connecting map from the cohomology of (t, s) to that of (u, t). -/
abbrev tripleDelta (n : ℕ) :
    H (triv (pairOf hst)) n →ₗ[ZMod 2] H (triv (pairOf htu)) (n + 1) :=
  OrdinaryDelta.delta (tripleExact hst htu) n

/-- Where the cohomology of (u, s) vanishes in two consecutive degrees, the connecting map of
the triple is bijective. -/
theorem tripleDelta_bijective (n : ℕ)
    (h₀ : ∀ x : H (triv (pairOf (hst.trans htu))) n, x = 0)
    (h₁ : ∀ x : H (triv (pairOf (hst.trans htu))) (n + 1), x = 0) :
    Function.Bijective (tripleDelta hst htu n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := OrdinaryDelta.exact_delta (tripleExact hst htu) n y hy
    rw [h₀ x, map_zero]
  · intro z
    exact OrdinaryDelta.exact_sub (tripleExact hst htu) n z (h₁ _)

/-- If the cohomology of (u, s) vanishes in degree zero, so does that of (u, t). -/
theorem triple_zero (h₀ : ∀ x : H (triv (pairOf (hst.trans htu))) 0, x = 0)
    (z : H (triv (pairOf htu)) 0) : z = 0 := by
  apply OrdinaryExact.sub_injective_zero (tripleExact hst htu)
  rw [h₀ (Hmap (trivHom (relPair hst htu)) 0 z), map_zero]

/-- If the cohomology of (t, s) vanishes in the degree n and in the degree before it, the map
from the cohomology of (u, t) to that of (u, s) is bijective in degree n. -/
theorem rel_bijective (n : ℕ) (h₀ : ∀ x : H (triv (pairOf hst)) n, x = 0)
    (h₁ : ∀ m, m + 1 = n → ∀ x : H (triv (pairOf hst)) m, x = 0) :
    Function.Bijective (Hmap (trivHom (relPair hst htu)) n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    cases n with
    | zero =>
      exact OrdinaryExact.sub_injective_zero (tripleExact hst htu) (hz.trans (map_zero _).symm)
    | succ m =>
      obtain ⟨y, rfl⟩ := OrdinaryDelta.exact_sub (tripleExact hst htu) m z hz
      rw [h₁ m rfl y, map_zero]
  · intro x
    exact exact_mid_ordinary (tripleExact hst htu) n x (h₀ _)

end Triple

section Self

variable {X : TopCat.{0}} (t : Set X)

/-- The relative cochains of the pair (t, t) vanish. -/
theorem relative_self_eq_zero (j : ℕ) (ψ : relative (pairOf (subset_refl t)) j) : ψ = 0 := by
  apply toAmbient_injective (pairOf (subset_refl t)) j
  have h : cochainPullback (𝟙 (TopCat.of ↥t)) j (toAmbient (pairOf (subset_refl t)) j ψ) = 0 :=
    restriction_toAmbient (pairOf (subset_refl t)) j ψ
  rw [cochain_id] at h
  rw [h, map_zero]

/-- The cohomology of the pair (t, t) vanishes. -/
theorem H_self_eq_zero (n : ℕ) (x : H (triv (pairOf (subset_refl t))) n) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hc : c = 0 := Subtype.ext (relative_self_eq_zero t n c.1)
  rw [hc, Submodule.Quotient.mk_zero]

end Self

section Maps

variable {X Y : TopCat.{0}}

/-- A continuous map between subsets of two spaces which maps a subset into a subset, as a map
of pairs. -/
def pairMapX {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t) (hst' : s' ⊆ t')
    (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s') : pairOf hst ⟶ pairOf hst' :=
  TopPair.ofHom (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x ↦ ⟨g ⟨x, hst x.2⟩, hg _ x.2⟩, by fun_prop⟩)

theorem pairMapX_comp {Z : TopCat.{0}} {s t : Set X} {s' t' : Set Y} {s'' t'' : Set Z}
    (hst : s ⊆ t) (hst' : s' ⊆ t') (hst'' : s'' ⊆ t'') (g : C(t, t')) (g' : C(t', t''))
    (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (hg' : ∀ x : t', (x : Y) ∈ s' → (g' x : Z) ∈ s'') :
    pairMapX hst hst'' (g'.comp g) (fun x hx ↦ hg' (g x) (hg x hx)) =
      pairMapX hst hst' g hg ≫ pairMapX hst' hst'' g' hg' := by
  ext : 2 <;> rfl

theorem pairMapX_id {s t : Set X} (hst : s ⊆ t) :
    pairMapX hst hst (ContinuousMap.id t) (fun _ hx ↦ hx) = 𝟙 (pairOf hst) := by
  ext : 2 <;> rfl

theorem pairMapX_congr {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t) (hst' : s' ⊆ t')
    {g g' : C(t, t')} (h : g = g') (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (hg' : ∀ x : t, (x : X) ∈ s → (g' x : Y) ∈ s') :
    pairMapX hst hst' g hg = pairMapX hst hst' g' hg' := by
  subst h
  rfl

/-- A homotopy between maps t → t' which keeps s inside s' at all times, as a homotopy between
the maps of pairs. -/
def pairHomotopyX {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t) (hst' : s' ⊆ t')
    {g₀ g₁ : C(t, t')} (F : g₀.Homotopy g₁)
    (hF : ∀ (τ : unitInterval) (x : t), (x : X) ∈ s → (F (τ, x) : Y) ∈ s') :
    TopPair.Homotopy (pairMapX hst hst' g₀ fun x hx ↦ F.apply_zero x ▸ hF 0 x hx)
      (pairMapX hst hst' g₁ fun x hx ↦ F.apply_one x ▸ hF 1 x hx) where
  fst := F
  snd :=
    { toFun (p : unitInterval × s) := ⟨F (p.1, ⟨p.2.1, hst p.2.2⟩), hF p.1 _ p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (congrArg Subtype.val (F.apply_zero ⟨x.1, hst x.2⟩) :)
      map_one_left x := Subtype.ext (congrArg Subtype.val (F.apply_one ⟨x.1, hst x.2⟩) :) }

/-- Maps of pairs p : (t, s) → (t', s') and i : (t', s') → (t, s) with p ∘ i the identity and
i ∘ p homotopic to the identity through maps keeping s: then p is bijective on cohomology. -/
theorem bijective_Hmap_of_section {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t) (hst' : s' ⊆ t')
    (p : C(t, t')) (i : C(t', t)) (hp : ∀ x : t, (x : X) ∈ s → (p x : Y) ∈ s')
    (hi : ∀ x : t', (x : Y) ∈ s' → (i x : X) ∈ s) (hpi : p.comp i = ContinuousMap.id t')
    (F : (i.comp p).Homotopy (ContinuousMap.id t))
    (hF : ∀ (τ : unitInterval) (x : t), (x : X) ∈ s → (F (τ, x) : X) ∈ s) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX hst hst' p hp)) n) := by
  refine bijective_Hmap _ (fun k => ?_) n
  have e1 : pairMapX hst hst' p hp ≫ pairMapX hst' hst i hi =
      pairMapX hst hst (i.comp p) (fun x hx ↦ F.apply_zero x ▸ hF 0 x hx) :=
    (pairMapX_comp hst hst' hst p i hp hi).symm
  have e2 : 𝟙 (pairOf hst) =
      pairMapX hst hst (ContinuousMap.id t) (fun x hx ↦ F.apply_one x ▸ hF 1 x hx) :=
    (pairMapX_id hst).symm
  have H₁ : TopPair.Homotopy (pairMapX hst hst' p hp ≫ pairMapX hst' hst i hi)
      (𝟙 (pairOf hst)) := by
    rw [e1, e2]
    exact pairHomotopyX hst hst F hF
  have e3 : pairMapX hst' hst i hi ≫ pairMapX hst hst' p hp = 𝟙 (pairOf hst') :=
    ((pairMapX_comp hst' hst hst' i p hi hp).symm.trans
      (pairMapX_congr hst' hst' hpi _ (fun _ hx ↦ hx))).trans (pairMapX_id hst')
  have H₂ : TopPair.Homotopy (pairMapX hst' hst i hi ≫ pairMapX hst hst' p hp)
      (𝟙 (pairOf hst')) := by
    rw [e3, ← pairMapX_id hst']
    exact pairHomotopyX hst' hst' (ContinuousMap.Homotopy.refl (ContinuousMap.id t'))
      (fun _ _ hx ↦ hx)
  exact BorelInvariance.bijective_nativePull_of_homotopyEquiv _ _ H₁ H₂ k

/-- The restriction of a homeomorphism to a subset mapped into a subset. -/
def restrictMap {t : Set X} {t' : Set Y} (e : X ≃ₜ Y) (ht : ∀ x, x ∈ t → e x ∈ t') : C(t, t') :=
  ⟨fun x => ⟨e x, ht _ x.2⟩, (e.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- A homeomorphism of spaces under which two pairs of subsets correspond is bijective on
cohomology. -/
theorem bijective_Hmap_of_homeomorph {s t : Set X} {s' t' : Set Y} (hst : s ⊆ t)
    (hst' : s' ⊆ t') (e : X ≃ₜ Y) (ht : ∀ x, x ∈ t ↔ e x ∈ t') (hs : ∀ x, x ∈ s ↔ e x ∈ s')
    (n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX hst hst'
      (restrictMap e fun x hx => (ht x).mp hx) (fun _ hx => (hs _).mp hx))) n) := by
  have ht' : ∀ y, y ∈ t' → e.symm y ∈ t := fun y hy =>
    (ht _).mpr ((e.apply_symm_apply y).symm ▸ hy)
  have hs' : ∀ y : t', (y : Y) ∈ s' → (restrictMap e.symm ht' y : X) ∈ s := fun y hy =>
    (hs _).mpr ((e.apply_symm_apply (y : Y)).symm ▸ hy)
  let p : C(t, t') := restrictMap e fun x hx => (ht x).mp hx
  let i : C(t', t) := restrictMap e.symm ht'
  let F : (i.comp p).Homotopy (ContinuousMap.id t) :=
    { toFun := fun q => q.2
      continuous_toFun := continuous_snd
      map_zero_left := fun x => Subtype.ext (e.symm_apply_apply (x : X)).symm
      map_one_left := fun _ => rfl }
  have hpi : p.comp i = ContinuousMap.id t' := by
    ext y
    exact e.apply_symm_apply (y : Y)
  exact bijective_Hmap_of_section hst hst' p i (fun _ hx => (hs _).mp hx) hs' hpi F
    (fun _ _ hx => hx) n

end Maps

section Excision

variable {X : TopCat.{0}} {s t s' t' : Set X} (hst : s ⊆ t) (hst' : s' ⊆ t') (hss : s ⊆ s')
  (htt : t ⊆ t')

/-- Excision: if s is the trace of s' on t and t' is covered by two open sets whose traces on
t' lie in s' and in t, the inclusion (t, s) → (t', s') is bijective on cohomology. -/
theorem bijective_Hmap_excision (hpre : ∀ x, x ∈ t → x ∈ s' → x ∈ s) (O₁ O₂ : Set X)
    (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂) (hcov : t' ⊆ O₁ ∪ O₂) (h₁ : O₁ ∩ t' ⊆ s')
    (h₂ : O₂ ∩ t' ⊆ t) (n : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair hst hst' hss htt)) n) := by
  refine bijective_Hmap _ (fun k => ?_) n
  have hemb : IsEmbedding (TopPair.Hom.fst (inclPair hst hst' hss htt)) :=
    IsEmbedding.inclusion htt
  refine BorelExcision.bijective_nativePull_of_homology _ k
    (TopPair.isIso_singularHomologyMap_of_open_cover coeff _ hemb ?_
      (fun i : Bool => bif i then (Subtype.val ⁻¹' O₂ : Set ↥t')
        else (Subtype.val ⁻¹' O₁ : Set ↥t')) ?_ ?_ ?_ k)
  · rintro x ⟨y, hy⟩
    have h : y.1 = x.1 := congrArg Subtype.val hy
    exact ⟨(⟨x.1, hpre _ x.2 (h ▸ y.2)⟩ : ↥s), Subtype.ext rfl⟩
  · rintro (_ | _)
    · exact hO₁.preimage continuous_subtype_val
    · exact hO₂.preimage continuous_subtype_val
  · apply eq_univ_of_forall
    rintro ⟨x, hx⟩
    rcases hcov hx with h | h
    · exact mem_iUnion.mpr ⟨false, h⟩
    · exact mem_iUnion.mpr ⟨true, h⟩
  · rintro (_ | _)
    · left
      rintro ⟨x, hx⟩ hxO
      exact ⟨(⟨x, h₁ ⟨hxO, hx⟩⟩ : ↥s'), Subtype.ext rfl⟩
    · right
      rintro ⟨x, hx⟩ hxO
      exact ⟨(⟨x, h₂ ⟨hxO, hx⟩⟩ : ↥t), Subtype.ext rfl⟩

end Excision

end

end Finsler.PairTriple
