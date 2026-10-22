module

public import Finsler.Topology.BorelFree
public import Finsler.Topology.PairAdditive
public import Finsler.Topology.OrbitAssembly

/-! Additivity of relative cochains over pairwise disjoint open sets. A singular simplex of a space
covered by pairwise disjoint open sets lies in one of them, because the standard simplex is
connected; it is then the image of a unique simplex of that set. Hence, for a pair (t, s) of
subsets of a space and pairwise disjoint open sets O_j covering t, restriction of relative
cochains to the parts (t ∩ O_j, s ∩ O_j) is jointly bijective in every degree: a cochain is
determined by its values on the simplices of the parts, and cochains of the parts glue to a
cochain of t vanishing on the simplices of s. For pairs of sets of loops invariant under the
reversal and the half rotation and invariant open sets O_j, restriction to the parts is therefore
jointly bijective on reflection Borel cohomology and on K-Borel cohomology (`OrbitAssembly`). -/

@[expose] public section

namespace Finsler.PieceAdditive

open CategoryTheory Set Topology SphereOddDegree Convexity
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelDeformation
open Finsler.RelativeCupCochain Finsler.PairAdditive Finsler.BorelIterate Finsler.BorelCoverK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- A singular simplex of a space covered by pairwise disjoint open sets lies in one of them. -/
theorem exists_piece {Y : TopCat.{0}} {J : Type} (U : J → Set Y) (hU : ∀ j, IsOpen (U j))
    (hdis : Pairwise fun i j => Disjoint (U i) (U j)) (hcov : ∀ y, ∃ j, y ∈ U j) (m : ℕ)
    (σ : singularSimplices Y m) :
    ∃ j, ∀ x, Y.toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) σ x ∈ U j := by
  set g := Y.toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) σ
  obtain ⟨j, hj⟩ := hcov (g default)
  refine ⟨j, ?_⟩
  have hclopen : IsClopen (g ⁻¹' U j) := by
    constructor
    · have e : (g ⁻¹' U j)ᶜ = ⋃ k ∈ {k | k ≠ j}, g ⁻¹' U k := by
        ext x
        simp only [mem_compl_iff, mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
        constructor
        · intro hx
          obtain ⟨k, hk⟩ := hcov (g x)
          exact ⟨k, fun h => hx (h ▸ hk), hk⟩
        · rintro ⟨k, hkj, hk⟩ hx
          exact Set.disjoint_left.mp (hdis hkj) hk hx
      rw [← isOpen_compl_iff, e]
      exact isOpen_biUnion fun k _ => (hU k).preimage g.continuous
    · exact (hU j).preimage g.continuous
  rcases isClopen_iff.mp hclopen with h | h
  · exfalso
    have hm : default ∈ g ⁻¹' U j := hj
    rw [h] at hm
    exact hm
  · intro x
    have hm : x ∈ g ⁻¹' U j := by
      rw [h]
      exact mem_univ x
    exact hm

variable {X : TopCat.{0}} {s t : Set X} (hst : s ⊆ t) {J : Type} (O : J → Set X)

/-- The inclusion of the part of (t, s) in O j. -/
abbrev partIncl (j : J) : pairOf (part_sub hst (O j)) ⟶ pairOf hst :=
  inclPair (part_sub hst (O j)) hst inter_subset_left inter_subset_left

/-- The point of t of a simplex. -/
abbrev pt {m : ℕ} (σ : singularSimplices (TopCat.of t) m) (x : StdSimplex ℝ (Fin (m + 1))) : t :=
  (TopCat.of t).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) σ x

/-- A simplex of t lying in O j as a simplex of t ∩ O j. -/
def lift {m : ℕ} (σ : singularSimplices (TopCat.of t) m) (j : J)
    (hj : ∀ x, (pt σ x : X) ∈ O j) : singularSimplices (TopCat.of ↥(t ∩ O j)) m :=
  ((TopCat.of ↥(t ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m))).symm
    ⟨fun x => ⟨(pt σ x : X), (pt σ x).2, hj x⟩, by fun_prop⟩

theorem map_lift {m : ℕ} (σ : singularSimplices (TopCat.of t) m) (j : J)
    (hj : ∀ x, (pt σ x : X) ∈ O j) :
    (TopCat.toSSet.map (TopPair.Hom.fst (partIncl hst O j))).app _ (lift O σ j hj) = σ := by
  apply ((TopCat.of t).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m))).injective
  ext x
  change ((((TopCat.of ↥(t ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)))
    (lift O σ j hj) x : ↥(t ∩ O j)) : X) = (pt σ x : X)
  rw [lift, Equiv.apply_symm_apply]
  rfl

/-- The simplices of a part lie in its open set. -/
theorem map_mem {m : ℕ} (j : J) (τ : singularSimplices (TopCat.of ↥(t ∩ O j)) m)
    (x : StdSimplex ℝ (Fin (m + 1))) :
    (pt ((TopCat.toSSet.map (TopPair.Hom.fst (partIncl hst O j))).app _ τ) x : X) ∈ O j :=
  ((TopCat.of ↥(t ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) τ x).2.2

theorem lift_map {m : ℕ} (j : J) (τ : singularSimplices (TopCat.of ↥(t ∩ O j)) m)
    (hj : ∀ x, (pt ((TopCat.toSSet.map (TopPair.Hom.fst (partIncl hst O j))).app _ τ) x : X) ∈
      O j) :
    lift O ((TopCat.toSSet.map (TopPair.Hom.fst (partIncl hst O j))).app _ τ) j hj = τ := by
  apply ((TopCat.of ↥(t ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m))).injective
  rw [lift, Equiv.apply_symm_apply]
  ext x
  rfl

variable (hO : ∀ j, IsOpen (O j)) (hdis : Pairwise fun i j => Disjoint (O i) (O j))
  (hcov : t ⊆ ⋃ j, O j)

include hO hdis hcov in
/-- Every simplex of t lies in one of the open sets. -/
theorem exists_piece_t {m : ℕ} (σ : singularSimplices (TopCat.of t) m) :
    ∃ j, ∀ x, (pt σ x : X) ∈ O j :=
  exists_piece (Y := TopCat.of t) (fun j => Subtype.val ⁻¹' O j)
    (fun j => (hO j).preimage continuous_subtype_val)
    (fun i j hij => Set.disjoint_left.mpr fun x hi hj => Set.disjoint_left.mp (hdis hij) hi hj)
    (fun y => by
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcov y.2)
      exact ⟨j, hj⟩) m σ

include hdis in
/-- A simplex of t lies in at most one of the open sets. -/
theorem piece_unique {m : ℕ} (σ : singularSimplices (TopCat.of t) m) {j k : J}
    (hj : ∀ x, (pt σ x : X) ∈ O j) (hk : ∀ x, (pt σ x : X) ∈ O k) : j = k := by
  by_contra hne
  exact Set.disjoint_left.mp (hdis hne) (hj default) (hk default)

/-- The value on a simplex of t of the cochain glued from cochains of the parts. -/
def value {m : ℕ} (y : ∀ j, relative (pairOf (part_sub hst (O j))) m)
    (σ : singularSimplices (TopCat.of t) m) : ZMod 2 := by
  classical
  exact if h : ∃ j, ∀ x, (pt σ x : X) ∈ O j then
    cochainEval m (toAmbient _ m (y h.choose)) (lift O σ h.choose h.choose_spec) else 0

include hdis in
theorem value_eq {m : ℕ} (y : ∀ j, relative (pairOf (part_sub hst (O j))) m)
    (σ : singularSimplices (TopCat.of t) m) (k : J) (hk : ∀ x, (pt σ x : X) ∈ O k) :
    value hst O y σ = cochainEval m (toAmbient _ m (y k)) (lift O σ k hk) := by
  classical
  have h : ∃ j, ∀ x, (pt σ x : X) ∈ O j := ⟨k, hk⟩
  have e : h.choose = k := piece_unique O hdis σ h.choose_spec hk
  have key : ∀ (k₁ k₂ : J) (e : k₁ = k₂) (h₁ : ∀ x, (pt σ x : X) ∈ O k₁)
      (h₂ : ∀ x, (pt σ x : X) ∈ O k₂),
      cochainEval m (toAmbient _ m (y k₁)) (lift O σ k₁ h₁) =
        cochainEval m (toAmbient _ m (y k₂)) (lift O σ k₂ h₂) := by
    intro k₁ k₂ e h₁ h₂
    subst e
    rfl
  unfold value
  rw [dite_eq_left h]
  exact key _ _ e _ _

/-- The cochain of t glued from cochains of the parts. -/
def glued {m : ℕ} (y : ∀ j, relative (pairOf (part_sub hst (O j))) m) :
    singularCochainGroup (ZMod 2) (TopCat.of t) m :=
  Limits.Sigma.desc (fun σ : singularSimplices (TopCat.of t) m =>
    ModuleCat.ofHom (value hst O y σ • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2)))

theorem glued_eval {m : ℕ} (y : ∀ j, relative (pairOf (part_sub hst (O j))) m)
    (σ : singularSimplices (TopCat.of t) m) :
    cochainEval m (glued hst O y) σ = value hst O y σ := by
  unfold cochainEval glued
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (Limits.Sigma.ι_comp_desc (fun σ : singularSimplices (TopCat.of t) m =>
      ModuleCat.ofHom (value hst O y σ • (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2))) σ))
    (1 : ZMod 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans (by simp)

include hO hdis hcov in
/-- **Additivity of relative cochains.** For a pair (t, s) and pairwise disjoint open sets O_j
covering t, restriction of relative cochains to the parts (t ∩ O_j, s ∩ O_j) is jointly
bijective in every degree. -/
theorem pullback_pi_bijective (m : ℕ) :
    Function.Bijective (LinearMap.pi fun j => pullback (partIncl hst O j) m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ψ hψ
    apply toAmbient_injective _ m
    rw [map_zero]
    apply cochain_ext
    intro σ
    obtain ⟨j, hj⟩ := exists_piece_t O hO hdis hcov σ
    rw [← map_lift hst O σ j hj, ← cochainPullback_eval, ← toAmbient_pullback]
    have h0 : pullback (partIncl hst O j) m ψ = 0 := congrFun hψ j
    rw [h0, map_zero, cochainEval_zero, cochainEval_zero]
  · intro y
    have hs0 : cochainPullback (pairOf hst).map m (glued hst O y) = 0 := by
      apply cochain_ext
      intro τ
      rw [cochainPullback_eval, glued_eval, cochainEval_zero]
      set σ := (TopCat.toSSet.map (pairOf hst).map).app _ τ
      obtain ⟨j, hj⟩ := exists_piece_t O hO hdis hcov σ
      rw [value_eq hst O hdis y σ j hj]
      -- the lifted simplex lies in s ∩ O j
      have hsj : ∀ x, ((TopCat.of ↥(t ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m))
          (lift O σ j hj) x : X) ∈ s ∩ O j := by
        intro x
        rw [lift, Equiv.apply_symm_apply]
        exact ⟨((TopCat.of s).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) τ x).2, hj x⟩
      set τ' : singularSimplices (TopCat.of ↥(s ∩ O j)) m :=
        ((TopCat.of ↥(s ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m))).symm
          ⟨fun x => ⟨_, hsj x⟩, by fun_prop⟩
      have hτ' : (TopCat.toSSet.map (pairOf (part_sub hst (O j))).map).app _ τ' =
          lift O σ j hj := by
        apply ((TopCat.of ↥(t ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m))).injective
        ext x
        change (((TopCat.of ↥(s ∩ O j)).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) τ' x :
          ↥(s ∩ O j)) : X) = _
        rw [Equiv.apply_symm_apply]
        rfl
      rw [← hτ', ← cochainPullback_eval, restriction_toAmbient, cochainEval_zero]
    obtain ⟨ψ, hψ⟩ := exists_lift (pairOf hst) m (glued hst O y) hs0
    refine ⟨ψ, funext fun j => ?_⟩
    apply toAmbient_injective _ m
    change toAmbient _ m (pullback (partIncl hst O j) m ψ) = toAmbient _ m (y j)
    apply cochain_ext
    intro τ
    rw [toAmbient_pullback, cochainPullback_eval, hψ, glued_eval,
      value_eq hst O hdis y _ j (map_mem hst O j τ), lift_map]

/-! ### Invariant sets of loops -/

variable {n : ℕ}

/-- **Additivity for invariant sets of loops.** For a pair (t, s) of sets of loops invariant under
the reversal and the half rotation and pairwise disjoint invariant open sets O_j covering t,
restriction to the parts is jointly bijective on the cochains, on reflection Borel cohomology
and on K-Borel cohomology. -/
theorem kHom_pi_bijective {s t : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    {J : Type} (O : J → Set (Loops n)) (hOK : ∀ j, KInv (O j)) (hO : ∀ j, IsOpen (O j))
    (hdis : Pairwise fun i j => Disjoint (O i) (O j)) (hcov : t ⊆ ⋃ j, O j) (m : ℕ) :
    Function.Bijective (LinearMap.pi fun j =>
      (kHom (part_sub hst (O j)) (kInv_inter hs (hOK j)) (kInv_inter ht (hOK j)) hst hs ht
        inter_subset_left inter_subset_left).φ.f m) :=
  pullback_pi_bijective hst O hO hdis hcov m

theorem HR_parts_bijective {s t : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    {J : Type} (O : J → Set (Loops n)) (hOK : ∀ j, KInv (O j)) (hO : ∀ j, IsOpen (O j))
    (hdis : Pairwise fun i j => Disjoint (O i) (O j)) (hcov : t ⊆ ⋃ j, O j) (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j => HRmap
      (kHom (part_sub hst (O j)) (kInv_inter hs (hOK j)) (kInv_inter ht (hOK j)) hst hs ht
        inter_subset_left inter_subset_left).φ q) :=
  Finsler.OrbitAssembly.HR_pi_bijective _ (kHom_pi_bijective hst hs ht O hOK hO hdis hcov) q

theorem HK_parts_bijective {s t : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    {J : Type} (O : J → Set (Loops n)) (hOK : ∀ j, KInv (O j)) (hO : ∀ j, IsOpen (O j))
    (hdis : Pairwise fun i j => Disjoint (O i) (O j)) (hcov : t ⊆ ⋃ j, O j) (q : ℕ) :
    Function.Bijective (LinearMap.pi fun j => HRmap (borelHom
      (kHom (part_sub hst (O j)) (kInv_inter hs (hOK j)) (kInv_inter ht (hOK j)) hst hs ht
        inter_subset_left inter_subset_left)) q) :=
  Finsler.OrbitAssembly.HK_pi_bijective _ (kHom_pi_bijective hst hs ht O hOK hO hdis hcov) q

end

end Finsler.PieceAdditive
