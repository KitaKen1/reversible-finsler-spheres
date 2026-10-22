module

public import Finsler.Topology.BorelLens
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.Reduced
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.RingTheory.Finiteness.Finsupp

/-! Tame homology. A space is tame of bound k if its mod 2 singular homology is finite
dimensional in every degree and vanishes from degree k on. The middle term of an exact sequence
of F₂-vector spaces is finite dimensional, respectively zero, if the outer terms are. With the
long exact sequence of a pair and excision this gives: if A and C are open, A and C ∩ A are tame
of bound m and C ∩ (A ∪ C) is tame of bound 1, then A ∪ C is tame of bound m + 1. A convex
subset of a real normed space is tame of bound 1 (it is empty or contractible), so every finite
union of convex open sets is tame; between a compact set and an open set containing it there is
such a union. Homotopic maps induce the same map on homology, a map with a left homotopy inverse
is injective on homology, and a space is tame if some map from it which is injective on homology
factors through a tame space. -/

@[expose] public section

namespace Finsler.TameHomology

open CategoryTheory Limits Set Topology AlgebraicTopology
open Finsler.RelativeCohomology Finsler.BorelLoop Finsler.BorelDeformation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### Exact sequences of vector spaces over F₂ -/

/-- The middle term of an exact sequence of F₂-vector spaces with finite-dimensional outer
terms is finite dimensional. -/
theorem finite_of_exact_linear {A B C : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module (ZMod 2) A] [Module (ZMod 2) B] [Module (ZMod 2) C]
    (f : A →ₗ[ZMod 2] B) (g : B →ₗ[ZMod 2] C) (h : ∀ b, g b = 0 → ∃ a, f a = b)
    [Module.Finite (ZMod 2) A] [Module.Finite (ZMod 2) C] : Module.Finite (ZMod 2) B := by
  have hker : LinearMap.ker g ≤ LinearMap.range f := fun b hb => h b hb
  have : Module.Finite (ZMod 2) (LinearMap.ker g) :=
    Module.Finite.of_injective (Submodule.inclusion hker) (Submodule.inclusion_injective hker)
  have : Module.Finite (ZMod 2) (B ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem finite_of_exact (S : ShortComplex (ModuleCat.{0} (ZMod 2))) (hS : S.Exact)
    (h₁ : Module.Finite (ZMod 2) S.X₁) (h₃ : Module.Finite (ZMod 2) S.X₃) :
    Module.Finite (ZMod 2) S.X₂ :=
  finite_of_exact_linear S.f.hom S.g.hom ((ShortComplex.moduleCat_exact_iff S).mp hS)

theorem isZero_of_exact (S : ShortComplex (ModuleCat.{0} (ZMod 2))) (hS : S.Exact)
    (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ :=
  hS.isZero_of_both_zeros (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

theorem finite_of_isZero {A : ModuleCat.{0} (ZMod 2)} (h : IsZero A) :
    Module.Finite (ZMod 2) A := by
  have : Subsingleton A := ModuleCat.subsingleton_of_isZero h
  infer_instance

theorem finite_of_epi {A B : ModuleCat.{0} (ZMod 2)} (f : A ⟶ B) [Epi f]
    (h : Module.Finite (ZMod 2) A) : Module.Finite (ZMod 2) B :=
  Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)

theorem finite_of_mono {A B : ModuleCat.{0} (ZMod 2)} (f : A ⟶ B) [Mono f]
    (h : Module.Finite (ZMod 2) B) : Module.Finite (ZMod 2) A :=
  Module.Finite.of_injective f.hom ((ModuleCat.mono_iff_injective f).mp inferInstance)

/-! ### Tame spaces -/

/-- The mod 2 singular homology of a space. -/
abbrev Hq (X : TopCat.{0}) (q : ℕ) : ModuleCat.{0} (ZMod 2) :=
  ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).obj X

/-- The map induced on mod 2 singular homology. -/
abbrev HqMap {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ) : Hq X q ⟶ Hq Y q :=
  ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).map f

/-- The relative mod 2 singular homology of a pair. -/
abbrev Hrel (P : TopPair.{0}) (q : ℕ) : ModuleCat.{0} (ZMod 2) := P.singularHomology coeff q

/-- A space is tame of bound k if its mod 2 singular homology is finite dimensional in every
degree and vanishes from degree k on. -/
structure Tame (X : TopCat.{0}) (k : ℕ) : Prop where
  finite : ∀ q, Module.Finite (ZMod 2) (Hq X q)
  zero : ∀ q, k ≤ q → IsZero (Hq X q)

theorem tame_mono {X : TopCat.{0}} {k k' : ℕ} (h : Tame X k) (hk : k ≤ k') : Tame X k' :=
  ⟨h.finite, fun q hq => h.zero q (hk.trans hq)⟩

theorem HqMap_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    HqMap (f ≫ g) q = HqMap f q ≫ HqMap g q :=
  Functor.map_comp _ f g

theorem HqMap_id (X : TopCat.{0}) (q : ℕ) : HqMap (𝟙 X) q = 𝟙 (Hq X q) :=
  CategoryTheory.Functor.map_id _ X

/-- Homotopic maps induce the same map on homology. -/
theorem HqMap_congr {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (q : ℕ) :
    HqMap f q = HqMap g q :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H coeff q

/-- A map with a left homotopy inverse is injective on homology. -/
theorem injective_of_leftInverse {X Y : TopCat.{0}} (i : X ⟶ Y) (r : Y ⟶ X)
    (H : TopCat.Homotopy (i ≫ r) (𝟙 X)) (q : ℕ) : Function.Injective (HqMap i q).hom := by
  have h : HqMap i q ≫ HqMap r q = 𝟙 (Hq X q) := by
    rw [← HqMap_comp, HqMap_congr H, HqMap_id]
  have hx : ∀ x : Hq X q, (HqMap r q).hom ((HqMap i q).hom x) = x := fun x =>
    congrArg (fun φ : Hq X q ⟶ Hq X q => φ.hom x) h
  intro x y hxy
  rw [← hx x, ← hx y, hxy]

/-- A space is tame if some map from it which is injective on homology factors through a tame
space. -/
theorem tame_of_factor {X Q Y : TopCat.{0}} (f : X ⟶ Q) (g : Q ⟶ Y) {k : ℕ} (hQ : Tame Q k)
    (hinj : ∀ q, Function.Injective (HqMap (f ≫ g) q).hom) : Tame X k := by
  have hf : ∀ q, Function.Injective (HqMap f q).hom := by
    intro q x y hxy
    apply hinj q
    rw [HqMap_comp]
    exact congrArg (HqMap g q).hom hxy
  refine ⟨fun q => ?_, fun q hq => ?_⟩
  · have := hQ.finite q
    exact Module.Finite.of_injective (HqMap f q).hom (hf q)
  · have : Subsingleton (Hq Q q) := ModuleCat.subsingleton_of_isZero (hQ.zero q hq)
    have : Subsingleton (Hq X q) := (hf q).subsingleton
    exact ModuleCat.isZero_of_subsingleton _

/-! ### The long exact sequence of a pair -/

section Pair

variable (P : TopPair.{0})

theorem finite_fst (q : ℕ) (hsnd : Module.Finite (ZMod 2) (Hq P.snd q))
    (hrel : Module.Finite (ZMod 2) (Hrel P q)) : Module.Finite (ZMod 2) (Hq P.fst q) :=
  finite_of_exact _ (P.singularHomology_exact_space coeff q) hsnd hrel

theorem isZero_fst (q : ℕ) (hsnd : IsZero (Hq P.snd q)) (hrel : IsZero (Hrel P q)) :
    IsZero (Hq P.fst q) :=
  isZero_of_exact _ (P.singularHomology_exact_space coeff q) hsnd hrel

theorem finite_rel_zero (hfst : Module.Finite (ZMod 2) (Hq P.fst 0)) :
    Module.Finite (ZMod 2) (Hrel P 0) :=
  finite_of_epi (P.singularHomologyπ coeff 0) hfst

theorem finite_rel_succ (q : ℕ) (hfst : Module.Finite (ZMod 2) (Hq P.fst (q + 1)))
    (hsnd : Module.Finite (ZMod 2) (Hq P.snd q)) : Module.Finite (ZMod 2) (Hrel P (q + 1)) :=
  finite_of_exact _ (P.singularHomology_exact_relative coeff (q + 1) q rfl) hfst hsnd

theorem isZero_rel_succ (q : ℕ) (hfst : IsZero (Hq P.fst (q + 1)))
    (hsnd : IsZero (Hq P.snd q)) : IsZero (Hrel P (q + 1)) :=
  isZero_of_exact _ (P.singularHomology_exact_relative coeff (q + 1) q rfl) hfst hsnd

end Pair

/-! ### Excision and unions -/

section Union

variable {X : TopCat.{0}}

/-- Excision in relative singular homology: for open sets A and N with A ⊆ B ⊆ A ∪ N, the
inclusion (N ∩ B, N ∩ A) → (B, A) is an isomorphism. -/
theorem isIso_excision {A B : Set X} (N : Set X) (hAB : A ⊆ B) (hA : IsOpen A) (hN : IsOpen N)
    (hcov : B ⊆ A ∪ N) (k : ℕ) :
    IsIso ((pairOf (inter_subset_inter_right N hAB)).singularHomologyMap
      (inclPair (inter_subset_inter_right N hAB) hAB inter_subset_right inter_subset_right)
      coeff k) := by
  have hemb : IsEmbedding (TopPair.Hom.fst (inclPair (inter_subset_inter_right N hAB) hAB
      inter_subset_right inter_subset_right)) :=
    IsEmbedding.inclusion inter_subset_right
  refine TopPair.isIso_singularHomologyMap_of_open_cover coeff _ hemb ?_
    (fun i : Bool => bif i then (Subtype.val ⁻¹' A : Set ↥B)
      else (Subtype.val ⁻¹' N : Set ↥B)) ?_ ?_ ?_ k
  · rintro x ⟨y, hy⟩
    have h : y.1 = x.1 := congrArg Subtype.val hy
    exact ⟨(⟨x.1, x.2.1, h ▸ y.2⟩ : ↥(N ∩ A)), Subtype.ext rfl⟩
  · rintro (_ | _)
    · exact hN.preimage continuous_subtype_val
    · exact hA.preimage continuous_subtype_val
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

theorem pairOf_fst {s t : Set X} (h : s ⊆ t) : (pairOf h).fst = TopCat.of ↥t := rfl

theorem pairOf_snd {s t : Set X} (h : s ⊆ t) : (pairOf h).snd = TopCat.of ↥s := rfl

/-- If A and C are open, A and C ∩ A are tame of bound m and C ∩ (A ∪ C) is tame of bound 1,
then A ∪ C is tame of bound m + 1. -/
theorem tame_union {A C : Set X} (hA : IsOpen A) (hC : IsOpen C) {m : ℕ}
    (hTA : Tame (TopCat.of ↥A) m) (hTC : Tame (TopCat.of ↥(C ∩ (A ∪ C))) 1)
    (hTAC : Tame (TopCat.of ↥(C ∩ A)) m) : Tame (TopCat.of ↥(A ∪ C)) (m + 1) := by
  have hAB : A ⊆ A ∪ C := subset_union_left
  have hexc : ∀ k, IsIso ((pairOf (inter_subset_inter_right C hAB)).singularHomologyMap
      (inclPair (inter_subset_inter_right C hAB) hAB inter_subset_right inter_subset_right)
      coeff k) := fun k => isIso_excision C hAB hA hC subset_rfl k
  have hfin2 : ∀ q, Module.Finite (ZMod 2) (Hrel (pairOf (inter_subset_inter_right C hAB)) q) := by
    intro q
    cases q with
    | zero =>
      have h1 : Module.Finite (ZMod 2) (Hq (pairOf (inter_subset_inter_right C hAB)).fst 0) :=
        hTC.finite 0
      exact finite_rel_zero _ h1
    | succ q =>
      have h1 : Module.Finite (ZMod 2)
          (Hq (pairOf (inter_subset_inter_right C hAB)).fst (q + 1)) := hTC.finite (q + 1)
      have h2 : Module.Finite (ZMod 2) (Hq (pairOf (inter_subset_inter_right C hAB)).snd q) :=
        hTAC.finite q
      exact finite_rel_succ _ q h1 h2
  have hzero2 : ∀ q, m ≤ q → IsZero (Hrel (pairOf (inter_subset_inter_right C hAB)) (q + 1)) := by
    intro q hq
    have h1 : IsZero (Hq (pairOf (inter_subset_inter_right C hAB)).fst (q + 1)) :=
      hTC.zero (q + 1) (by omega)
    have h2 : IsZero (Hq (pairOf (inter_subset_inter_right C hAB)).snd q) := hTAC.zero q hq
    exact isZero_rel_succ _ q h1 h2
  have hfin1 : ∀ q, Module.Finite (ZMod 2) (Hrel (pairOf hAB) q) := by
    intro q
    have := hexc q
    exact finite_of_epi ((pairOf (inter_subset_inter_right C hAB)).singularHomologyMap
      (inclPair (inter_subset_inter_right C hAB) hAB inter_subset_right inter_subset_right)
      coeff q) (hfin2 q)
  have hzero1 : ∀ q, m ≤ q → IsZero (Hrel (pairOf hAB) (q + 1)) := by
    intro q hq
    have := hexc (q + 1)
    exact (hzero2 q hq).of_iso
      (asIso ((pairOf (inter_subset_inter_right C hAB)).singularHomologyMap
        (inclPair (inter_subset_inter_right C hAB) hAB inter_subset_right inter_subset_right)
        coeff (q + 1))).symm
  refine ⟨fun q => ?_, fun q hq => ?_⟩
  · have h1 : Module.Finite (ZMod 2) (Hq (pairOf hAB).snd q) := hTA.finite q
    exact finite_fst (pairOf hAB) q h1 (hfin1 q)
  · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have h1 : IsZero (Hq (pairOf hAB).snd (q' + 1)) := hTA.zero _ (by omega)
    exact isZero_fst (pairOf hAB) (q' + 1) h1 (hzero1 q' (by omega))

end Union

/-! ### Convex sets and their finite unions -/

section Convex

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A convex subset of a real normed space is tame of bound 1. -/
theorem tame_convex (S : Set E) (hS : Convex ℝ S) : Tame (TopCat.of ↥S) 1 := by
  rcases S.eq_empty_or_nonempty with hne | hne
  · have : IsEmpty (TopCat.of ↥S) := by
      rw [hne]
      exact inferInstanceAs (IsEmpty (∅ : Set E))
    have h0 : Mono ((TopCat.of ↥S).singularHomology₀ε coeff) := by
      have h := TauCeti.isZero_reducedSingularHomologyFunctor_of_isEmpty coeff (TopCat.of ↥S) 0
      rw [TauCeti.reducedSingularHomologyFunctor_zero_obj] at h
      exact Preadditive.mono_of_isZero_kernel _ h
    have hpos : ∀ q, IsZero (Hq (TopCat.of ↥S) (q + 1)) := fun q =>
      isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ (q + 1) coeff
        (TopCat.of ↥S) q.succ_ne_zero
    refine ⟨fun q => ?_, fun q hq => ?_⟩
    · cases q with
      | zero => exact finite_of_mono ((TopCat.of ↥S).singularHomology₀ε coeff) inferInstance
      | succ q => exact finite_of_isZero (hpos q)
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact hpos q'
  · have : ContractibleSpace (TopCat.of ↥S) := hS.contractibleSpace hne
    have : PathConnectedSpace (TopCat.of ↥S) :=
      isPathConnected_iff_pathConnectedSpace.mp (hS.isPathConnected hne)
    have hpos : ∀ q, IsZero (Hq (TopCat.of ↥S) (q + 1)) := fun q =>
      TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace coeff (TopCat.of ↥S)
        q.succ_ne_zero
    refine ⟨fun q => ?_, fun q hq => ?_⟩
    · cases q with
      | zero => exact finite_of_mono ((TopCat.of ↥S).singularHomology₀ε coeff) inferInstance
      | succ q => exact finite_of_isZero (hpos q)
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      exact hpos q'

/-- Finite unions of convex open subsets of a real normed space. -/
inductive ConvexUnion : Set E → Prop
  | convex (C : Set E) (hC : Convex ℝ C) (hCo : IsOpen C) : ConvexUnion C
  | union (A C : Set E) (hA : ConvexUnion A) (hC : Convex ℝ C) (hCo : IsOpen C) :
      ConvexUnion (A ∪ C)

theorem convexUnion_isOpen {A : Set E} (h : ConvexUnion A) : IsOpen A := by
  induction h with
  | convex C hC hCo => exact hCo
  | union A C hA hC hCo ih => exact ih.union hCo

/-- The intersection of a finite union of convex open sets with a convex open set is tame. -/
theorem convexUnion_tame_inter {A : Set E} (h : ConvexUnion A) :
    ∀ D : Set E, Convex ℝ D → IsOpen D → ∃ m : ℕ, Tame (TopCat.of ↥(D ∩ A)) m := by
  induction h with
  | convex C hC hCo =>
    intro D hD hDo
    exact ⟨1, tame_convex (D ∩ C) (hD.inter hC)⟩
  | union A C hA hC hCo ih =>
    intro D hD hDo
    obtain ⟨m₁, h₁⟩ := ih D hD hDo
    obtain ⟨m₂, h₂⟩ := ih (D ∩ C) (hD.inter hC) (hDo.inter hCo)
    have e1 : D ∩ (A ∪ C) = (D ∩ A) ∪ (D ∩ C) := inter_union_distrib_left D A C
    have e2 : (D ∩ C) ∩ (D ∩ A) = (D ∩ C) ∩ A := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h1.1, h2⟩
    have e3 : (D ∩ C) ∩ ((D ∩ A) ∪ (D ∩ C)) = D ∩ C := inter_eq_left.mpr subset_union_right
    have hT1 : Tame (TopCat.of ↥(D ∩ A)) (max m₁ m₂) := tame_mono h₁ (le_max_left _ _)
    have hT2 : Tame (TopCat.of ↥((D ∩ C) ∩ (D ∩ A))) (max m₁ m₂) := by
      rw [e2]
      exact tame_mono h₂ (le_max_right _ _)
    have hT3 : Tame (TopCat.of ↥((D ∩ C) ∩ ((D ∩ A) ∪ (D ∩ C)))) 1 :=
      tame_convex _ (by rw [e3]; exact hD.inter hC)
    refine ⟨max m₁ m₂ + 1, ?_⟩
    rw [e1]
    exact tame_union (X := TopCat.of E) (hDo.inter (convexUnion_isOpen hA)) (hDo.inter hCo) hT1 hT3 hT2

/-- A finite union of convex open sets is tame. -/
theorem convexUnion_tame {A : Set E} (h : ConvexUnion A) : ∃ m : ℕ, Tame (TopCat.of ↥A) m := by
  obtain ⟨m, hm⟩ := convexUnion_tame_inter h univ convex_univ isOpen_univ
  rw [univ_inter] at hm
  exact ⟨m, hm⟩

/-- Between a compact set and an open set containing it there is a finite union of open
balls. -/
theorem exists_convexUnion_between {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hKΩ : K ⊆ Ω) : ∃ Q : Set E, ConvexUnion Q ∧ K ⊆ Q ∧ Q ⊆ Ω := by
  classical
  have h : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Ω := fun x hx =>
    Metric.isOpen_iff.mp hΩ x (hKΩ hx)
  choose! r hr0 hrΩ using h
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (r x))
    (fun x hx => Metric.ball_mem_nhds x (hr0 x hx))
  have key : ∀ s : Finset E, (∀ x ∈ s, x ∈ K) →
      ∃ Q : Set E, ConvexUnion Q ∧ (⋃ x ∈ s, Metric.ball x (r x)) ⊆ Q ∧ Q ⊆ Ω := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, ConvexUnion.convex ∅ convex_empty isOpen_empty, by simp, empty_subset _⟩
    | insert a s ha ih =>
      intro hs
      obtain ⟨Q, hQ, hsub, hQΩ⟩ := ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
      refine ⟨Q ∪ Metric.ball a (r a),
        ConvexUnion.union Q _ hQ (convex_ball a (r a)) Metric.isOpen_ball, ?_,
        union_subset hQΩ (hrΩ a (hs a (Finset.mem_insert_self a s)))⟩
      rw [Finset.set_biUnion_insert]
      exact union_subset subset_union_right (hsub.trans subset_union_left)
  obtain ⟨Q, hQ, hsub, hQΩ⟩ := key t htK
  exact ⟨Q, hQ, hcov.trans hsub, hQΩ⟩

/-- Between a compact set and an open set containing it there is an open tame set. -/
theorem exists_tame_between {K Ω : Set E} (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ (Q : Set E) (m : ℕ), IsOpen Q ∧ K ⊆ Q ∧ Q ⊆ Ω ∧ Tame (TopCat.of ↥Q) m := by
  obtain ⟨Q, hQ, hKQ, hQΩ⟩ := exists_convexUnion_between hK hΩ hKΩ
  obtain ⟨m, hm⟩ := convexUnion_tame hQ
  exact ⟨Q, m, convexUnion_isOpen hQ, hKQ, hQΩ, hm⟩

end Convex

end

end Finsler.TameHomology
