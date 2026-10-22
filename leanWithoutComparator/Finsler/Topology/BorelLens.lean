module

public import Finsler.Topology.BorelDeformation
public import Finsler.Topology.BorelExcision
public import Finsler.Topology.AvoidPoint
public import Finsler.Analysis.IntervalH1CutTopology

/-! Lenses and the vanishing of e on crossing groups. The inclusion of a pair of sets with the
same underlying sets is an isomorphism on actual relative cohomology. For open sets A and N of
a space and A ⊆ B ⊆ A ∪ N, the inclusion (N ∩ B, N ∩ A) → (B, A) is an excision. For nested sets
s ⊆ y ⊆ u, a map of u taking y into s which is homotopic to the identity through maps keeping s
gives a map of pairs (u, y) → (u, s) whose composite with (u, s) → (u, y) is an isomorphism on
actual relative cohomology. For pairs of reversal-invariant sets of loops, e is natural for
inclusions of pairs; hence e vanishes on a pair when it vanishes on a smaller pair to which
restriction is injective, and on a smaller pair when it vanishes on a larger one from which
restriction is surjective. A lens for levels a ≤ b consists of open reversal-invariant sets Y
and N of loops with t_a ⊆ Y ⊆ t_b ⊆ Y ∪ N, such that the loops of N below b avoid a point, and of
a map of t_b commuting with reversal which takes Y into t_a and is homotopic to the identity
through maps keeping t_a. The homotopy need not commute with reversal and need not keep Y. For
a lens, e acts as zero on the reflection Borel cohomology of the crossing pair (t_b, t_a): it
is zero on (N ∩ t_b, N ∩ Y) because evaluation avoids a point there, restriction from (t_b, Y)
to that pair is an excision, and restriction from (t_b, Y) to (t_b, t_a) is surjective because
its composite with the map induced by the retraction is an isomorphism. The existence of
lenses for tight regular cuts around a critical level is a separate geometric statement and is
not proved here. -/

@[expose] public section

namespace Finsler.BorelLens

open CategoryTheory Set Topology SphereOddDegree
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.RelativeCohomology Finsler.BorelEvaluation
open Finsler.SphereTopClass Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.SobolevReflectionAction Finsler.BorelDeformation
open Finsler.AvoidPoint

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Pullback on actual relative cohomology is contravariantly functorial. -/
theorem nativePull_comp {P Q R : TopPair.{0}} (f : P ⟶ Q) (g : Q ⟶ R) (k : ℕ)
    (x : native R k) : nativePull (f ≫ g) k x = nativePull f k (nativePull g k x) := by
  have h := TopPair.singularCohomologyMap_comp (R := coeff) (k := ZMod 2) (M := coeff) f g k
  exact congrArg (fun φ => φ.hom x) h

section General

variable {X : TopCat.{0}}

/-- The constant deformation: if t' ⊆ t and s' ⊆ s, the identity of t' deforms the pair
(t', s') into the pair (t, s). -/
def constDeformation {s t s' t' : Set X} (ht : t' ⊆ t) (hs : s' ⊆ s) :
    PairDeformation s t s' t' where
  r := ContinuousMap.id t'
  H := ContinuousMap.Homotopy.refl _
  r_mem x := ht x.2
  r_sub _ hx := hs hx
  keep_sub' _ _ hx := hx
  keep _ _ hx := hx
  keep_sub _ _ hx := hx

/-- An inclusion of pairs with the same underlying sets is an isomorphism on actual relative
cohomology. -/
theorem bijective_nativePull_of_eq {s t s' t' : Set X} (hst : s ⊆ t) (hst' : s' ⊆ t')
    (hss : s ⊆ s') (htt : t ⊆ t') (hs : s' ⊆ s) (ht : t' ⊆ t) (k : ℕ) :
    Function.Bijective (nativePull (inclPair hst hst' hss htt) k) :=
  bijective_nativePull_inclPair hst hst' hss htt (constDeformation ht hs) k

/-- A self-map of a pair which is homotopic to the identity is an isomorphism on actual relative
cohomology. -/
theorem bijective_nativePull_of_homotopic_id {P : TopPair.{0}} (f : P ⟶ P)
    (H : TopPair.Homotopy f (𝟙 P)) (k : ℕ) : Function.Bijective (nativePull f k) := by
  have H1 : Nonempty (TopPair.Homotopy (f ≫ 𝟙 P) (𝟙 P)) := by
    rw [Category.comp_id]
    exact ⟨H⟩
  have H2 : Nonempty (TopPair.Homotopy (𝟙 P ≫ f) (𝟙 P)) := by
    rw [Category.id_comp]
    exact ⟨H⟩
  obtain ⟨H1⟩ := H1
  obtain ⟨H2⟩ := H2
  exact BorelInvariance.bijective_nativePull_of_homotopyEquiv f (𝟙 P) H1 H2 k

/-- A retraction of the pair (u, y) to the pair (u, s): a map of u taking y into s, with a
homotopy from the identity under which s is invariant. -/
structure Retraction (s y u : Set X) where
  r : C(u, u)
  r_mem : ∀ x : u, (x : X) ∈ y → (r x : X) ∈ s
  H : (ContinuousMap.id u).Homotopy r
  keep : ∀ (τ : _root_.unitInterval) (x : u), (x : X) ∈ s → (H (τ, x) : X) ∈ s

section Retract

variable {s y u : Set X} (hsy : s ⊆ y) (hyu : y ⊆ u) (R : Retraction s y u)

/-- The retraction as a map of pairs (u, y) → (u, s). -/
def retractPair : pairOf hyu ⟶ pairOf (hsy.trans hyu) :=
  pairMap hyu (hsy.trans hyu) R.r (fun x hx => R.r_mem x hx)

/-- The composite (u, s) → (u, y) → (u, s) of the inclusion with a retraction is an isomorphism
on actual relative cohomology. -/
theorem bijective_nativePull_retract (k : ℕ) :
    Function.Bijective (nativePull
      (inclPair (hsy.trans hyu) hyu hsy subset_rfl ≫ retractPair hsy hyu R) k) := by
  have hF : ∀ (τ : _root_.unitInterval) (x : u), (x : X) ∈ s → (R.H (τ, x) : X) ∈ s := R.keep
  have H := (pairHomotopy (hsy.trans hyu) (hsy.trans hyu) R.H hF).symm
  have hcomp : R.r.comp (ContinuousMap.inclusion (subset_rfl : u ⊆ u)) = R.r := by
    ext x
    rfl
  have e1 : inclPair (hsy.trans hyu) hyu hsy subset_rfl ≫ retractPair hsy hyu R =
      pairMap (hsy.trans hyu) (hsy.trans hyu) R.r
        (fun x hx ↦ R.H.apply_one x ▸ hF 1 x hx) :=
    (pairMap_comp (hsy.trans hyu) hyu (hsy.trans hyu) (ContinuousMap.inclusion subset_rfl) R.r
      (fun _ hx => hsy hx) (fun x hx => R.r_mem x hx)).symm.trans
      (pairMap_congr _ _ hcomp _ _)
  have e2 : 𝟙 (pairOf (hsy.trans hyu)) =
      pairMap (hsy.trans hyu) (hsy.trans hyu) (ContinuousMap.id u)
        (fun x hx ↦ R.H.apply_zero x ▸ hF 0 x hx) :=
    (pairMap_id (hsy.trans hyu)).symm
  have Hn : Nonempty (TopPair.Homotopy
      (inclPair (hsy.trans hyu) hyu hsy subset_rfl ≫ retractPair hsy hyu R)
      (𝟙 (pairOf (hsy.trans hyu)))) := by
    rw [e1, e2]
    exact ⟨H⟩
  obtain ⟨H'⟩ := Hn
  exact bijective_nativePull_of_homotopic_id _ H' k

end Retract

variable {A B : Set X} (N : Set X) (hAB : A ⊆ B)

/-- Excision: for open sets A and N with A ⊆ B ⊆ A ∪ N, the inclusion
(N ∩ B, N ∩ A) → (B, A) is an isomorphism on actual relative cohomology. -/
theorem bijective_nativePull_excision (hA : IsOpen A) (hN : IsOpen N) (hcov : B ⊆ A ∪ N)
    (k : ℕ) :
    Function.Bijective (nativePull (inclPair (inter_subset_inter_right N hAB) hAB
      inter_subset_right inter_subset_right) k) := by
  have hemb : IsEmbedding (TopPair.Hom.fst (inclPair (inter_subset_inter_right N hAB) hAB
      inter_subset_right inter_subset_right)) :=
    IsEmbedding.inclusion inter_subset_right
  refine BorelExcision.bijective_nativePull_of_homology _ k
    (TopPair.isIso_singularHomologyMap_of_open_cover coeff _ hemb ?_
      (fun i : Bool => bif i then (Subtype.val ⁻¹' A : Set ↥B)
        else (Subtype.val ⁻¹' N : Set ↥B)) ?_ ?_ ?_ k)
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

end General

variable {n : ℕ}

section Subpairs

variable {s t s' t' : Set (Loops n)} (hst : s ⊆ t) (hst' : s' ⊆ t')
  (hs : ∀ u : SphereLoop n, u ∈ s → reverseSphere u ∈ s)
  (ht : ∀ u : SphereLoop n, u ∈ t → reverseSphere u ∈ t)
  (hs' : ∀ u : SphereLoop n, u ∈ s' → reverseSphere u ∈ s')
  (ht' : ∀ u : SphereLoop n, u ∈ t' → reverseSphere u ∈ t')
  (hss : s ⊆ s') (htt : t ⊆ t')

theorem inclPair_equivariant :
    inclPair hst hst' hss htt ≫ revSub hst' hs' ht' =
      revSub hst hs ht ≫ inclPair hst hst' hss htt := by
  ext : 2 <;> rfl

theorem inclPair_eval :
    TopPair.Hom.fst (inclPair hst hst' hss htt) ≫ evalSub hst' = evalSub hst := by
  ext u
  rfl

/-- Restriction of cochains between pairs of reversal-invariant sets of loops. -/
abbrev subHom : InvHom (ofPair (pairOf hst') (revSub hst' hs' ht') (revSub_sq hst' hs' ht'))
    (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) :=
  pullHom (revSub_sq hst hs ht) (revSub_sq hst' hs' ht') (inclPair hst hst' hss htt)
    (inclPair_equivariant hst hst' hs ht hs' ht' hss htt)

/-- Naturality of e for inclusions of pairs of reversal-invariant sets of loops. -/
theorem subE_natural (hn : 1 ≤ n) (q : ℕ)
    (z : HR (ofPair (pairOf hst') (revSub hst' hs' ht') (revSub_sq hst' hs' ht')) q) :
    HRmap (subHom hst hst' hs ht hs' ht' hss htt) (n + q) (subE hst' hs' ht' hn q z) =
      subE hst hs ht hn q (HRmap (subHom hst hst' hs ht hs' ht' hss htt) q z) := by
  apply BorelCup.cup_natural
  rw [cochain_comp, inclPair_eval]

/-- If restriction to a smaller pair is injective in degree n + q and e is zero on the smaller
pair in degree q, then e is zero on the larger pair in degree q. -/
theorem subE_zero_of_injective (hn : 1 ≤ n) (q : ℕ)
    (hinj : Function.Injective (HRmap (subHom hst hst' hs ht hs' ht' hss htt) (n + q)))
    (hzero : subE hst hs ht hn q = 0) : subE hst' hs' ht' hn q = 0 := by
  refine LinearMap.ext fun z => hinj ?_
  have h := subE_natural hst hst' hs ht hs' ht' hss htt hn q z
  rw [hzero, LinearMap.zero_apply] at h
  rw [h, LinearMap.zero_apply, map_zero]

/-- If restriction to a smaller pair is surjective in degree q and e is zero on the larger pair
in degree q, then e is zero on the smaller pair in degree q. -/
theorem subE_zero_of_surjective (hn : 1 ≤ n) (q : ℕ)
    (hsurj : Function.Surjective (HRmap (subHom hst hst' hs ht hs' ht' hss htt) q))
    (hzero : subE hst' hs' ht' hn q = 0) : subE hst hs ht hn q = 0 := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨z, rfl⟩ := hsurj y
  have h := subE_natural hst hst' hs ht hs' ht' hss htt hn q z
  rw [hzero, LinearMap.zero_apply, map_zero] at h
  exact h.symm.trans (LinearMap.zero_apply _).symm

/-- An inclusion of pairs of reversal-invariant sets of loops which is an isomorphism on actual
relative cohomology is an isomorphism on reflection Borel cohomology. -/
theorem bijective_subHom
    (h : ∀ k, Function.Bijective (nativePull (inclPair hst hst' hss htt) k)) :
    ∀ k, Function.Bijective (HRmap (subHom hst hst' hs ht hs' ht' hss htt) k) :=
  BorelInvariance.bijective_HRmap (revSub_sq hst hs ht) (revSub_sq hst' hs' ht')
    (inclPair hst hst' hss htt) (inclPair_equivariant hst hst' hs ht hs' ht' hss htt) h

end Subpairs

variable (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)

/-- For a positive level the set t_a is the open sublevel. -/
theorem lev_isOpen (ha : 0 < a) : IsOpen (lev F a) := by
  have h : lev F a = energyCut F a := by
    apply Subset.antisymm
    · rintro u (hu | ⟨x, rfl⟩)
      · exact hu
      · exact (constant_mem_energyCut_iff F a x).mpr ha
    · exact subset_union_left
  rw [h]
  exact Finsler.SobolevCutTopology.energyCut_isOpen F a

/-- If e acts as zero on the pair (t_b, t_a) regarded as a pair of sets of loops, it acts as
zero on the crossing group. -/
theorem crossE_zero_of_subE_zero (hn : 1 ≤ n) (q : ℕ)
    (h : subE (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => reverse_mem_lev F hu) hn q = 0)
    (z : HR (crossComplex F hab) q) : crossE F hab hn q z = 0 := by
  have hbij := BorelInvariance.bijective_HRmap
    (revSub_sq (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => reverse_mem_lev F hu))
    (revCross_sq F hab) (toCross (lev_mono F hab) F hab subset_rfl subset_rfl)
    (toCross_equivariant (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => reverse_mem_lev F hu) F hab subset_rfl subset_rfl)
    (fun k => bijective_nativePull_of_eq (lev_mono F hab) (lev_mono F hab) subset_rfl
      subset_rfl subset_rfl subset_rfl k) (n + q)
  apply hbij.1
  rw [crossE_toCross, h, LinearMap.zero_apply, map_zero]

/-- A lens for the levels a ≤ b and a point p: open reversal-invariant sets Y and N of loops
with t_a ⊆ Y ⊆ t_b ⊆ Y ∪ N, such that the loops of N below b avoid p, and a map of t_b commuting
with reversal which takes Y into t_a and is homotopic to the identity through maps keeping
t_a. -/
structure Lens (F : ReversibleMetric n) (a b : ℝ) (p : Sphere n) where
  Y : Set (Loops n)
  N : Set (Loops n)
  Y_open : IsOpen Y
  N_open : IsOpen N
  Y_rev : ∀ u : SphereLoop n, u ∈ Y → reverseSphere u ∈ Y
  N_rev : ∀ u : SphereLoop n, u ∈ N → reverseSphere u ∈ N
  lev_subset : lev F a ⊆ Y
  subset_lev : Y ⊆ lev F b
  cover : lev F b ⊆ Y ∪ N
  avoids : N ∩ lev F b ⊆ avoid p
  retraction : Retraction (lev F a) Y (lev F b)
  rev_comm : ∀ x : lev F b,
    (retraction.r ⟨reverseSphere (x : SphereLoop n), reverse_mem_lev F x.2⟩ : Loops n) =
      reverseSphere (retraction.r x : SphereLoop n)

/-- For a lens, restriction from (t_b, Y) to (t_b, t_a) is surjective on reflection Borel
cohomology. -/
theorem lens_surjective (p : Sphere n) (L : Lens F a b p) (q : ℕ) :
    Function.Surjective (HRmap (subHom (L.lev_subset.trans L.subset_lev) L.subset_lev
      (fun _ hu => reverse_mem_lev F hu) (fun _ hu => reverse_mem_lev F hu) L.Y_rev
      (fun _ hu => reverse_mem_lev F hu) L.lev_subset subset_rfl) q) := by
  have hA : lev F a ⊆ lev F b := L.lev_subset.trans L.subset_lev
  have hra : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have hrb : ∀ u : SphereLoop n, u ∈ lev F b → reverseSphere u ∈ lev F b :=
    fun _ hu => reverse_mem_lev F hu
  have hcomm : (revSet hrb).comp L.retraction.r = L.retraction.r.comp (revSet hrb) :=
    ContinuousMap.ext fun x => Subtype.ext (L.rev_comm x).symm
  have hR : retractPair L.lev_subset L.subset_lev L.retraction ≫ revSub hA hra hrb =
      revSub L.subset_lev L.Y_rev hrb ≫ retractPair L.lev_subset L.subset_lev L.retraction :=
    (pairMap_comp L.subset_lev hA hA L.retraction.r (revSet hrb)
      (fun x hx => L.retraction.r_mem x hx) (fun _ hx => hra _ hx)).symm.trans
      ((pairMap_congr _ _ hcomm _ _).trans
        (pairMap_comp L.subset_lev L.subset_lev hA (revSet hrb) L.retraction.r
          (fun _ hx => L.Y_rev _ hx) (fun x hx => L.retraction.r_mem x hx)))
  have hj := inclPair_equivariant hA L.subset_lev hra hrb L.Y_rev hrb L.lev_subset subset_rfl
  have hjR : (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) ≫ revSub hA hra hrb =
      revSub hA hra hrb ≫ (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) := by
    rw [Category.assoc, hR, ← Category.assoc, hj, Category.assoc]
  have hB := BorelInvariance.bijective_HRmap (revSub_sq hA hra hrb) (revSub_sq hA hra hrb)
    (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
      retractPair L.lev_subset L.subset_lev L.retraction) hjR
    (fun k => bijective_nativePull_retract L.lev_subset L.subset_lev L.retraction k) q
  intro y
  obtain ⟨x, hx⟩ := hB.2 y
  refine ⟨HRmap (pullHom (revSub_sq L.subset_lev L.Y_rev hrb) (revSub_sq hA hra hrb)
    (retractPair L.lev_subset L.subset_lev L.retraction) hR) q x, ?_⟩
  rw [← hx, ← HRmap_comp]
  exact (HRmap_congr (pullHom_comp (revSub_sq hA hra hrb)
    (revSub_sq L.subset_lev L.Y_rev hrb) (revSub_sq hA hra hrb)
    (inclPair hA L.subset_lev L.lev_subset subset_rfl)
    (retractPair L.lev_subset L.subset_lev L.retraction) hj hR hjR) q x).symm

/-- E-ZERO from a lens: e acts as zero on the reflection Borel cohomology of the crossing pair
(t_b, t_a). -/
theorem crossE_zero_of_lens (hn : 1 ≤ n) (p : Sphere n) (L : Lens F a b p) (q : ℕ)
    (z : HR (crossComplex F hab) q) : crossE F hab hn q z = 0 := by
  have hA : lev F a ⊆ lev F b := L.lev_subset.trans L.subset_lev
  have hC : L.N ∩ L.Y ⊆ L.N ∩ lev F b := inter_subset_inter_right L.N L.subset_lev
  have hra : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have hrb : ∀ u : SphereLoop n, u ∈ lev F b → reverseSphere u ∈ lev F b :=
    fun _ hu => reverse_mem_lev F hu
  have hCs : ∀ u : SphereLoop n, u ∈ L.N ∩ L.Y → reverseSphere u ∈ L.N ∩ L.Y :=
    fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩
  have hCt : ∀ u : SphereLoop n, u ∈ L.N ∩ lev F b → reverseSphere u ∈ L.N ∩ lev F b :=
    fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩
  have h1 : subE hC hCs hCt hn q = 0 := subE_zero_of_subset_avoid hC hCs hCt hn p L.avoids q
  have h2 : subE L.subset_lev L.Y_rev hrb hn q = 0 :=
    subE_zero_of_injective hC L.subset_lev hCs hCt L.Y_rev hrb inter_subset_right
      inter_subset_right hn q
      (bijective_subHom hC L.subset_lev hCs hCt L.Y_rev hrb inter_subset_right
        inter_subset_right
        (fun k => bijective_nativePull_excision L.N L.subset_lev L.Y_open L.N_open L.cover k)
        (n + q)).1 h1
  have h3 : subE hA hra hrb hn q = 0 :=
    subE_zero_of_surjective hA L.subset_lev hra hrb L.Y_rev hrb L.lev_subset subset_rfl hn q
      (lens_surjective F p L q) h2
  exact crossE_zero_of_subE_zero F hab hn q h3 z

end

end Finsler.BorelLens
