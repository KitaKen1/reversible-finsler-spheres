module

public import Finsler.Topology.BorelLocal
public import Finsler.Topology.BorelFreeK
public import Finsler.Topology.BorelCrossingK
public import Finsler.Topology.ShorteningK

/-! Local lenses and the reflection class on K-Borel cohomology. A pair of sets of loops
invariant under the reversal and the half rotation carries two commuting involutions, hence
K-Borel cochains, and inclusions of such pairs induce maps of them; an inclusion which is an
isomorphism on actual relative cohomology is an isomorphism on K-Borel cohomology. If the pair
lies in a set with an orientation invariant under the half rotation, the reflection class w
acts as zero on its K-Borel cohomology. For a local lens whose sets and retraction are
compatible with the half rotation, restriction from (t_b, Y) to (t_b, t_a) is surjective on
K-Borel cohomology, so w acts as zero on the K-Borel cohomology of the crossing pair when the
lens lies in such an oriented set. The passage from tight to wide cuts holds as for the
reflection groups, and a shortening commuting with the half rotation gives a local lens
compatible with it. -/

@[expose] public section

namespace Finsler.BorelLocalK

open CategoryTheory Set Topology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevReverse Finsler.SobolevReflectionAction
open Finsler.BorelDeformation Finsler.AvoidPoint Finsler.BorelLens Finsler.RegularInterval
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelCrossingK Finsler.BorelLocal
open Finsler.BorelFreeK Finsler.ShorteningK Finsler.SobolevShiftEnergy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

section Subpairs

variable {s t : Set (Loops n)} (hst : s ⊆ t)
  (hs : ∀ u : SphereLoop n, u ∈ s → reverseSphere u ∈ s)
  (ht : ∀ u : SphereLoop n, u ∈ t → reverseSphere u ∈ t)
  (hhs : ∀ u : SphereLoop n, u ∈ s → half +ᵥ u ∈ s)
  (hht : ∀ u : SphereLoop n, u ∈ t → half +ᵥ u ∈ t)

/-- The half rotation on a set of loops invariant under it. -/
def halfSet : C(t, t) :=
  ⟨fun u => ⟨half +ᵥ (u : SphereLoop n), hht _ u.2⟩,
    (half_continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The half rotation of a pair of sets of loops invariant under it. -/
def halfSub : pairOf hst ⟶ pairOf hst :=
  pairMap hst hst (halfSet hht) (fun _ hx => hhs _ hx)

theorem halfSub_sq : halfSub hst hhs hht ≫ halfSub hst hhs hht = 𝟙 (pairOf hst) := by
  have h : (halfSet hht).comp (halfSet hht) = ContinuousMap.id t := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (half_half (u : SphereLoop n)) :
      (⟨half +ᵥ (half +ᵥ (u : SphereLoop n)), hht _ (hht _ u.2)⟩ : t) = u)
  exact (pairMap_comp hst hst hst (halfSet hht) (halfSet hht) (fun _ hx => hhs _ hx)
    (fun _ hx => hhs _ hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem halfSub_rev :
    halfSub hst hhs hht ≫ revSub hst hs ht = revSub hst hs ht ≫ halfSub hst hhs hht := by
  have h : (revSet ht).comp (halfSet hht) = (halfSet hht).comp (revSet ht) := by
    ext u
    exact congrArg Subtype.val (Subtype.ext (reverse_half (u : SphereLoop n)) :
      (⟨reverseSphere (half +ᵥ (u : SphereLoop n)), ht _ (hht _ u.2)⟩ : t) =
        ⟨half +ᵥ reverseSphere (u : SphereLoop n), hht _ (ht _ u.2)⟩)
  exact (pairMap_comp _ _ _ (halfSet hht) (revSet ht) (fun _ hx => hhs _ hx)
    (fun _ hx => hs _ hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hhs _ (hs _ hx))).trans
      (pairMap_comp _ _ _ (revSet ht) (halfSet hht) (fun _ hx => hs _ hx)
        (fun _ hx => hhs _ hx)))

/-- The two commuting involutions on the cochains of a pair of sets of loops invariant under the
reversal and the half rotation. -/
abbrev subCommuting :
    Commuting (ofPair (pairOf hst) (revSub hst hs ht) (revSub_sq hst hs ht)) :=
  BorelInvariance.commuting (revSub_sq hst hs ht) (halfSub hst hhs hht)
    (halfSub_sq hst hhs hht) (halfSub_rev hst hs ht hhs hht)

/-- An orientation invariant under the half rotation. -/
structure HalfInvariant {V : Set (Loops n)} (O : Orientation V) : Prop where
  pos_half : ∀ u : SphereLoop n, u ∈ O.pos → half +ᵥ u ∈ O.pos
  neg_half : ∀ u : SphereLoop n, u ∈ O.neg → half +ᵥ u ∈ O.neg

/-- On a pair of sets of loops invariant under the reversal and the half rotation inside a set
with an orientation invariant under the half rotation, the reflection class acts as zero on
K-Borel cohomology. -/
theorem subWK_zero {V : Set (Loops n)} (O : Orientation V) (hO : HalfInvariant O)
    (htV : t ⊆ V) (q : ℕ) (y : HR (borelInv (subCommuting hst hs ht hhs hht)) q) :
    BorelGraded.onHR (innerW (subCommuting hst hs ht hhs hht)) q y = 0 := by
  have hcompl : ({x : t | (x : Loops n) ∈ O.pos} : Set t)ᶜ = {x : t | (x : Loops n) ∈ O.neg} := by
    ext x
    constructor
    · intro hx
      rcases O.cover (htV x.2) with h | h
      · exact absurd h hx
      · exact h
    · intro hx hpos
      exact O.disjoint _ (htV x.2) hpos hx
  have hclosed : IsClosed ({x : t | (x : Loops n) ∈ O.pos} : Set t) := by
    rw [← isOpen_compl_iff, hcompl]
    exact O.neg_open.preimage continuous_subtype_val
  have hopen : IsOpen ({x : t | (x : Loops n) ∈ O.pos} : Set t) :=
    O.pos_open.preimage continuous_subtype_val
  refine innerW_eq_zero_of_isClopen (pairOf hst) (revSub hst hs ht) (halfSub hst hhs hht)
    (revSub_sq hst hs ht) (halfSub_sq hst hhs hht) (halfSub_rev hst hs ht hhs hht)
    {x : t | (x : Loops n) ∈ O.pos} ⟨hclosed, hopen⟩
    (fun x => ⟨fun hrx hx => ?_, fun hx => ?_⟩) (fun x => ⟨fun hx => ?_, fun hx => ?_⟩) q y
  · exact O.disjoint _ (htV (ht _ x.2)) hrx (O.rev_pos _ hx)
  · rcases O.cover (htV x.2) with h | h
    · exact absurd h hx
    · exact O.rev_neg _ h
  · have h : half +ᵥ (half +ᵥ (x.1 : SphereLoop n)) ∈ O.pos := hO.pos_half _ hx
    rw [half_half] at h
    exact h
  · exact hO.pos_half _ hx

variable {s' t' : Set (Loops n)} (hst' : s' ⊆ t')
  (hs' : ∀ u : SphereLoop n, u ∈ s' → reverseSphere u ∈ s')
  (ht' : ∀ u : SphereLoop n, u ∈ t' → reverseSphere u ∈ t')
  (hhs' : ∀ u : SphereLoop n, u ∈ s' → half +ᵥ u ∈ s')
  (hht' : ∀ u : SphereLoop n, u ∈ t' → half +ᵥ u ∈ t')
  (hss : s ⊆ s') (htt : t ⊆ t')

theorem inclPair_half :
    inclPair hst hst' hss htt ≫ halfSub hst' hhs' hht' =
      halfSub hst hhs hht ≫ inclPair hst hst' hss htt := by
  ext : 2 <;> rfl

/-- Restriction of K-Borel cochains between pairs of sets of loops invariant under the reversal
and the half rotation. -/
abbrev subCommHom : CommHom (subCommuting hst' hs' ht' hhs' hht')
    (subCommuting hst hs ht hhs hht) :=
  BorelInvariance.commHom (revSub_sq hst hs ht) (revSub_sq hst' hs' ht')
    (inclPair hst hst' hss htt) (inclPair_equivariant hst hst' hs ht hs' ht' hss htt)
    (halfSub_sq hst hhs hht) (halfSub_sq hst' hhs' hht') (halfSub_rev hst hs ht hhs hht)
    (halfSub_rev hst' hs' ht' hhs' hht') (inclPair_half hst hhs hht hst' hhs' hht' hss htt)

/-- An inclusion of such pairs which is an isomorphism on actual relative cohomology is an
isomorphism on K-Borel cohomology. -/
theorem bijective_subCommHom
    (h : ∀ k, Function.Bijective (nativePull (inclPair hst hst' hss htt) k)) :
    ∀ k, Function.Bijective (HRmap (borelHom
      (subCommHom hst hs ht hhs hht hst' hs' ht' hhs' hht' hss htt)) k) :=
  BorelInvariance.bijective_iterated (revSub_sq hst hs ht) (revSub_sq hst' hs' ht')
    (inclPair hst hst' hss htt) (inclPair_equivariant hst hst' hs ht hs' ht' hss htt)
    (halfSub_sq hst hhs hht) (halfSub_sq hst' hhs' hht') (halfSub_rev hst hs ht hhs hht)
    (halfSub_rev hst' hs' ht' hhs' hht') (inclPair_half hst hhs hht hst' hhs' hht' hss htt) h

variable (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)
  (hsa : s ⊆ lev F a) (htb : t ⊆ lev F b)

theorem toCross_half :
    toCross hst F hab hsa htb ≫ halfCross F hab =
      halfSub hst hhs hht ≫ toCross hst F hab hsa htb := by
  ext : 2 <;> rfl

/-- The two commuting involutions on the crossing cochains, in the form used for pairs. -/
abbrev crossCommuting : Commuting (crossComplex F hab) :=
  BorelInvariance.commuting (revCross_sq F hab) (halfCross F hab) (halfCross_sq F hab)
    (halfCross_rev F hab)

/-- Restriction of K-Borel crossing cochains to a pair of sets of loops. -/
abbrev toCrossCommHom : CommHom (crossCommuting F hab) (subCommuting hst hs ht hhs hht) :=
  BorelInvariance.commHom (revSub_sq hst hs ht) (revCross_sq F hab)
    (toCross hst F hab hsa htb) (toCross_equivariant hst hs ht F hab hsa htb)
    (halfSub_sq hst hhs hht) (halfCross_sq F hab) (halfSub_rev hst hs ht hhs hht)
    (halfCross_rev F hab) (toCross_half hst hhs hht F hab hsa htb)

theorem bijective_toCrossCommHom
    (h : ∀ k, Function.Bijective (nativePull (toCross hst F hab hsa htb) k)) :
    ∀ k, Function.Bijective (HRmap (borelHom
      (toCrossCommHom hst hs ht hhs hht F hab hsa htb)) k) :=
  BorelInvariance.bijective_iterated (revSub_sq hst hs ht) (revCross_sq F hab)
    (toCross hst F hab hsa htb) (toCross_equivariant hst hs ht F hab hsa htb)
    (halfSub_sq hst hhs hht) (halfCross_sq F hab) (halfSub_rev hst hs ht hhs hht)
    (halfCross_rev F hab) (toCross_half hst hhs hht F hab hsa htb) h

end Subpairs

variable (F : ReversibleMetric n) {a b : ℝ} {V : Set (Loops n)}

/-- A local lens whose sets and retraction are compatible with the half rotation. -/
structure HalfLens (L : LocalLens F a b V) : Prop where
  Y_half : ∀ u : SphereLoop n, u ∈ L.Y → half +ᵥ u ∈ L.Y
  N_half : ∀ u : SphereLoop n, u ∈ L.N → half +ᵥ u ∈ L.N
  half_comm : ∀ x : lev F b,
    (L.retraction.r ⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩ : Loops n) =
      half +ᵥ (L.retraction.r x : SphereLoop n)

/-- For a local lens compatible with the half rotation, restriction from (t_b, Y) to
(t_b, t_a) is surjective on K-Borel cohomology. -/
theorem halfLens_surjective (L : LocalLens F a b V) (hL : HalfLens F L) (q : ℕ) :
    Function.Surjective (HRmap (borelHom (subCommHom (L.lev_subset.trans L.subset_lev)
      (fun _ hu => reverse_mem_lev F hu) (fun _ hu => reverse_mem_lev F hu)
      (fun _ hu => half_mem_lev F hu) (fun _ hu => half_mem_lev F hu) L.subset_lev L.Y_rev
      (fun _ hu => reverse_mem_lev F hu) hL.Y_half (fun _ hu => half_mem_lev F hu)
      L.lev_subset subset_rfl)) q) := by
  have hA : lev F a ⊆ lev F b := L.lev_subset.trans L.subset_lev
  have hra : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have hrb : ∀ u : SphereLoop n, u ∈ lev F b → reverseSphere u ∈ lev F b :=
    fun _ hu => reverse_mem_lev F hu
  have hha : ∀ u : SphereLoop n, u ∈ lev F a → half +ᵥ u ∈ lev F a :=
    fun _ hu => half_mem_lev F hu
  have hhb : ∀ u : SphereLoop n, u ∈ lev F b → half +ᵥ u ∈ lev F b :=
    fun _ hu => half_mem_lev F hu
  have hcomm : (revSet hrb).comp L.retraction.r = L.retraction.r.comp (revSet hrb) :=
    ContinuousMap.ext fun x => Subtype.ext (L.rev_comm x).symm
  have hcommh : (halfSet hhb).comp L.retraction.r = L.retraction.r.comp (halfSet hhb) :=
    ContinuousMap.ext fun x => Subtype.ext (hL.half_comm x).symm
  have hR : retractPair L.lev_subset L.subset_lev L.retraction ≫ revSub hA hra hrb =
      revSub L.subset_lev L.Y_rev hrb ≫ retractPair L.lev_subset L.subset_lev L.retraction :=
    (pairMap_comp L.subset_lev hA hA L.retraction.r (revSet hrb)
      (fun x hx => L.retraction.r_mem x hx) (fun _ hx => hra _ hx)).symm.trans
      ((pairMap_congr _ _ hcomm _ _).trans
        (pairMap_comp L.subset_lev L.subset_lev hA (revSet hrb) L.retraction.r
          (fun _ hx => L.Y_rev _ hx) (fun x hx => L.retraction.r_mem x hx)))
  have hRh : retractPair L.lev_subset L.subset_lev L.retraction ≫ halfSub hA hha hhb =
      halfSub L.subset_lev hL.Y_half hhb ≫
        retractPair L.lev_subset L.subset_lev L.retraction :=
    (pairMap_comp L.subset_lev hA hA L.retraction.r (halfSet hhb)
      (fun x hx => L.retraction.r_mem x hx) (fun _ hx => hha _ hx)).symm.trans
      ((pairMap_congr _ _ hcommh _ _).trans
        (pairMap_comp L.subset_lev L.subset_lev hA (halfSet hhb) L.retraction.r
          (fun _ hx => hL.Y_half _ hx) (fun x hx => L.retraction.r_mem x hx)))
  have hj := inclPair_equivariant hA L.subset_lev hra hrb L.Y_rev hrb L.lev_subset subset_rfl
  have hjh := inclPair_half hA hha hhb L.subset_lev hL.Y_half hhb L.lev_subset subset_rfl
  have hjR : (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) ≫ revSub hA hra hrb =
      revSub hA hra hrb ≫ (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) := by
    rw [Category.assoc, hR, ← Category.assoc, hj, Category.assoc]
  have hjRh : (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) ≫ halfSub hA hha hhb =
      halfSub hA hha hhb ≫ (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
        retractPair L.lev_subset L.subset_lev L.retraction) := by
    rw [Category.assoc, hRh, ← Category.assoc, hjh, Category.assoc]
  have hB := BorelInvariance.bijective_iterated (revSub_sq hA hra hrb) (revSub_sq hA hra hrb)
    (inclPair hA L.subset_lev L.lev_subset subset_rfl ≫
      retractPair L.lev_subset L.subset_lev L.retraction) hjR
    (halfSub_sq hA hha hhb) (halfSub_sq hA hha hhb) (halfSub_rev hA hra hrb hha hhb)
    (halfSub_rev hA hra hrb hha hhb) hjRh
    (fun k => bijective_nativePull_retract L.lev_subset L.subset_lev L.retraction k) q
  intro y
  obtain ⟨x, hx⟩ := hB.2 y
  refine ⟨HRmap (borelHom (BorelInvariance.commHom (revSub_sq L.subset_lev L.Y_rev hrb)
    (revSub_sq hA hra hrb) (retractPair L.lev_subset L.subset_lev L.retraction) hR
    (halfSub_sq L.subset_lev hL.Y_half hhb) (halfSub_sq hA hha hhb)
    (halfSub_rev L.subset_lev L.Y_rev hrb hL.Y_half hhb) (halfSub_rev hA hra hrb hha hhb)
    hRh)) q x, ?_⟩
  rw [← hx, ← HRmap_comp]
  refine (HRmap_congr (fun j z => ?_) q x).symm
  apply Subtype.ext
  funext i
  exact pullHom_comp (revSub_sq hA hra hrb) (revSub_sq L.subset_lev L.Y_rev hrb)
    (revSub_sq hA hra hrb) (inclPair hA L.subset_lev L.lev_subset subset_rfl)
    (retractPair L.lev_subset L.subset_lev L.retraction) hj hR hjR i _

/-- For a local lens compatible with the half rotation inside a set with an orientation
invariant under the half rotation, the reflection class acts as zero on the K-Borel cohomology
of the crossing pair (t_b, t_a). -/
theorem crossWK_zero_of_localLens (hab : a ≤ b) (L : LocalLens F a b V) (hL : HalfLens F L)
    (O : Orientation V) (hO : HalfInvariant O) (q : ℕ)
    (z : HR (borelInv (crossCommuting F hab)) q) :
    BorelGraded.onHR (innerW (crossCommuting F hab)) q z = 0 := by
  have hA : lev F a ⊆ lev F b := L.lev_subset.trans L.subset_lev
  have hC : L.N ∩ L.Y ⊆ L.N ∩ lev F b := inter_subset_inter_right L.N L.subset_lev
  have hra : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have hrb : ∀ u : SphereLoop n, u ∈ lev F b → reverseSphere u ∈ lev F b :=
    fun _ hu => reverse_mem_lev F hu
  have hha : ∀ u : SphereLoop n, u ∈ lev F a → half +ᵥ u ∈ lev F a :=
    fun _ hu => half_mem_lev F hu
  have hhb : ∀ u : SphereLoop n, u ∈ lev F b → half +ᵥ u ∈ lev F b :=
    fun _ hu => half_mem_lev F hu
  have hCs : ∀ u : SphereLoop n, u ∈ L.N ∩ L.Y → reverseSphere u ∈ L.N ∩ L.Y :=
    fun u hu => ⟨L.N_rev u hu.1, L.Y_rev u hu.2⟩
  have hCt : ∀ u : SphereLoop n, u ∈ L.N ∩ lev F b → reverseSphere u ∈ L.N ∩ lev F b :=
    fun u hu => ⟨L.N_rev u hu.1, reverse_mem_lev F hu.2⟩
  have hhCs : ∀ u : SphereLoop n, u ∈ L.N ∩ L.Y → half +ᵥ u ∈ L.N ∩ L.Y :=
    fun u hu => ⟨hL.N_half u hu.1, hL.Y_half u hu.2⟩
  have hhCt : ∀ u : SphereLoop n, u ∈ L.N ∩ lev F b → half +ᵥ u ∈ L.N ∩ lev F b :=
    fun u hu => ⟨hL.N_half u hu.1, half_mem_lev F hu.2⟩
  have h1 := subWK_zero hC hCs hCt hhCs hhCt O hO L.inside q
  have h2 := innerW_zero_of_injective
    (subCommHom hC hCs hCt hhCs hhCt L.subset_lev L.Y_rev hrb hL.Y_half hhb
      inter_subset_right inter_subset_right) q
    (bijective_subCommHom hC hCs hCt hhCs hhCt L.subset_lev L.Y_rev hrb hL.Y_half hhb
      inter_subset_right inter_subset_right
      (fun k => bijective_nativePull_excision L.N L.subset_lev L.Y_open L.N_open L.cover k)
      (1 + q)).1 h1
  have h3 := innerW_zero_of_surjective
    (subCommHom hA hra hrb hha hhb L.subset_lev L.Y_rev hrb hL.Y_half hhb L.lev_subset
      subset_rfl) q (halfLens_surjective F L hL q) h2
  have hbij := bijective_toCrossCommHom (lev_mono F hab) (fun _ hu => reverse_mem_lev F hu)
    (fun _ hu => reverse_mem_lev F hu) (fun _ hu => half_mem_lev F hu)
    (fun _ hu => half_mem_lev F hu) F hab subset_rfl subset_rfl
    (fun k => bijective_nativePull_of_eq (lev_mono F hab) (lev_mono F hab) subset_rfl
      subset_rfl subset_rfl subset_rfl k) (1 + q)
  exact innerW_zero_of_injective _ q hbij.1 h3 z

/-- From tight cuts to wide cuts for the reflection class on K-Borel cohomology. -/
theorem crossWK_zero_of_tight {a a' b' b : ℝ} (haa : a ≤ a') (hab' : a' ≤ b') (hbb : b' ≤ b)
    (D₁ : LevelDeformation F a a' b') (D₂ : LevelDeformation F b' b b) (q : ℕ)
    (htight : ∀ z' : HR (borelInv (crossCommuting F hab')) q,
      BorelGraded.onHR (innerW (crossCommuting F hab')) q z' = 0)
    (z : HR (borelInv (crossCommuting F (haa.trans (hab'.trans hbb)))) q) :
    BorelGraded.onHR (innerW (crossCommuting F (haa.trans (hab'.trans hbb)))) q z = 0 := by
  have hst : lev F a ⊆ lev F b' := lev_mono F (haa.trans hab')
  have hs : ∀ u : SphereLoop n, u ∈ lev F a → reverseSphere u ∈ lev F a :=
    fun _ hu => reverse_mem_lev F hu
  have ht : ∀ u : SphereLoop n, u ∈ lev F b' → reverseSphere u ∈ lev F b' :=
    fun _ hu => reverse_mem_lev F hu
  have hhs : ∀ u : SphereLoop n, u ∈ lev F a → half +ᵥ u ∈ lev F a :=
    fun _ hu => half_mem_lev F hu
  have hht : ∀ u : SphereLoop n, u ∈ lev F b' → half +ᵥ u ∈ lev F b' :=
    fun _ hu => half_mem_lev F hu
  have h1 := bijective_toCrossCommHom hst hs ht hhs hht F (haa.trans (hab'.trans hbb))
    subset_rfl (lev_mono F hbb)
    (fun k => bijective_nativePull hst (lev_mono F hbb) (toDeformation D₂ a) k)
  have h2 := bijective_toCrossCommHom hst hs ht hhs hht F hab' (lev_mono F haa) subset_rfl
    (fun k => bijective_nativePull_inclPair hst (lev_mono F hab') (lev_mono F haa) subset_rfl
      (toPairDeformation D₁) k)
  have hmid := innerW_zero_of_surjective _ q (h2 q).2 htight
  exact innerW_zero_of_injective _ q (h1 (1 + q)).1 hmid z

/-- The vanishing of the reflection class on the K-Borel cohomology of single crossings from
level deformations and oriented local lenses compatible with the half rotation. -/
theorem crossWK_zero_of_flow (crit : Set ℝ)
    (hreg : ∀ a a' b : ℝ, 0 < a → a ≤ a' → a' ≤ b → (∀ x ∈ Icc a a', x ∉ crit) →
      Nonempty (LevelDeformation F a a' b))
    (hlens : ∀ c ∈ crit, ∃ (V : Set (Loops n)) (O : Orientation V) (_ : HalfInvariant O)
      (ε : ℝ), 0 < ε ∧ ∀ a b : ℝ, c - ε < a → a < c → c < b → b < c + ε →
        ∃ L : LocalLens F a b V, HalfLens F L)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit) (hbc : b ∉ crit)
    (hsub : (crit ∩ Icc a b).Subsingleton) (q : ℕ)
    (z : HR (borelInv (crossCommuting F hab)) q) :
    BorelGraded.onHR (innerW (crossCommuting F hab)) q z = 0 := by
  by_cases hne : (crit ∩ Icc a b).Nonempty
  · obtain ⟨c, hc, hcab⟩ := hne
    have hac' : a < c := lt_of_le_of_ne hcab.1 (fun h => hac (h ▸ hc))
    have hcb' : c < b := lt_of_le_of_ne hcab.2 (fun h => hbc (h ▸ hc))
    obtain ⟨V, O, hO, ε, hε, hL⟩ := hlens c hc
    obtain ⟨a', ha'1, ha'2⟩ := exists_between (max_lt hac' (sub_lt_self c hε))
    obtain ⟨b', hb'1, hb'2⟩ := exists_between (lt_min hcb' (lt_add_of_pos_right c hε))
    have haa : a ≤ a' := (le_max_left _ _).trans ha'1.le
    have hbb : b' ≤ b := hb'2.le.trans (min_le_left _ _)
    have hab' : a' ≤ b' := (ha'2.trans hb'1).le
    have hreg₁ : ∀ x ∈ Icc a a', x ∉ crit := by
      intro x hx hxc
      have hxe : x = c := hsub ⟨hxc, hx.1, hx.2.trans (ha'2.le.trans hcb'.le)⟩ ⟨hc, hcab⟩
      rw [hxe] at hx
      exact absurd hx.2 (not_le.mpr ha'2)
    have hreg₂ : ∀ x ∈ Icc b' b, x ∉ crit := by
      intro x hx hxc
      have hxe : x = c := hsub ⟨hxc, (hac'.le.trans hb'1.le).trans hx.1, hx.2⟩ ⟨hc, hcab⟩
      rw [hxe] at hx
      exact absurd hx.1 (not_le.mpr hb'1)
    obtain ⟨D₁⟩ := hreg a a' b' ha haa hab' hreg₁
    obtain ⟨D₂⟩ := hreg b' b b (ha.trans_le (haa.trans hab')) hbb le_rfl hreg₂
    obtain ⟨L, hLh⟩ := hL a' b' ((le_max_right _ _).trans_lt ha'1) ha'2 hb'1
      (hb'2.trans_le (min_le_right _ _))
    exact crossWK_zero_of_tight F haa hab' hbb D₁ D₂ q
      (fun z' => crossWK_zero_of_localLens F hab' L hLh O hO q z') z
  · have hreg₀ : ∀ x ∈ Icc a b, x ∉ crit := fun x hx hxc => hne ⟨x, hxc, hx⟩
    obtain ⟨D⟩ := hreg a b b ha hab le_rfl hreg₀
    rw [HR_borelInv_eq_zero (crossCommuting F hab) (fun k y => crossing_eq_zero F hab D k y) q z,
      map_zero]

section Shortening

variable {F} {b : ℝ} (S : Shortening.Data F b)

/-- The local lens of a shortening commuting with the half rotation is compatible with the half
rotation. -/
theorem halfLens_localLens (hS : HalfComm S) {a a' : ℝ} (V : Set (Loops n)) (ha : 0 < a)
    (ha' : a' < a) (hab : a ≤ b)
    (hloc : ∀ x : lev F b, a' < Real.sqrt (energy F (S.D x : SphereLoop n)) →
      (x : Loops n) ∈ V) : HalfLens F (localLens S V ha ha' hab hloc) where
  Y_half := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩, ?_, rfl⟩
    change Real.sqrt (energy F (S.D ⟨half +ᵥ (x : SphereLoop n),
      half_mem_lev F x.2⟩ : SphereLoop n)) < a
    rw [hS x, energy_vadd]
    exact hx
  N_half := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨half +ᵥ (x : SphereLoop n), half_mem_lev F x.2⟩, ?_, rfl⟩
    change a' < Real.sqrt (energy F (S.D ⟨half +ᵥ (x : SphereLoop n),
      half_mem_lev F x.2⟩ : SphereLoop n))
    rw [hS x, energy_vadd]
    exact hx
  half_comm := hS

end Shortening

end

end Finsler.BorelLocalK
