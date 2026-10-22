module

public import Finsler.Topology.BorelLocal
public import Finsler.Topology.BorelLens
public import Finsler.Topology.NilpotentW
public import Finsler.Topology.SmallLevel
public import Finsler.Topology.BorelQuasiIso
public import Finsler.Topology.PairTriple
public import Finsler.Topology.BorelInvariance

/-! Powers of w from covers by oriented sets, for any space with an involution.

The cover lemma of `CoverW` (written there for the reversal of loops) for an arbitrary space W
with a continuous involution ι. For invariant sets s ⊆ t ⊆ u the relative cochains of
(u, t), (u, s), (t, s) form a short exact sequence of involutive complexes. If V is an open
invariant set with an orientation (two open sets covering V, disjoint on V and exchanged by ι)
and t is open, the restriction from (t ∪ V, t) to (V ∩ (t ∪ V), V ∩ t) is an excision and w acts
as zero on the latter pair. Hence a vanishing power w^k on (t, s) gives w^{k+1} = 0 on
(t ∪ V, s), and if X is the union of an open invariant set N and k oriented open invariant sets,
w^k vanishes on the reflection Borel cohomology of (X, N). -/

@[expose] public section

namespace Finsler.InvCover

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.BorelDeformation Finsler.BorelLens Finsler.NilpotentW
open Finsler.PairTriple Finsler.BorelComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} (ι : C(W, W)) (hι : ∀ x, ι (ι x) = x)

/-- An invariant set. -/
def Inv (A : Set W) : Prop := ∀ x ∈ A, ι x ∈ A

variable {ι}

theorem inv_union {A B : Set W} (hA : Inv ι A) (hB : Inv ι B) : Inv ι (A ∪ B) :=
  fun x hx => hx.elim (fun h => Or.inl (hA x h)) (fun h => Or.inr (hB x h))

theorem inv_inter {A B : Set W} (hA : Inv ι A) (hB : Inv ι B) : Inv ι (A ∩ B) :=
  fun x hx => ⟨hA x hx.1, hB x hx.2⟩

/-- The involution on an invariant set. -/
def invSet {t : Set W} (ht : Inv ι t) : C(t, t) :=
  ⟨fun x => ⟨ι x, ht _ x.2⟩, (ι.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The involution of a pair of invariant sets. -/
def invSub {s t : Set W} (hst : s ⊆ t) (hs : Inv ι s) (ht : Inv ι t) : pairOf hst ⟶ pairOf hst :=
  pairMap hst hst (invSet ht) (fun _ hx => hs _ hx)

include hι in
theorem invSub_sq {s t : Set W} (hst : s ⊆ t) (hs : Inv ι s) (ht : Inv ι t) :
    invSub hst hs ht ≫ invSub hst hs ht = 𝟙 (pairOf hst) := by
  have h : (invSet ht).comp (invSet ht) = ContinuousMap.id t := by
    ext x
    exact congrArg Subtype.val (Subtype.ext (hι x) : (⟨ι (ι x), ht _ (ht _ x.2)⟩ : t) = x)
  exact (pairMap_comp hst hst hst (invSet ht) (invSet ht) (fun _ hx => hs _ hx)
    (fun _ hx => hs _ hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

/-- The involutive complex of relative cochains of a pair of invariant sets. -/
abbrev iC {s t : Set W} (hst : s ⊆ t) (hs : Inv ι s) (ht : Inv ι t) : InvComplex :=
  ofPair (pairOf hst) (invSub hst hs ht) (invSub_sq hι hst hs ht)

section Subpairs

variable {s t s' t' : Set W} (hst : s ⊆ t) (hst' : s' ⊆ t') (hs : Inv ι s) (ht : Inv ι t)
  (hs' : Inv ι s') (ht' : Inv ι t') (hss : s ⊆ s') (htt : t ⊆ t')

theorem inclPair_equivariant :
    inclPair hst hst' hss htt ≫ invSub hst' hs' ht' = invSub hst hs ht ≫ inclPair hst hst' hss htt := by
  ext : 2 <;> rfl

/-- Restriction of cochains between pairs of invariant sets. -/
abbrev subHom : InvHom (iC hι hst' hs' ht') (iC hι hst hs ht) :=
  pullHom (invSub_sq hι hst hs ht) (invSub_sq hι hst' hs' ht') (inclPair hst hst' hss htt)
    (inclPair_equivariant hst hst' hs ht hs' ht' hss htt)

/-- An inclusion of pairs of invariant sets which is an isomorphism on relative cohomology is an
isomorphism on reflection Borel cohomology. -/
theorem bijective_subHom
    (h : ∀ k, Function.Bijective (nativePull (inclPair hst hst' hss htt) k)) :
    ∀ k, Function.Bijective (HRmap (subHom hι hst hst' hs ht hs' ht' hss htt) k) :=
  Finsler.BorelInvariance.bijective_HRmap (invSub_sq hι hst hs ht) (invSub_sq hι hst' hs' ht')
    (inclPair hst hst' hss htt) (inclPair_equivariant hst hst' hs ht hs' ht' hss htt) h

end Subpairs

/-! ### Transport of powers of w -/

section Transport

variable {K L : InvComplex} (φ : InvHom K L)

theorem wPow_zero_of_injective (k q : ℕ) (hinj : Function.Injective (HRmap φ (q + k)))
    (h : ∀ y : HR L q, wPow L q k y = 0) (x : HR K q) : wPow K q k x = 0 :=
  hinj (by rw [HRmap_wPow, h, map_zero])

end Transport

/-! ### Triples -/

section Triple

variable {s t u : Set W} (hst : s ⊆ t) (htu : t ⊆ u) (hs : Inv ι s) (ht : Inv ι t)
  (hu : Inv ι u)

/-- The relative cochains of (u, t), (u, s), (t, s) form a short exact sequence. -/
theorem shortExact_incl :
    BorelExact.ShortExact (subHom hι (hst.trans htu) htu hs hu ht hu hst subset_rfl)
      (subHom hι hst (hst.trans htu) hs ht hs hu subset_rfl htu) := by
  have e1 : inclPair (hst.trans htu) htu hst subset_rfl = relPair hst htu := by
    ext : 2 <;> rfl
  have e2 : inclPair hst (hst.trans htu) subset_rfl htu = incPair hst htu := by
    ext : 2 <;> rfl
  refine ⟨fun j => ?_, fun j => ?_, fun j z => ?_, fun j x hx => ?_⟩
  · change Function.Injective
      (RelativeCupCochain.pullback (inclPair (hst.trans htu) htu hst subset_rfl) j)
    rw [e1]
    exact rel_injective hst htu j
  · change Function.Surjective
      (RelativeCupCochain.pullback (inclPair hst (hst.trans htu) subset_rfl htu) j)
    rw [e2]
    exact inc_surjective hst htu j
  · change RelativeCupCochain.pullback (inclPair hst (hst.trans htu) subset_rfl htu) j
      (RelativeCupCochain.pullback (inclPair (hst.trans htu) htu hst subset_rfl) j z) = 0
    rw [e1, e2]
    exact rel_inc_zero hst htu j z
  · change RelativeCupCochain.pullback (inclPair hst (hst.trans htu) subset_rfl htu) j x = 0
      at hx
    rw [e2] at hx
    obtain ⟨ψ, hψ⟩ := inc_exact hst htu j x hx
    refine ⟨ψ, ?_⟩
    change RelativeCupCochain.pullback (inclPair (hst.trans htu) htu hst subset_rfl) j ψ = x
    rw [e1]
    exact hψ

end Triple

/-! ### Oriented sets -/

variable (ι) in
/-- An orientation of a set V: two open sets covering V, disjoint on V and exchanged by ι. -/
structure Orient (V : Set W) where
  pos : Set W
  neg : Set W
  pos_open : IsOpen pos
  neg_open : IsOpen neg
  cover : V ⊆ pos ∪ neg
  disjoint : ∀ x, x ∈ V → x ∈ pos → x ∈ neg → False
  swap_pos : ∀ x, x ∈ pos → ι x ∈ neg
  swap_neg : ∀ x, x ∈ neg → ι x ∈ pos

/-- On a pair of invariant sets inside an oriented set, w acts as zero. -/
theorem subW_zero {V : Set W} (O : Orient ι V) {s t : Set W} (hst : s ⊆ t) (hs : Inv ι s)
    (ht : Inv ι t) (htV : t ⊆ V) (q : ℕ) (y : HR (iC hι hst hs ht) q) :
    w (iC hι hst hs ht) q y = 0 := by
  have hcompl : ({x : t | (x : W) ∈ O.pos} : Set t)ᶜ = {x : t | (x : W) ∈ O.neg} := by
    ext x
    constructor
    · intro hx
      rcases O.cover (htV x.2) with h | h
      · exact absurd h hx
      · exact h
    · intro hx hpos
      exact O.disjoint _ (htV x.2) hpos hx
  have hclosed : IsClosed ({x : t | (x : W) ∈ O.pos} : Set t) := by
    rw [← isOpen_compl_iff, hcompl]
    exact O.neg_open.preimage continuous_subtype_val
  have hopen : IsOpen ({x : t | (x : W) ∈ O.pos} : Set t) :=
    O.pos_open.preimage continuous_subtype_val
  refine Finsler.BorelFree.w_eq_zero_of_isClopen (pairOf hst) (invSub hst hs ht)
    (invSub_sq hι hst hs ht) {x : t | (x : W) ∈ O.pos} ⟨hclosed, hopen⟩
    (fun x => ⟨fun hrx hx => ?_, fun hx => ?_⟩) q y
  · exact O.disjoint _ (htV (ht _ x.2)) hrx (O.swap_pos _ hx)
  · rcases O.cover (htV x.2) with h | h
    · exact absurd h hx
    · exact O.swap_neg _ h

/-! ### Covers -/

/-- Adding an oriented open invariant set: if w^k vanishes on the reflection Borel cohomology
of (t, s), then w^{k+1} vanishes on that of (t ∪ V, s). -/
theorem wPow_union {s t V : Set W} (hst : s ⊆ t) (hs : Inv ι s) (ht : Inv ι t)
    (hV : Inv ι V) (hto : IsOpen t) (hVo : IsOpen V) (O : Orient ι V) (k : ℕ)
    (h : ∀ (q : ℕ) (x : HR (iC hι hst hs ht) q), wPow (iC hι hst hs ht) q k x = 0) (q : ℕ)
    (x : HR (iC hι (hst.trans subset_union_left) hs (inv_union ht hV)) q) :
    wPow (iC hι (hst.trans subset_union_left) hs (inv_union ht hV)) q (k + 1) x = 0 := by
  have htu : t ⊆ t ∪ V := subset_union_left
  have hu := inv_union ht hV
  have hex := shortExact_incl hι hst htu hs ht hu
  have h1 : HRmap (subHom hι hst (hst.trans htu) hs ht hs hu subset_rfl htu) (q + k)
      (wPow _ q k x) = 0 := by
    rw [HRmap_wPow, h]
  obtain ⟨z, hz⟩ := BorelExact.exact_mid hex (q + k) _ h1
  have hE : V ∩ t ⊆ V ∩ (t ∪ V) := inter_subset_inter_right V htu
  have hbij := bijective_subHom hι hE htu (inv_inter hV ht) (inv_inter hV hu) ht hu
    inter_subset_right inter_subset_right
    (fun j => bijective_nativePull_excision V htu hto hVo subset_rfl j)
  have hwz : w _ (q + k) z = 0 := by
    apply (hbij (q + k + 1)).1
    rw [map_zero, HRmap_w]
    exact subW_zero hι O hE (inv_inter hV ht) (inv_inter hV hu) inter_subset_left (q + k) _
  rw [wPow_succ, ← hz, ← HRmap_w, hwz, map_zero]

variable (ι) in
/-- An open invariant set with an orientation. -/
structure Oriented where
  V : Set W
  isOpen : IsOpen V
  inv : Inv ι V
  orient : Orient ι V

/-- The union of a set and a list of oriented sets. -/
def unionOf (N : Set W) : List (Oriented ι) → Set W
  | [] => N
  | T :: l => unionOf N l ∪ T.V

theorem subset_unionOf (N : Set W) (l : List (Oriented ι)) : N ⊆ unionOf N l := by
  induction l with
  | nil => exact subset_rfl
  | cons T l ih => exact ih.trans subset_union_left

theorem unionOf_isOpen {N : Set W} (hN : IsOpen N) (l : List (Oriented ι)) :
    IsOpen (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact ih.union T.isOpen

theorem unionOf_inv {N : Set W} (hN : Inv ι N) (l : List (Oriented ι)) :
    Inv ι (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact inv_union ih T.inv

/-- The reflection Borel cohomology of a pair of equal sets vanishes. -/
theorem HR_eq_zero_of_subset {s t : Set W} (hst : s ⊆ t) (hts : t ⊆ s) (hs : Inv ι s)
    (ht : Inv ι t) (q : ℕ) (x : HR (iC hι hst hs ht) q) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_zero_iff_bcoboundary]
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero]
  funext j
  exact (Finsler.SmallLevel.relative_eq_zero hst hts j _).symm

/-- For an open invariant set N and a list of oriented sets, the power of w given by the length
of the list vanishes on the reflection Borel cohomology of the pair of the union and N. -/
theorem wPow_unionOf {N : Set W} (hN : Inv ι N) (hNo : IsOpen N) (l : List (Oriented ι)) :
    ∀ (q : ℕ) (x : HR (iC hι (subset_unionOf N l) hN (unionOf_inv hN l)) q),
      wPow (iC hι (subset_unionOf N l) hN (unionOf_inv hN l)) q l.length x = 0 := by
  induction l with
  | nil =>
    intro q x
    exact HR_eq_zero_of_subset hι (subset_unionOf N []) subset_rfl hN (unionOf_inv hN []) q x
  | cons T l ih =>
    intro q x
    exact wPow_union hι (subset_unionOf N l) hN (unionOf_inv hN l) T.inv (unionOf_isOpen hNo l)
      T.isOpen T.orient l.length ih q x

/-- **Covers.** If an invariant set X is the union of an open invariant set N and a list of
oriented sets, the power of w given by the length of the list vanishes on the reflection Borel
cohomology of (X, N). -/
theorem wPow_of_cover {N X : Set W} (hNX : N ⊆ X) (hN : Inv ι N) (hX : Inv ι X)
    (hNo : IsOpen N) (l : List (Oriented ι)) (h1 : X ⊆ unionOf N l) (h2 : unionOf N l ⊆ X)
    (q : ℕ) (x : HR (iC hι hNX hN hX) q) : wPow (iC hι hNX hN hX) q l.length x = 0 := by
  have hbij := bijective_subHom hι hNX (subset_unionOf N l) hN hX hN (unionOf_inv hN l)
    subset_rfl h1 (fun j => bijective_nativePull_of_eq hNX (subset_unionOf N l) subset_rfl h1
      subset_rfl h2 j)
  obtain ⟨y, rfl⟩ := (hbij q).2 x
  rw [← HRmap_wPow, wPow_unionOf hι hN hNo l q y, map_zero]

end

end Finsler.InvCover
