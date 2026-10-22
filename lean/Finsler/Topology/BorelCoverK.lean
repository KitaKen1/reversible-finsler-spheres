module

public import Finsler.Topology.BorelFreeVW
public import Finsler.Topology.BorelLocalK
public import Finsler.Topology.SmallLevel

/-! The operator U = v(v + w) on K-Borel cohomology and finite covers by sets of stabilizer
type. A set of loops is split by the half rotation if it is covered by two open sets, disjoint
on it, which the half rotation exchanges. If the reversal keeps the two pieces, the class v of
the half rotation acts as zero on the K-Borel cohomology of every pair of invariant sets inside;
if the reversal exchanges them, v and the reflection class w agree there. In both cases
U = v(v + w) acts as zero. The operator U is natural for restriction. For nested invariant sets
s ⊆ t ⊆ u the K-Borel cochains of (u, t), (u, s), (t, s) form a short exact sequence. Hence, if
the k-th power of U vanishes on the K-Borel cohomology of (t, s) and V is an open invariant set
split in one of the two ways, the (k+1)-st power of U vanishes on that of (t ∪ V, s), by
exactness and excision; by induction, for an open invariant set N and a list of such sets, the
power of U given by the length of the list vanishes on the K-Borel cohomology of the pair of N
and the union. -/

@[expose] public section

namespace Finsler.BorelCoverK

open CategoryTheory Set Topology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.BorelDeformation Finsler.BorelLens Finsler.AvoidPoint
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelFreeK Finsler.BorelFreeV
open Finsler.BorelFreeVW Finsler.BorelLocalK

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### The operator U and its powers -/

section Operator

variable {K L : InvComplex}

/-- The operator v(v + w) on the Borel cohomology of an iterated complex. -/
def opU (S : Commuting K) (q : ℕ) : HR (borelInv S) q →ₗ[ZMod 2] HR (borelInv S) (q + 1 + 1) :=
  w (borelInv S) (q + 1) ∘ₗ (w (borelInv S) q + innerStep S q)

theorem opU_apply (S : Commuting K) (q : ℕ) (x : HR (borelInv S) q) :
    opU S q x = w (borelInv S) (q + 1) (w (borelInv S) q x + innerStep S q x) := rfl

/-- The class x is annihilated by the k-th power of U. -/
def Ann (S : Commuting K) : ℕ → (q : ℕ) → HR (borelInv S) q → Prop
  | 0, _, x => x = 0
  | k + 1, q, x => Ann S k (q + 1 + 1) (opU S q x)

theorem ann_zero (S : Commuting K) (k : ℕ) : ∀ q : ℕ, Ann S k q 0 := by
  induction k with
  | zero => exact fun _ => rfl
  | succ k ih =>
    intro q
    change Ann S k (q + 1 + 1) (opU S q 0)
    rw [map_zero]
    exact ih (q + 1 + 1)

variable {SK : Commuting K} {SL : Commuting L} (Φ : CommHom SK SL)

/-- The operator U is natural. -/
theorem HRmap_opU (q : ℕ) (x : HR (borelInv SK) q) :
    HRmap (borelHom Φ) (q + 1 + 1) (opU SK q x) = opU SL q (HRmap (borelHom Φ) q x) := by
  rw [opU_apply, opU_apply, HRmap_w, map_add, HRmap_w, HRmap_innerStep]

theorem ann_map (k : ℕ) : ∀ (q : ℕ) (x : HR (borelInv SK) q), Ann SK k q x →
    Ann SL k q (HRmap (borelHom Φ) q x) := by
  induction k with
  | zero =>
    intro q x hx
    change HRmap (borelHom Φ) q x = 0
    rw [show x = 0 from hx, map_zero]
  | succ k ih =>
    intro q x hx
    change Ann SL k (q + 1 + 1) (opU SL q (HRmap (borelHom Φ) q x))
    rw [← HRmap_opU]
    exact ih _ _ hx

theorem ann_of_injective (hinj : ∀ q, Function.Injective (HRmap (borelHom Φ) q)) (k : ℕ) :
    ∀ (q : ℕ) (x : HR (borelInv SK) q), Ann SL k q (HRmap (borelHom Φ) q x) → Ann SK k q x := by
  induction k with
  | zero =>
    intro q x hx
    apply hinj q
    rw [map_zero]
    exact hx
  | succ k ih =>
    intro q x hx
    change Ann SL k (q + 1 + 1) (opU SL q (HRmap (borelHom Φ) q x)) at hx
    rw [← HRmap_opU] at hx
    exact ih _ _ hx

/-- In an exact sequence G' → G → G'' of iterated Borel cohomology, if U vanishes on G' and the
k-th power of U vanishes on G'', the (k+1)-st power of U vanishes on G. -/
theorem ann_of_exact {K' K'' : InvComplex} {S' : Commuting K'} {S : Commuting K}
    {S'' : Commuting K''} (I : CommHom S' S) (P : CommHom S S'')
    (hex : ∀ (q : ℕ) (x : HR (borelInv S) q), HRmap (borelHom P) q x = 0 →
      ∃ z, HRmap (borelHom I) q z = x)
    (hU : ∀ (q : ℕ) (z : HR (borelInv S') q), opU S' q z = 0) (k : ℕ) :
    ∀ (q : ℕ) (x : HR (borelInv S) q), Ann S'' k q (HRmap (borelHom P) q x) →
      Ann S (k + 1) q x := by
  induction k with
  | zero =>
    intro q x hx
    obtain ⟨z, rfl⟩ := hex q x hx
    change opU S q (HRmap (borelHom I) q z) = 0
    rw [← HRmap_opU, hU, map_zero]
  | succ k ih =>
    intro q x hx
    change Ann S'' k (q + 1 + 1) (opU S'' q (HRmap (borelHom P) q x)) at hx
    rw [← HRmap_opU] at hx
    exact ih _ _ hx

end Operator

/-! ### Invariant sets of loops -/

/-- A set of loops invariant under the reversal and the half rotation. -/
structure KInv (A : Set (Loops n)) : Prop where
  rev_mem : ∀ u : SphereLoop n, u ∈ A → reverseSphere u ∈ A
  half_mem : ∀ u : SphereLoop n, u ∈ A → half +ᵥ u ∈ A

theorem kInv_union {A B : Set (Loops n)} (hA : KInv A) (hB : KInv B) : KInv (A ∪ B) :=
  ⟨fun u hu => hu.elim (fun h => Or.inl (hA.rev_mem u h)) (fun h => Or.inr (hB.rev_mem u h)),
    fun u hu => hu.elim (fun h => Or.inl (hA.half_mem u h)) (fun h => Or.inr (hB.half_mem u h))⟩

theorem kInv_inter {A B : Set (Loops n)} (hA : KInv A) (hB : KInv B) : KInv (A ∩ B) :=
  ⟨fun u hu => ⟨hA.rev_mem u hu.1, hB.rev_mem u hu.2⟩,
    fun u hu => ⟨hA.half_mem u hu.1, hB.half_mem u hu.2⟩⟩

/-- The two commuting involutions on the cochains of a pair of invariant sets of loops. -/
abbrev kCommuting {s t : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t) :
    Commuting (ofPair (pairOf hst) (revSub hst hs.rev_mem ht.rev_mem)
      (revSub_sq hst hs.rev_mem ht.rev_mem)) :=
  subCommuting hst hs.rev_mem ht.rev_mem hs.half_mem ht.half_mem

/-- Restriction of K-Borel cochains between pairs of invariant sets of loops. -/
abbrev kHom {s t s' t' : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    (hst' : s' ⊆ t') (hs' : KInv s') (ht' : KInv t') (hss : s ⊆ s') (htt : t ⊆ t') :
    CommHom (kCommuting hst' hs' ht') (kCommuting hst hs ht) :=
  subCommHom hst hs.rev_mem ht.rev_mem hs.half_mem ht.half_mem hst' hs'.rev_mem ht'.rev_mem
    hs'.half_mem ht'.half_mem hss htt

/-! ### Sets split by the half rotation -/

/-- A set of loops covered by two open sets, disjoint on it, which the half rotation
exchanges. -/
structure HalfSplit (V : Set (Loops n)) where
  pos : Set (Loops n)
  neg : Set (Loops n)
  pos_open : IsOpen pos
  neg_open : IsOpen neg
  cover : V ⊆ pos ∪ neg
  disjoint : ∀ u, u ∈ V → u ∈ pos → u ∈ neg → False
  half_pos : ∀ u : SphereLoop n, u ∈ pos → half +ᵥ u ∈ neg
  half_neg : ∀ u : SphereLoop n, u ∈ neg → half +ᵥ u ∈ pos

/-- The reversal keeps the two pieces. -/
structure RevKeeps {V : Set (Loops n)} (O : HalfSplit V) : Prop where
  rev_pos : ∀ u : SphereLoop n, u ∈ O.pos → reverseSphere u ∈ O.pos
  rev_neg : ∀ u : SphereLoop n, u ∈ O.neg → reverseSphere u ∈ O.neg

/-- The reversal exchanges the two pieces. -/
structure RevSwaps {V : Set (Loops n)} (O : HalfSplit V) : Prop where
  rev_pos : ∀ u : SphereLoop n, u ∈ O.pos → reverseSphere u ∈ O.neg
  rev_neg : ∀ u : SphereLoop n, u ∈ O.neg → reverseSphere u ∈ O.pos

section Types

variable {s t V : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t) (O : HalfSplit V)
  (htV : t ⊆ V)

include htV in
theorem isClopen_pos : IsClopen ({x : t | (x : Loops n) ∈ O.pos} : Set t) := by
  have hcompl : ({x : t | (x : Loops n) ∈ O.pos} : Set t)ᶜ =
      {x : t | (x : Loops n) ∈ O.neg} := by
    ext x
    constructor
    · intro hx
      rcases O.cover (htV x.2) with h | h
      · exact absurd h hx
      · exact h
    · intro hx hpos
      exact O.disjoint _ (htV x.2) hpos hx
  refine ⟨?_, O.pos_open.preimage continuous_subtype_val⟩
  rw [← isOpen_compl_iff, hcompl]
  exact O.neg_open.preimage continuous_subtype_val

include ht htV in
theorem half_swap (x : t) :
    half +ᵥ (x.1 : SphereLoop n) ∈ O.pos ↔ (x.1 : Loops n) ∉ O.pos := by
  constructor
  · intro hx hpos
    exact O.disjoint _ (htV (ht.half_mem _ x.2)) hx (O.half_pos _ hpos)
  · intro hx
    rcases O.cover (htV x.2) with h | h
    · exact absurd h hx
    · exact O.half_neg _ h

include htV in
/-- If the reversal keeps the two pieces, the class of the half rotation acts as zero on the
K-Borel cohomology of pairs of invariant sets inside. -/
theorem subV_zero (hO : RevKeeps O) (q : ℕ) (y : HR (borelInv (kCommuting hst hs ht)) q) :
    w (borelInv (kCommuting hst hs ht)) q y = 0 := by
  refine outerW_eq_zero_of_isClopen (pairOf hst) (revSub hst hs.rev_mem ht.rev_mem)
    (halfSub hst hs.half_mem ht.half_mem) (revSub_sq hst hs.rev_mem ht.rev_mem)
    (halfSub_sq hst hs.half_mem ht.half_mem)
    (halfSub_rev hst hs.rev_mem ht.rev_mem hs.half_mem ht.half_mem)
    {x : t | (x : Loops n) ∈ O.pos} (isClopen_pos O htV) (fun x => half_swap ht O htV x)
    (fun x => ⟨fun hx => ?_, fun hx => hO.rev_pos _ hx⟩) q y
  have h : reverseSphere (reverseSphere (x.1 : SphereLoop n)) ∈ O.pos := hO.rev_pos _ hx
  rw [reverseSphere_involutive] at h
  exact h

include htV in
/-- If the reversal exchanges the two pieces, the class of the half rotation and the reflection
class agree on the K-Borel cohomology of pairs of invariant sets inside. -/
theorem subVW_eq (hO : RevSwaps O) (q : ℕ) (y : HR (borelInv (kCommuting hst hs ht)) q) :
    w (borelInv (kCommuting hst hs ht)) q y = innerStep (kCommuting hst hs ht) q y := by
  refine outerW_eq_innerW_of_isClopen (pairOf hst) (revSub hst hs.rev_mem ht.rev_mem)
    (halfSub hst hs.half_mem ht.half_mem) (revSub_sq hst hs.rev_mem ht.rev_mem)
    (halfSub_sq hst hs.half_mem ht.half_mem)
    (halfSub_rev hst hs.rev_mem ht.rev_mem hs.half_mem ht.half_mem)
    {x : t | (x : Loops n) ∈ O.pos} (isClopen_pos O htV) (fun x => half_swap ht O htV x)
    (fun x => ⟨fun hx hpos => ?_, fun hx => ?_⟩) q y
  · exact O.disjoint _ (htV (ht.rev_mem _ x.2)) hx (hO.rev_pos _ hpos)
  · rcases O.cover (htV x.2) with h | h
    · exact absurd h hx
    · exact hO.rev_neg _ h

include htV in
/-- In both cases U acts as zero. -/
theorem opU_zero (hO : RevKeeps O ∨ RevSwaps O) (q : ℕ)
    (y : HR (borelInv (kCommuting hst hs ht)) q) : opU (kCommuting hst hs ht) q y = 0 := by
  rw [opU_apply]
  rcases hO with hO | hO
  · exact subV_zero hst hs ht O htV hO (q + 1) _
  · rw [subVW_eq hst hs ht O htV hO q y, two_eq_zero_of_mod, map_zero]

end Types

/-! ### Triples and covers -/

section Triple

variable {s t u : Set (Loops n)} (hst : s ⊆ t) (htu : t ⊆ u) (hs : KInv s) (ht : KInv t)
  (hu : KInv u)

/-- The actual relative cochains of (u, t), (u, s), (t, s) form a short exact sequence. -/
theorem shortExact_incl :
    BorelExact.ShortExact (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl).φ
      (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu).φ := by
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

/-- Exactness of the K-Borel sequence of a triple of invariant sets at the middle group. -/
theorem exact_triple (q : ℕ) (x : HR (borelInv (kCommuting (hst.trans htu) hs hu)) q)
    (hx : HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) q x = 0) :
    ∃ z : HR (borelInv (kCommuting htu ht hu)) q,
      HRmap (borelHom (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl)) q z = x :=
  BorelExact.exact_mid (BorelQuasiIso.shortExact_iterated
    (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl)
    (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)
    (shortExact_incl hst htu hs ht hu)) q x hx

end Triple

/-- Adding an open invariant set split in one of the two ways: if the k-th power of U vanishes
on the K-Borel cohomology of (t, s), the (k+1)-st power vanishes on that of (t ∪ V, s). -/
theorem ann_union {s t V : Set (Loops n)} (hst : s ⊆ t) (hs : KInv s) (ht : KInv t)
    (hV : KInv V) (hto : IsOpen t) (hVo : IsOpen V) (O : HalfSplit V)
    (hO : RevKeeps O ∨ RevSwaps O) (k : ℕ)
    (h : ∀ (q : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q),
      Ann (kCommuting hst hs ht) k q x) (q : ℕ)
    (x : HR (borelInv (kCommuting (hst.trans subset_union_left) hs (kInv_union ht hV))) q) :
    Ann (kCommuting (hst.trans subset_union_left) hs (kInv_union ht hV)) (k + 1) q x := by
  have htu : t ⊆ t ∪ V := subset_union_left
  have hE : V ∩ t ⊆ V ∩ (t ∪ V) := inter_subset_inter_right V htu
  have hbij := bijective_subCommHom hE (kInv_inter hV ht).rev_mem (kInv_inter hV (kInv_union ht hV)).rev_mem
    (kInv_inter hV ht).half_mem (kInv_inter hV (kInv_union ht hV)).half_mem htu ht.rev_mem
    (kInv_union ht hV).rev_mem ht.half_mem (kInv_union ht hV).half_mem inter_subset_right
    inter_subset_right
    (fun j => bijective_nativePull_excision V htu hto hVo subset_rfl j)
  have hU : ∀ (j : ℕ) (z : HR (borelInv (kCommuting htu ht (kInv_union ht hV))) j),
      opU (kCommuting htu ht (kInv_union ht hV)) j z = 0 := by
    intro j z
    apply (hbij (j + 1 + 1)).1
    rw [map_zero]
    exact (HRmap_opU (kHom hE (kInv_inter hV ht) (kInv_inter hV (kInv_union ht hV)) htu ht (kInv_union ht hV)
      inter_subset_right inter_subset_right) j z).trans
      (opU_zero hE (kInv_inter hV ht) (kInv_inter hV (kInv_union ht hV)) O inter_subset_left hO j _)
  exact ann_of_exact (kHom (hst.trans htu) hs (kInv_union ht hV) htu ht (kInv_union ht hV) hst subset_rfl)
    (kHom hst hs ht (hst.trans htu) hs (kInv_union ht hV) subset_rfl htu)
    (fun j y hy => exact_triple hst htu hs ht (kInv_union ht hV) j y hy) hU k q x (h q _)

/-- An open invariant set of loops split by the half rotation in one of the two ways. -/
structure Typed (n : ℕ) where
  V : Set (Loops n)
  isOpen : IsOpen V
  inv : KInv V
  split : HalfSplit V
  type : RevKeeps split ∨ RevSwaps split

/-- The union of a set and a list of typed sets. -/
def unionOf (N : Set (Loops n)) : List (Typed n) → Set (Loops n)
  | [] => N
  | T :: l => unionOf N l ∪ T.V

theorem subset_unionOf (N : Set (Loops n)) (l : List (Typed n)) : N ⊆ unionOf N l := by
  induction l with
  | nil => exact subset_rfl
  | cons T l ih => exact ih.trans subset_union_left

theorem unionOf_isOpen {N : Set (Loops n)} (hN : IsOpen N) (l : List (Typed n)) :
    IsOpen (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact ih.union T.isOpen

theorem unionOf_inv {N : Set (Loops n)} (hN : KInv N) (l : List (Typed n)) :
    KInv (unionOf N l) := by
  induction l with
  | nil => exact hN
  | cons T l ih => exact kInv_union ih T.inv

/-- The K-Borel cohomology of a pair of equal invariant sets vanishes. -/
theorem HR_eq_zero_of_subset {s t : Set (Loops n)} (hst : s ⊆ t) (hts : t ⊆ s) (hs : KInv s)
    (ht : KInv t) (q : ℕ) (x : HR (borelInv (kCommuting hst hs ht)) q) : x = 0 := by
  refine HR_borelInv_eq_zero (kCommuting hst hs ht) (fun k y => ?_) q x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [mk_eq_zero_iff_bcoboundary]
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero]
  funext j
  exact (Finsler.SmallLevel.relative_eq_zero hst hts j _).symm

/-- For an open invariant set N and a list of typed sets, the power of U given by the length of
the list vanishes on the K-Borel cohomology of the pair of the union and N. -/
theorem ann_unionOf {N : Set (Loops n)} (hN : KInv N) (hNo : IsOpen N) (l : List (Typed n)) :
    ∀ (q : ℕ) (x : HR (borelInv (kCommuting (subset_unionOf N l) hN (unionOf_inv hN l))) q),
      Ann (kCommuting (subset_unionOf N l) hN (unionOf_inv hN l)) l.length q x := by
  induction l with
  | nil =>
    intro q x
    exact HR_eq_zero_of_subset (subset_unionOf N []) subset_rfl hN (unionOf_inv hN []) q x
  | cons T l ih =>
    intro q x
    exact ann_union (subset_unionOf N l) hN (unionOf_inv hN l) T.inv (unionOf_isOpen hNo l)
      T.isOpen T.split T.type l.length ih q x

/-- If an invariant set X is the union of an open invariant set N and a list of typed sets,
the power of U given by the length of the list vanishes on the K-Borel cohomology of
(X, N). -/
theorem ann_of_cover {N X : Set (Loops n)} (hNX : N ⊆ X) (hN : KInv N) (hX : KInv X)
    (hNo : IsOpen N) (l : List (Typed n)) (h1 : X ⊆ unionOf N l) (h2 : unionOf N l ⊆ X) (q : ℕ)
    (x : HR (borelInv (kCommuting hNX hN hX)) q) : Ann (kCommuting hNX hN hX) l.length q x := by
  have hbij := bijective_subCommHom hNX hN.rev_mem hX.rev_mem hN.half_mem hX.half_mem
    (subset_unionOf N l) hN.rev_mem (unionOf_inv hN l).rev_mem hN.half_mem
    (unionOf_inv hN l).half_mem subset_rfl h1
    (fun j => bijective_nativePull_of_eq hNX (subset_unionOf N l) subset_rfl h1 subset_rfl h2 j)
  obtain ⟨y, rfl⟩ := (hbij q).2 x
  exact ann_map (kHom hNX hN hX (subset_unionOf N l) hN (unionOf_inv hN l) subset_rfl h1)
    l.length q y (ann_unionOf hN hNo l q y)

end

end Finsler.BorelCoverK
