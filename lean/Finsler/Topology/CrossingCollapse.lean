module

public import Finsler.Topology.TowerSpan
public import Finsler.Topology.OrdinaryDelta

/-! Collapse of reflection Borel crossing sequences from ordinary collapse.

For a degreewise short exact sequence 0 → K' → K → K'' → 0 of involutive complexes the connecting
maps of the Borel and of the ordinary long exact sequences commute with forgetting the action and
with the transfer. Call a degree q a start of K if some Borel class of degree q has nonzero
forgetful image, and an end if the transfer of degree q is nonzero. If the ordinary cohomology of
K has dimension at most one in degree q and does not vanish there, q is a start or an end and not
both. Starts are transported along maps injective on ordinary cohomology, ends backwards along
maps surjective on ordinary cohomology.

Collapse. Suppose that the ordinary cohomology of K'' has dimension at most one in every degree,
that the ordinary connecting map vanishes, and that for every start s of K'' forgetting is
injective on the Borel cohomology of K' in degree s + 1. Then the Borel connecting map vanishes:
by the tower lemma the Borel cohomology of K'' is spanned by the w-powers of start classes, the
connecting map commutes with w, and the connecting image of a start class is detected by its
forgetful image, which is the ordinary connecting image of a class, hence zero. So the Borel
crossing sequence splits into short exact sequences and the dimensions add. In the application
K' is the crossing group of a critical level, whose Borel cohomology vanishes below its lowest
degree and is detected by forgetting there, and the starts of K'' lie below that degree; then the
hypothesis on starts is automatic. No Thom isomorphism and no cup product is used. -/

@[expose] public section

namespace Finsler.CrossingCollapse

open Finsler.BorelCochain Finsler.BorelExact Module

noncomputable section

section Connecting

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

/-- Forgetting the action commutes with the connecting maps. -/
theorem forget_delta (n : ℕ) (x : HR K'' n) :
    forget K' (n + 1) (delta h n x) = OrdinaryDelta.delta h n (forget K'' n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  rw [delta_mk h n c b hb hπb ⟨z, hz⟩ hιz, forget, Submodule.mapQ_apply, forget,
    Submodule.mapQ_apply, OrdinaryDelta.delta, Submodule.mapQ_apply, Submodule.Quotient.eq]
  change z (n + 1) - ret h (n + 1) (K.d n (sec h n ((c : Seq K'') n))) ∈ coboundaries K' (n + 1)
  have hbn : π.f n (b n) = (c : Seq K'') n := congrFun hπb n
  obtain ⟨v, hv⟩ := OrdinaryDelta.d_sec_eq h n ((c : Seq K'') n) (b n) hbn
  have hb1 : b (n + 1) = 0 := hb (n + 1) le_rfl
  have hD : D K b (n + 1) = K.d n (b n) := by
    rw [D_succ, hb1, map_zero, add_zero]
  have hιz' : ι.f (n + 1) (z (n + 1)) = K.d n (b n) := by
    rw [← hD, ← hιz]
    rfl
  rw [hv, ← hιz', ← map_add, ret_incl]
  refine ⟨-v, ?_⟩
  rw [map_neg]
  abel

/-- The connecting maps commute with the transfer. -/
theorem delta_transfer (n : ℕ) (z : H K'' n) :
    delta h n (transfer K'' n z) = transfer K' (n + 1) (OrdinaryDelta.delta h n z) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hx : K''.d n (x : K''.C n) = 0 := x.2
  have hb : (Pi.single n (tr K n (sec h n (x : K''.C n))) : Seq K) ∈ low K (n + 1) :=
    single_mem_low K n _
  have hπb : seqMap π (Pi.single n (tr K n (sec h n (x : K''.C n))) : Seq K) =
      (trCocycle K'' n x : Seq K'') := by
    rw [trCocycle_coe]
    funext j
    rw [seqMap_apply]
    by_cases hj : j = n
    · subst hj
      rw [single_same, single_same, comm_tr, proj_sec]
    · rw [single_ne K hj, single_ne K'' hj, map_zero]
  have hDb : D K (Pi.single n (tr K n (sec h n (x : K''.C n))) : Seq K) =
      Pi.single (n + 1) (tr K (n + 1) (K.d n (sec h n (x : K''.C n)))) := by
    rw [D_single, tr_tr, single_zero_seq, zero_add, tr_d]
  have hιz : seqMap ι (trCocycle K' (n + 1) (OrdinaryDelta.deltaCocycle h n x) : Seq K') =
      D K (Pi.single n (tr K n (sec h n (x : K''.C n))) : Seq K) := by
    rw [trCocycle_coe, hDb]
    funext j
    rw [seqMap_apply]
    by_cases hj : j = n + 1
    · subst hj
      rw [single_same, single_same, comm_tr]
      congr 1
      exact OrdinaryDelta.incl_ret_d_sec h n _ hx
    · rw [single_ne K' hj, single_ne K hj, map_zero]
  rw [transfer, Submodule.mapQ_apply, transfer, OrdinaryDelta.delta, Submodule.mapQ_apply,
    Submodule.mapQ_apply]
  exact delta_mk h n (trCocycle K'' n x) _ hb hπb _ hιz

end Connecting

/-! ### Starts and ends of the Gysin sequence -/

section StartEnd

/-- A degree in which some Borel class has nonzero forgetful image. -/
def IsStart (K : InvComplex) (q : ℕ) : Prop := ∃ y : HR K q, forget K q y ≠ 0

/-- A degree in which the transfer does not vanish. -/
def IsEnd (K : InvComplex) (q : ℕ) : Prop := ∃ z : H K q, transfer K q z ≠ 0

variable {K L : InvComplex}

/-- A degree is an end iff some nonzero Borel class is killed by w. -/
theorem isEnd_iff (q : ℕ) : IsEnd K q ↔ ∃ t : HR K q, t ≠ 0 ∧ w K q t = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨transfer K q z, hz, (exact_w K q _).mpr ⟨z, rfl⟩⟩
  · rintro ⟨t, ht, hwt⟩
    obtain ⟨z, rfl⟩ := (exact_w K q t).mp hwt
    exact ⟨z, ht⟩

/-- In a degree of ordinary dimension at most one with a nonzero class, the degree is a start or
an end. -/
theorem start_or_end {q : ℕ} {z : H K q} (hz : z ≠ 0) : IsStart K q ∨ IsEnd K q := by
  by_cases ht : transfer K q z = 0
  · obtain ⟨y, hy⟩ := (exact_transfer K q z).mp ht
    exact Or.inl ⟨y, by rw [hy]; exact hz⟩
  · exact Or.inr ⟨z, ht⟩

/-- In a degree of ordinary dimension at most one a start is not an end. -/
theorem not_end_of_start {q : ℕ} [FiniteDimensional (ZMod 2) (H K q)]
    (hdim : finrank (ZMod 2) (H K q) ≤ 1) (hs : IsStart K q) : ¬ IsEnd K q := by
  obtain ⟨y, hy⟩ := hs
  rintro ⟨z, hz⟩
  obtain ⟨c, hc⟩ := TowerSpan.exists_smul_of_finrank_le_one hdim hy z
  apply hz
  rw [hc, map_smul, (exact_transfer K q _).mpr ⟨y, rfl⟩, smul_zero]

/-- Starts are transported along maps which are injective on ordinary cohomology. -/
theorem isStart_map (φ : InvHom K L) {q : ℕ} (hinj : Function.Injective (Hmap φ q))
    (hs : IsStart K q) : IsStart L q := by
  obtain ⟨y, hy⟩ := hs
  refine ⟨HRmap φ q y, ?_⟩
  rw [← Hmap_forget]
  intro h0
  exact hy (hinj (by rw [h0, map_zero]))

/-- Ends are transported backwards along maps which are surjective on ordinary cohomology. -/
theorem isEnd_of_map (φ : InvHom K L) {q : ℕ} (hsurj : Function.Surjective (Hmap φ q))
    (he : IsEnd L q) : IsEnd K q := by
  obtain ⟨z, hz⟩ := he
  obtain ⟨z', rfl⟩ := hsurj z
  refine ⟨z', fun h0 => hz ?_⟩
  rw [← HRmap_transfer, h0, map_zero]

/-- Ends are transported along maps which are injective on Borel cohomology. -/
theorem isEnd_map (φ : InvHom K L) {q : ℕ} (hinj : Function.Injective (HRmap φ q))
    (he : IsEnd K q) : IsEnd L q := by
  obtain ⟨z, hz⟩ := he
  refine ⟨Hmap φ q z, ?_⟩
  rw [← HRmap_transfer]
  intro h0
  exact hz (hinj (by rw [h0, map_zero]))

/-- Starts are transported backwards along maps which are surjective on Borel cohomology and
injective on ordinary cohomology... more simply: a start of the target whose class lifts. -/
theorem isStart_of_map (φ : InvHom K L) {q : ℕ} (hsurj : Function.Surjective (HRmap φ q))
    (hs : IsStart L q) : IsStart K q := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨y', rfl⟩ := hsurj y
  refine ⟨y', fun h0 => hy ?_⟩
  rw [← Hmap_forget, h0, map_zero]

end StartEnd

/-! ### Collapse -/

section Collapse

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

open Classical in
/-- The Borel connecting map vanishes if the ordinary one does, the ordinary cohomology of the
quotient complex has dimension at most one in every degree, and forgetting is injective on the
Borel cohomology of the subcomplex one degree above every start of the quotient complex. -/
theorem delta_eq_zero (hfin : ∀ q, FiniteDimensional (ZMod 2) (H K'' q))
    (hdim : ∀ q, finrank (ZMod 2) (H K'' q) ≤ 1)
    (hord : ∀ q (y : HR K'' q), OrdinaryDelta.delta h q (forget K'' q y) = 0)
    (hinj : ∀ q, IsStart K'' q → Function.Injective (forget K' (q + 1))) :
    ∀ q (x : HR K'' q), delta h q x = 0 := by
  let S : Set ℕ := {q | IsStart K'' q}
  let x : (s : ℕ) → HR K'' s := fun s => if hs : IsStart K'' s then Classical.choose hs else 0
  have hx : ∀ s, IsStart K'' s → forget K'' s (x s) ≠ 0 := fun s hs => by
    simp only [x, dif_pos hs]
    exact Classical.choose_spec hs
  have hcase : ∀ q, (q ∈ S ∧ forget K'' q (x q) ≠ 0) ∨
      (∃ t : HR K'' q, t ≠ 0 ∧ w K'' q t = 0) ∨ (∀ z : H K'' q, z = 0) := by
    intro q
    by_cases hz : ∀ z : H K'' q, z = 0
    · exact Or.inr (Or.inr hz)
    push_neg at hz
    obtain ⟨z, hz⟩ := hz
    rcases start_or_end hz with hs | he
    · exact Or.inl ⟨hs, hx q hs⟩
    · exact Or.inr (Or.inl ((isEnd_iff q).mp he))
  have hspan := TowerSpan.eq_tower hfin hdim hcase
  have hstart : ∀ s, s ∈ S → delta h s (x s) = 0 := by
    intro s hs
    apply hinj s hs
    rw [forget_delta, hord, map_zero]
  have hker : ∀ q, TowerSpan.tower K'' S x q ≤ LinearMap.ker (delta h q) := by
    intro q
    induction q with
    | zero =>
      rw [TowerSpan.tower_zero]
      split_ifs with h0
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hstart 0 h0
      · exact bot_le
    | succ q ih =>
      rw [TowerSpan.tower_succ]
      refine sup_le ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        rw [LinearMap.mem_ker, delta_w, LinearMap.mem_ker.mp (ih hy), map_zero]
      · split_ifs with h1
        · rw [Submodule.span_le, Set.singleton_subset_iff]
          exact hstart (q + 1) h1
        · exact bot_le
  intro q y
  exact hker q (hspan q y)

variable {h}

/-- With vanishing connecting map the injection is injective on Borel cohomology. -/
theorem injective_of_delta (hδ : ∀ q (x : HR K'' q), delta h q x = 0) (q : ℕ) :
    Function.Injective (HRmap ι q) := by
  cases q with
  | zero => exact injective_zero h
  | succ q =>
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := exact_sub h q y hy
    exact hδ q x

/-- With vanishing connecting map the projection is surjective on Borel cohomology. -/
theorem surjective_of_delta (hδ : ∀ q (x : HR K'' q), delta h q x = 0) (q : ℕ) :
    Function.Surjective (HRmap π q) := fun x => exact_delta h q x (hδ q x)

/-- With vanishing ordinary connecting map the injection is injective on ordinary cohomology. -/
theorem injective_of_delta_ordinary
    (hδ : ∀ q (x : H K'' q), OrdinaryDelta.delta h q x = 0) (q : ℕ) :
    Function.Injective (Hmap ι q) := by
  cases q with
  | zero => exact OrdinaryExact.sub_injective_zero h
  | succ q =>
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := OrdinaryDelta.exact_sub h q y hy
    exact hδ q x

/-- With vanishing ordinary connecting map the projection is surjective on ordinary
cohomology. -/
theorem surjective_of_delta_ordinary
    (hδ : ∀ q (x : H K'' q), OrdinaryDelta.delta h q x = 0) (q : ℕ) :
    Function.Surjective (Hmap π q) := fun x => OrdinaryDelta.exact_delta h q x (hδ q x)

/-- With vanishing connecting map the dimensions of the Borel cohomology add. -/
theorem finrank_eq_add (hδ : ∀ q (x : HR K'' q), delta h q x = 0) (q : ℕ)
    [FiniteDimensional (ZMod 2) (HR K q)] :
    finrank (ZMod 2) (HR K q) = finrank (ZMod 2) (HR K' q) + finrank (ZMod 2) (HR K'' q) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (HRmap π q)
  rw [LinearMap.range_eq_top.mpr (surjective_of_delta hδ q), finrank_top] at h1
  have h2 : LinearMap.ker (HRmap π q) = LinearMap.range (HRmap ι q) := by
    ext y
    constructor
    · intro hy
      exact exact_mid h q y hy
    · rintro ⟨z, rfl⟩
      exact comp_zero h q z
  rw [h2, LinearMap.finrank_range_of_inj (injective_of_delta hδ q)] at h1
  omega

/-- With vanishing ordinary connecting map the dimensions of the ordinary cohomology add. -/
theorem finrank_eq_add_ordinary (hδ : ∀ q (x : H K'' q), OrdinaryDelta.delta h q x = 0)
    (q : ℕ) [FiniteDimensional (ZMod 2) (H K q)] :
    finrank (ZMod 2) (H K q) = finrank (ZMod 2) (H K' q) + finrank (ZMod 2) (H K'' q) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Hmap π q)
  rw [LinearMap.range_eq_top.mpr (surjective_of_delta_ordinary hδ q), finrank_top] at h1
  have h2 : LinearMap.ker (Hmap π q) = LinearMap.range (Hmap ι q) := by
    ext y
    constructor
    · intro hy
      exact exact_mid_ordinary h q y hy
    · rintro ⟨z, rfl⟩
      exact comp_zero_ordinary h q z
  rw [h2, LinearMap.finrank_range_of_inj (injective_of_delta_ordinary hδ q)] at h1
  omega

end Collapse

end

end Finsler.CrossingCollapse
