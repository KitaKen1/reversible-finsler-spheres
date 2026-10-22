module

public import Finsler.Topology.BorelCochain
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective

/-! The long exact sequence of Borel cohomology for a degreewise short exact sequence
0 → K' → K → K'' → 0 of involutive F₂-cochain complexes. Exactness at the middle term uses only
componentwise lifts. The connecting map HR K'' n → HR K' (n + 1) is defined with componentwise
linear sections; its value is computed from any supported lift, which gives exactness at the two
other places, naturality and compatibility with w. The same middle exactness is proved for
ordinary cohomology. No topological pair is constructed in this file. -/

@[expose] public section

namespace Finsler.BorelExact

open Finsler.BorelCochain

noncomputable section

variable {K' K K'' : InvComplex} (ι : InvHom K' K) (π : InvHom K K'')

/-- Degreewise short exactness of two composable equivariant cochain maps. -/
structure ShortExact : Prop where
  inj : ∀ j, Function.Injective (ι.f j)
  surj : ∀ j, Function.Surjective (π.f j)
  zero : ∀ j z, π.f j (ι.f j z) = 0
  exact : ∀ j x, π.f j x = 0 → ∃ z, ι.f j z = x

variable {ι π} (h : ShortExact ι π)

include h in
theorem seqMap_injective : Function.Injective (seqMap ι) := by
  intro x y hxy
  funext j
  exact h.inj j (congrFun hxy j)

include h in
theorem seqMap_comp_zero (z : Seq K') : seqMap π (seqMap ι z) = 0 := by
  funext j
  exact h.zero j (z j)

include h in
/-- A supported sequence killed by π comes from a sequence with the same support. -/
theorem exists_seq_lift {k : ℕ} {c : Seq K} (hc : c ∈ low K k) (hπ : seqMap π c = 0) :
    ∃ z, z ∈ low K' k ∧ seqMap ι z = c := by
  have hz : ∀ j, ∃ z, ι.f j z = c j := fun j => h.exact j (c j) (congrFun hπ j)
  choose z hzc using hz
  refine ⟨z, ?_, funext hzc⟩
  intro j hj
  apply h.inj j
  rw [hzc, hc j hj, map_zero]

include h in
/-- A supported sequence of the quotient complex has a preimage with the same support. -/
theorem exists_seq_preimage {k : ℕ} {c : Seq K''} (hc : c ∈ low K'' k) :
    ∃ b, b ∈ low K k ∧ seqMap π b = c := by
  classical
  have hb : ∀ j, ∃ b, π.f j b = c j := fun j => h.surj j (c j)
  choose b hbc using hb
  refine ⟨fun j => if j < k then b j else 0, ?_, ?_⟩
  · intro j hj
    exact ite_eq_right (Nat.not_lt.mpr hj)
  · funext j
    rw [seqMap_apply]
    by_cases hj : j < k
    · rw [ite_eq_left hj, hbc]
    · rw [ite_eq_right hj, map_zero, hc j (Nat.le_of_not_gt hj)]

include h in
/-- A sequence over K' whose image is a supported Borel cocycle is a supported Borel cocycle. -/
theorem mem_bcocycles_of_map {n : ℕ} {z : Seq K'} (hz : seqMap ι z ∈ bcocycles K n) :
    z ∈ bcocycles K' n := by
  obtain ⟨hlow, hD⟩ := (mem_bcocycles K).mp hz
  refine ⟨?_, ?_⟩
  · intro j hj
    apply h.inj j
    rw [map_zero]
    exact hlow j hj
  · apply seqMap_injective h
    rw [seqMap_D, map_zero]
    exact hD

include h in
theorem comp_zero (n : ℕ) (z : HR K' n) : HRmap π n (HRmap ι n z) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (bcocycleMap π n (bcocycleMap ι n c)) : HR K'' n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change seqMap π (seqMap ι (c : Seq K')) ∈ bcoboundaries K'' n
  rw [seqMap_comp_zero h]
  exact Submodule.zero_mem _

include h in
/-- Exactness of Borel cohomology at the middle term. -/
theorem exact_mid (n : ℕ) (x : HR K n) (hx : HRmap π n x = 0) :
    ∃ z : HR K' n, HRmap ι n z = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [HRmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨b'', hb'', hD⟩ := hx
  have hD' : D K'' b'' = seqMap π (c : Seq K) := hD
  obtain ⟨b, hb, hπb⟩ := exists_seq_preimage h hb''
  obtain ⟨hclow, hcD⟩ := (mem_bcocycles K).mp c.2
  have hlow : (c : Seq K) - D K b ∈ low K (n + 1) :=
    Submodule.sub_mem _ hclow (D_mem_low K hb)
  have hπ : seqMap π ((c : Seq K) - D K b) = 0 := by
    rw [map_sub, seqMap_D, hπb, hD', sub_self]
  obtain ⟨z, hz, hιz⟩ := exists_seq_lift h hlow hπ
  have hzc : z ∈ bcocycles K' n := by
    apply mem_bcocycles_of_map h
    rw [hιz]
    refine ⟨hlow, ?_⟩
    change D K ((c : Seq K) - D K b) = 0
    rw [map_sub, hcD, D_D, sub_zero]
  refine ⟨Submodule.Quotient.mk ⟨z, hzc⟩, ?_⟩
  rw [HRmap, Submodule.mapQ_apply, Submodule.Quotient.eq]
  change seqMap ι z - (c : Seq K) ∈ bcoboundaries K n
  refine ⟨-b, Submodule.neg_mem _ hb, ?_⟩
  rw [map_neg, hιz]
  abel

include h in
theorem comp_zero_ordinary (n : ℕ) (z : H K' n) : Hmap π n (Hmap ι n z) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change (Submodule.Quotient.mk (cocycleMap π n (cocycleMap ι n c)) : H K'' n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change π.f n (ι.f n (c : K'.C n)) ∈ coboundaries K'' n
  rw [h.zero]
  exact Submodule.zero_mem _

include h in
/-- Exactness of ordinary cohomology at the middle term. -/
theorem exact_mid_ordinary (n : ℕ) (x : H K n) (hx : Hmap π n x = 0) :
    ∃ z : H K' n, Hmap ι n z = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Hmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  have hx' : π.f n (c : K.C n) ∈ coboundaries K'' n := hx
  have hc : K.d n (c : K.C n) = 0 := c.2
  cases n with
  | zero =>
    have h0 : π.f 0 (c : K.C 0) = 0 := (Submodule.mem_bot (ZMod 2)).mp hx'
    obtain ⟨z, hz⟩ := h.exact 0 _ h0
    have hzd : K'.d 0 z = 0 := by
      apply h.inj 1
      rw [ι.comm_d, hz, hc, map_zero]
    refine ⟨Submodule.Quotient.mk ⟨z, hzd⟩, ?_⟩
    rw [Hmap, Submodule.mapQ_apply]
    congr 1
    exact Subtype.ext hz
  | succ m =>
    obtain ⟨b'', hb''⟩ := hx'
    obtain ⟨b, hb⟩ := h.surj m b''
    have hπ : π.f (m + 1) ((c : K.C (m + 1)) - K.d m b) = 0 := by
      rw [map_sub, π.comm_d, hb, hb'', sub_self]
    obtain ⟨z, hz⟩ := h.exact (m + 1) _ hπ
    have hzd : K'.d (m + 1) z = 0 := by
      apply h.inj (m + 1 + 1)
      rw [ι.comm_d, hz, map_sub, hc, K.dd, sub_zero, map_zero]
    refine ⟨Submodule.Quotient.mk ⟨z, hzd⟩, ?_⟩
    rw [Hmap, Submodule.mapQ_apply, Submodule.Quotient.eq]
    change ι.f (m + 1) z - (c : K.C (m + 1)) ∈ coboundaries K (m + 1)
    refine ⟨-b, ?_⟩
    rw [map_neg, hz]
    abel

/-- A linear section of the surjection in each degree. -/
def sec (j : ℕ) : K''.C j →ₗ[ZMod 2] K.C j :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (π.f j)
    (LinearMap.range_eq_top.mpr (h.surj j)))

theorem proj_sec (j : ℕ) (x : K''.C j) : π.f j (sec h j x) = x :=
  congrArg (fun g => g x) (Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective
    (π.f j) (LinearMap.range_eq_top.mpr (h.surj j))))

/-- A linear retraction of the injection in each degree. -/
def ret (j : ℕ) : K.C j →ₗ[ZMod 2] K'.C j :=
  Classical.choose (LinearMap.exists_leftInverse_of_injective (ι.f j)
    (LinearMap.ker_eq_bot.mpr (h.inj j)))

theorem ret_incl (j : ℕ) (z : K'.C j) : ret h j (ι.f j z) = z :=
  congrArg (fun g => g z) (Classical.choose_spec (LinearMap.exists_leftInverse_of_injective
    (ι.f j) (LinearMap.ker_eq_bot.mpr (h.inj j))))

def secSeq : Seq K'' →ₗ[ZMod 2] Seq K := LinearMap.pi fun j => sec h j ∘ₗ LinearMap.proj j

def retSeq : Seq K →ₗ[ZMod 2] Seq K' := LinearMap.pi fun j => ret h j ∘ₗ LinearMap.proj j

theorem proj_secSeq (c : Seq K'') : seqMap π (secSeq h c) = c := by
  funext j
  exact proj_sec h j (c j)

theorem retSeq_incl (z : Seq K') : retSeq h (seqMap ι z) = z := by
  funext j
  exact ret_incl h j (z j)

theorem secSeq_low {k : ℕ} {c : Seq K''} (hc : c ∈ low K'' k) : secSeq h c ∈ low K k := by
  intro j hj
  change sec h j (c j) = 0
  rw [hc j hj, map_zero]

/-- The cocycle-level connecting map: lift, apply the Borel differential, retract. -/
def deltaSeq : Seq K'' →ₗ[ZMod 2] Seq K' := retSeq h ∘ₗ D K ∘ₗ secSeq h

/-- The connecting value does not depend on the supported lift, up to a Borel coboundary. -/
theorem deltaSeq_sub_mem (n : ℕ) (c : Seq K'') (b : Seq K) (hb : b ∈ low K (n + 1))
    (hc : c ∈ low K'' (n + 1)) (hπ : seqMap π b = c) (z : Seq K') (hz : seqMap ι z = D K b) :
    deltaSeq h c - z ∈ bcoboundaries K' (n + 1) := by
  have hlow : secSeq h c - b ∈ low K (n + 1) := Submodule.sub_mem _ (secSeq_low h hc) hb
  have hzero : seqMap π (secSeq h c - b) = 0 := by
    rw [map_sub, proj_secSeq, hπ, sub_self]
  obtain ⟨u, hu, hιu⟩ := exists_seq_lift h hlow hzero
  refine ⟨u, hu, ?_⟩
  have he : D K (secSeq h c) = seqMap ι (D K' u + z) := by
    rw [map_add, seqMap_D, hιu, hz, map_sub, sub_add_cancel]
  change D K' u = retSeq h (D K (secSeq h c)) - z
  rw [he, retSeq_incl, add_sub_cancel_right]

include h in
theorem exists_delta_lift (n : ℕ) (c : bcocycles K'' n) :
    ∃ b z, b ∈ low K (n + 1) ∧ seqMap π b = (c : Seq K'') ∧ z ∈ bcocycles K' (n + 1) ∧
      seqMap ι z = D K b := by
  obtain ⟨hclow, hcD⟩ := (mem_bcocycles K'').mp c.2
  obtain ⟨b, hb, hπb⟩ := exists_seq_preimage h hclow
  have hπ : seqMap π (D K b) = 0 := by
    rw [seqMap_D, hπb]
    exact hcD
  obtain ⟨z, _, hιz⟩ := exists_seq_lift h (D_mem_low K hb) hπ
  refine ⟨b, z, hb, hπb, ?_, hιz⟩
  apply mem_bcocycles_of_map h
  rw [hιz]
  exact ⟨D_mem_low K hb, D_D K b⟩

theorem deltaSeq_mem (n : ℕ) (c : bcocycles K'' n) :
    deltaSeq h (c : Seq K'') ∈ bcocycles K' (n + 1) := by
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  have hd := deltaSeq_sub_mem h n (c : Seq K'') b hb ((mem_bcocycles K'').mp c.2).1 hπb z hιz
  have he : deltaSeq h (c : Seq K'') = (deltaSeq h (c : Seq K'') - z) + z := by abel
  rw [he]
  exact Submodule.add_mem _ (bcoboundaries_le K' (n + 1) hd) hz

/-- The connecting map on Borel cocycles. -/
def deltaCocycle (n : ℕ) : bcocycles K'' n →ₗ[ZMod 2] bcocycles K' (n + 1) :=
  LinearMap.codRestrict (bcocycles K' (n + 1)) (deltaSeq h ∘ₗ (bcocycles K'' n).subtype)
    (deltaSeq_mem h n)

theorem deltaCocycle_coboundary (n : ℕ) :
    (bcoboundaries K'' n).comap (bcocycles K'' n).subtype ≤
      ((bcoboundaries K' (n + 1)).comap (bcocycles K' (n + 1)).subtype).comap
        (deltaCocycle h n) := by
  rintro c ⟨b'', hb'', hD⟩
  have hD' : D K'' b'' = (c : Seq K'') := hD
  obtain ⟨b, hb, hπb⟩ := exists_seq_preimage h hb''
  have hd := deltaSeq_sub_mem h n (c : Seq K'') (D K b) (D_mem_low K hb)
    ((mem_bcocycles K'').mp c.2).1 (by rw [seqMap_D, hπb, hD']) 0
    (by rw [map_zero, D_D])
  rw [sub_zero] at hd
  exact hd

/-- The connecting map of the Borel long exact sequence. -/
def delta (n : ℕ) : HR K'' n →ₗ[ZMod 2] HR K' (n + 1) :=
  Submodule.mapQ _ _ (deltaCocycle h n) (deltaCocycle_coboundary h n)

/-- The connecting class is represented by the differential of any supported lift. -/
theorem delta_mk (n : ℕ) (c : bcocycles K'' n) (b : Seq K) (hb : b ∈ low K (n + 1))
    (hπ : seqMap π b = (c : Seq K'')) (z : bcocycles K' (n + 1))
    (hz : seqMap ι (z : Seq K') = D K b) :
    delta h n (Submodule.Quotient.mk c) = Submodule.Quotient.mk z := by
  rw [delta, Submodule.mapQ_apply, Submodule.Quotient.eq]
  exact deltaSeq_sub_mem h n (c : Seq K'') b hb ((mem_bcocycles K'').mp c.2).1 hπ z hz

/-- The connecting map vanishes on the image of the surjection. -/
theorem delta_comp_zero (n : ℕ) (x : HR K n) : delta h n (HRmap π n x) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [HRmap, Submodule.mapQ_apply]
  have hz : (0 : Seq K') ∈ bcocycles K' (n + 1) := Submodule.zero_mem _
  rw [delta_mk h n (bcocycleMap π n c) (c : Seq K) ((mem_bcocycles K).mp c.2).1 rfl ⟨0, hz⟩
    (by rw [map_zero, ((mem_bcocycles K).mp c.2).2])]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.zero_mem _)

/-- Exactness at the quotient term: the kernel of the connecting map is the image of π. -/
theorem exact_delta (n : ℕ) (x : HR K'' n) (hx : delta h n x = 0) :
    ∃ y : HR K n, HRmap π n y = x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  rw [delta_mk h n c b hb hπb ⟨z, hz⟩ hιz, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨u, hu, hDu⟩ := hx
  have hDu' : D K' u = z := hDu
  have hy : b - seqMap ι u ∈ bcocycles K n := by
    refine ⟨Submodule.sub_mem _ hb (seqMap_low ι hu), ?_⟩
    change D K (b - seqMap ι u) = 0
    rw [map_sub, ← seqMap_D, hDu', hιz, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨b - seqMap ι u, hy⟩, ?_⟩
  rw [HRmap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change seqMap π (b - seqMap ι u) = (c : Seq K'')
  rw [map_sub, seqMap_comp_zero h, sub_zero, hπb]

/-- The composite of the connecting map with the injection vanishes. -/
theorem comp_delta_zero (n : ℕ) (x : HR K'' n) : HRmap ι (n + 1) (delta h n x) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  rw [delta_mk h n c b hb hπb ⟨z, hz⟩ hιz, HRmap, Submodule.mapQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact ⟨b, hb, hιz.symm⟩

/-- Exactness at the sub term: the kernel of ι in positive degree is the image of the
connecting map. -/
theorem exact_sub (n : ℕ) (y : HR K' (n + 1)) (hy : HRmap ι (n + 1) y = 0) :
    ∃ x : HR K'' n, delta h n x = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [HRmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨b, hb, hDb⟩ := hy
  have hDb' : D K b = seqMap ι (z : Seq K') := hDb
  have hc : seqMap π b ∈ bcocycles K'' n := by
    refine ⟨seqMap_low π hb, ?_⟩
    change D K'' (seqMap π b) = 0
    rw [← seqMap_D, hDb', seqMap_comp_zero h]
  exact ⟨Submodule.Quotient.mk ⟨seqMap π b, hc⟩, delta_mk h n ⟨seqMap π b, hc⟩ b hb rfl z hDb'.symm⟩

include h in
/-- The injection is injective on Borel cohomology of degree zero. -/
theorem injective_zero : Function.Injective (HRmap ι 0) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [HRmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨b, hb, hDb⟩ := hy
  have hDb' : D K b = seqMap ι (z : Seq K') := hDb
  have hz0 : (z : Seq K') = 0 := by
    apply seqMap_injective h
    rw [← hDb', mem_low_zero K hb, map_zero, map_zero]
  have hz : z = 0 := Subtype.ext hz0
  rw [hz, Submodule.Quotient.mk_zero]

/-- The connecting map commutes with w. -/
theorem delta_w (n : ℕ) (x : HR K'' n) :
    delta h (n + 1) (w K'' n x) = w K' (n + 1) (delta h n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  rw [delta_mk h n c b hb hπb ⟨z, hz⟩ hιz]
  exact delta_mk h (n + 1) (Submodule.inclusion (bcocycles_mono K'' n) c) b
    (low_mono K (Nat.le_succ _) hb) hπb
    (Submodule.inclusion (bcocycles_mono K' (n + 1)) ⟨z, hz⟩) hιz

section Naturality

variable {L' L L'' : InvComplex} {κ : InvHom L' L} {ρ : InvHom L L''} (g : ShortExact κ ρ)
  (φ' : InvHom K' L') (φ : InvHom K L) (φ'' : InvHom K'' L'')

/-- Naturality of the connecting map for a commuting map of short exact sequences. -/
theorem delta_natural (hl : ∀ j z, φ.f j (ι.f j z) = κ.f j (φ'.f j z))
    (hr : ∀ j x, φ''.f j (π.f j x) = ρ.f j (φ.f j x)) (n : ℕ) (x : HR K'' n) :
    delta g n (HRmap φ'' n x) = HRmap φ' (n + 1) (delta h n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  rw [delta_mk h n c b hb hπb ⟨z, hz⟩ hιz]
  refine delta_mk g n (bcocycleMap φ'' n c) (seqMap φ b) (seqMap_low φ hb) ?_
    (bcocycleMap φ' (n + 1) ⟨z, hz⟩) ?_
  · change seqMap ρ (seqMap φ b) = seqMap φ'' (c : Seq K'')
    rw [← hπb]
    funext j
    exact (hr j (b j)).symm
  · change seqMap κ (seqMap φ' z) = D L (seqMap φ b)
    rw [← seqMap_D, ← hιz]
    funext j
    exact (hl j (z j)).symm

end Naturality

end

end Finsler.BorelExact
