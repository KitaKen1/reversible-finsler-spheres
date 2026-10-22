module

public import Finsler.Topology.BorelExact

/-! Vanishing of the ordinary cohomology of the subcomplex in a degreewise short exact sequence
0 → K' → K → K'' → 0 of F₂-cochain complexes. If the map H K n → H K'' n is surjective and the
map H K (n + 1) → H K'' (n + 1) is injective, then H K' (n + 1) = 0; in degree zero injectivity
of H K 0 → H K'' 0 suffices. The proof is the cochain-level chase; no connecting map of ordinary
cohomology is constructed. -/

@[expose] public section

namespace Finsler.OrdinaryExact

open Finsler.BorelCochain Finsler.BorelExact

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

include h

/-- The map from the ordinary cohomology of the subcomplex is injective in degree zero. -/
theorem sub_injective_zero : Function.Injective (Hmap ι 0) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Hmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  have hz' : ι.f 0 (c : K'.C 0) ∈ coboundaries K 0 := hz
  have h0 : ι.f 0 (c : K'.C 0) = 0 := (Submodule.mem_bot (ZMod 2)).mp hz'
  have hc : (c : K'.C 0) = 0 := h.inj 0 (h0.trans (map_zero (ι.f 0)).symm)
  rw [Submodule.Quotient.mk_eq_zero]
  change (c : K'.C 0) ∈ coboundaries K' 0
  rw [hc]
  exact Submodule.zero_mem _

/-- If the restriction is injective in degree zero, the ordinary cohomology of the subcomplex
vanishes in degree zero. -/
theorem sub_eq_zero_zero (hinj : Function.Injective (Hmap π 0)) (z : H K' 0) : z = 0 := by
  apply sub_injective_zero h
  apply hinj
  rw [comp_zero_ordinary h, map_zero, map_zero]

/-- If the restriction is surjective in degree n and injective in degree n + 1, the ordinary
cohomology of the subcomplex vanishes in degree n + 1. -/
theorem sub_eq_zero_succ (n : ℕ) (hsurj : Function.Surjective (Hmap π n))
    (hinj : Function.Injective (Hmap π (n + 1))) (z : H K' (n + 1)) : z = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hc : K'.d (n + 1) (c : K'.C (n + 1)) = 0 := c.2
  -- the image in the middle complex is a coboundary
  have h1 : Hmap ι (n + 1) (Submodule.Quotient.mk c) = 0 := by
    apply hinj
    rw [comp_zero_ordinary h, map_zero]
  rw [Hmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at h1
  have h1' : ι.f (n + 1) (c : K'.C (n + 1)) ∈ coboundaries K (n + 1) := h1
  obtain ⟨b, hb⟩ := h1'
  -- the restriction of the primitive is a cocycle, hence the restriction of a cocycle
  have hπb : K''.d n (π.f n b) = 0 := by
    rw [← π.comm_d, hb, h.zero]
  obtain ⟨y, hy⟩ := hsurj (Submodule.Quotient.mk ⟨π.f n b, hπb⟩)
  obtain ⟨e, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have he : K.d n (e : K.C n) = 0 := e.2
  rw [Hmap, Submodule.mapQ_apply, Submodule.Quotient.eq] at hy
  have hy' : π.f n (e : K.C n) - π.f n b ∈ coboundaries K'' n := hy
  rw [Submodule.Quotient.mk_eq_zero]
  change (c : K'.C (n + 1)) ∈ coboundaries K' (n + 1)
  cases n with
  | zero =>
    have h0 : π.f 0 (e : K.C 0) - π.f 0 b = 0 := (Submodule.mem_bot (ZMod 2)).mp hy'
    have hπ : π.f 0 (b - (e : K.C 0)) = 0 := by
      rw [map_sub, ← neg_sub, h0, neg_zero]
    obtain ⟨z', hz'⟩ := h.exact 0 _ hπ
    refine ⟨z', h.inj 1 ?_⟩
    rw [ι.comm_d, hz', map_sub, hb, he, sub_zero]
  | succ m =>
    obtain ⟨u'', hu''⟩ := hy'
    obtain ⟨u, hu⟩ := h.surj m u''
    have hπ : π.f (m + 1) (b - (e : K.C (m + 1)) + K.d m u) = 0 := by
      rw [map_add, map_sub, π.comm_d, hu, hu'']
      abel
    obtain ⟨z', hz'⟩ := h.exact (m + 1) _ hπ
    refine ⟨z', h.inj (m + 1 + 1) ?_⟩
    rw [ι.comm_d, hz', map_add, map_sub, hb, he, K.dd, sub_zero, add_zero]

end Finsler.OrdinaryExact
