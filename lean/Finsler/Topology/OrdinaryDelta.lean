module

public import Finsler.Topology.OrdinaryExact
public import Finsler.Topology.TameHomology

/-! The connecting map of ordinary cohomology for a degreewise short exact sequence
0 → K' → K → K'' → 0 of F₂-cochain complexes: lift a cocycle of K'', apply the differential and
retract to K'. It is well defined on cohomology; a class of K'' with zero connecting image comes
from K, and a class of K' of positive degree which becomes zero in K is a connecting image.
Consequences: the cohomology of K' in degree n + 1 is finite dimensional if that of K'' in
degree n and of K in degree n + 1 are, and the dimension of the cohomology of K'' in degree n is
at most the dimension of the image of the cohomology of K plus the dimension of the cohomology
of K' in degree n + 1. -/

@[expose] public section

namespace Finsler.OrdinaryDelta

open Module Finsler.BorelCochain Finsler.BorelExact

noncomputable section

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

/-- The differential of the lift of a cocycle lies in the subcomplex. -/
theorem incl_ret_d_sec (n : ℕ) (c : K''.C n) (hc : K''.d n c = 0) :
    ι.f (n + 1) (ret h (n + 1) (K.d n (sec h n c))) = K.d n (sec h n c) := by
  have hπ : π.f (n + 1) (K.d n (sec h n c)) = 0 := by rw [π.comm_d, proj_sec, hc]
  obtain ⟨z, hz⟩ := h.exact (n + 1) _ hπ
  rw [← hz, ret_incl]

/-- The differential of the chosen lift and of any other lift differ by the image of a
coboundary of the subcomplex. -/
theorem d_sec_eq (n : ℕ) (c : K''.C n) (b : K.C n) (hb : π.f n b = c) :
    ∃ v : K'.C n, K.d n (sec h n c) = K.d n b + ι.f (n + 1) (K'.d n v) := by
  have hπ : π.f n (sec h n c - b) = 0 := by rw [map_sub, proj_sec, hb, sub_self]
  obtain ⟨v, hv⟩ := h.exact n _ hπ
  refine ⟨v, ?_⟩
  rw [ι.comm_d, hv, map_sub]
  abel

/-- The connecting map on cocycles. -/
def deltaCocycle (n : ℕ) : cocycles K'' n →ₗ[ZMod 2] cocycles K' (n + 1) :=
  LinearMap.codRestrict (cocycles K' (n + 1))
    (ret h (n + 1) ∘ₗ K.d n ∘ₗ sec h n ∘ₗ (cocycles K'' n).subtype) fun c => by
    change K'.d (n + 1) (ret h (n + 1) (K.d n (sec h n (c : K''.C n)))) = 0
    apply h.inj (n + 1 + 1)
    rw [ι.comm_d, incl_ret_d_sec h n _ c.2, K.dd, map_zero]

theorem deltaCocycle_coboundary (n : ℕ) :
    (coboundaries K'' n).comap (cocycles K'' n).subtype ≤
      ((coboundaries K' (n + 1)).comap (cocycles K' (n + 1)).subtype).comap
        (deltaCocycle h n) := by
  intro c hc
  change ret h (n + 1) (K.d n (sec h n (c : K''.C n))) ∈ coboundaries K' (n + 1)
  have hc' : (c : K''.C n) ∈ coboundaries K'' n := hc
  cases n with
  | zero =>
    have h0 : (c : K''.C 0) = 0 := (Submodule.mem_bot (ZMod 2)).mp hc'
    rw [h0, map_zero, map_zero, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨u'', hu''⟩ := hc'
    obtain ⟨u, hu⟩ := h.surj m u''
    have hb : π.f (m + 1) (K.d m u) = (c : K''.C (m + 1)) := by rw [π.comm_d, hu, hu'']
    obtain ⟨v, hv⟩ := d_sec_eq h (m + 1) _ _ hb
    rw [hv, K.dd, zero_add, ret_incl]
    exact ⟨v, rfl⟩

/-- The connecting map of ordinary cohomology. -/
def delta (n : ℕ) : H K'' n →ₗ[ZMod 2] H K' (n + 1) :=
  Submodule.mapQ _ _ (deltaCocycle h n) (deltaCocycle_coboundary h n)

/-- Exactness at the cohomology of K'': a class with zero connecting image comes from K. -/
theorem exact_delta (n : ℕ) (y : H K'' n) (hy : delta h n y = 0) :
    ∃ x : H K n, Hmap π n x = y := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [delta, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  have hy' : ret h (n + 1) (K.d n (sec h n (c : K''.C n))) ∈ coboundaries K' (n + 1) := hy
  obtain ⟨u, hu⟩ := hy'
  have hc : K''.d n (c : K''.C n) = 0 := c.2
  have hcoc : K.d n (sec h n (c : K''.C n) - ι.f n u) = 0 := by
    rw [map_sub, ← ι.comm_d, hu, incl_ret_d_sec h n _ hc, sub_self]
  refine ⟨Submodule.Quotient.mk ⟨sec h n (c : K''.C n) - ι.f n u, hcoc⟩, ?_⟩
  rw [Hmap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change π.f n (sec h n (c : K''.C n) - ι.f n u) = (c : K''.C n)
  rw [map_sub, proj_sec, h.zero, sub_zero]

/-- Exactness at the cohomology of K' in positive degrees: a class which becomes zero in K is a
connecting image. -/
theorem exact_sub (n : ℕ) (z : H K' (n + 1)) (hz : Hmap ι (n + 1) z = 0) :
    ∃ y : H K'' n, delta h n y = z := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [Hmap, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  have hz' : ι.f (n + 1) (c : K'.C (n + 1)) ∈ coboundaries K (n + 1) := hz
  obtain ⟨b, hb⟩ := hz'
  have hπb : K''.d n (π.f n b) = 0 := by rw [← π.comm_d, hb, h.zero]
  refine ⟨Submodule.Quotient.mk ⟨π.f n b, hπb⟩, ?_⟩
  rw [delta, Submodule.mapQ_apply, Submodule.Quotient.eq]
  change ret h (n + 1) (K.d n (sec h n (π.f n b))) - (c : K'.C (n + 1)) ∈
    coboundaries K' (n + 1)
  obtain ⟨v, hv⟩ := d_sec_eq h n (π.f n b) b rfl
  rw [hv, hb, ← map_add, ret_incl, add_sub_cancel_left]
  exact ⟨v, rfl⟩

include h in
/-- The cohomology of the subcomplex in degree n + 1 is finite dimensional if that of the
quotient complex in degree n and of the middle complex in degree n + 1 are. -/
theorem finite_sub (n : ℕ) [Module.Finite (ZMod 2) (H K'' n)]
    [Module.Finite (ZMod 2) (H K (n + 1))] : Module.Finite (ZMod 2) (H K' (n + 1)) :=
  TameHomology.finite_of_exact_linear (delta h n) (Hmap ι (n + 1))
    fun z hz => exact_sub h n z hz

include h in
/-- The dimension of the cohomology of the quotient complex is at most the dimension of the
image of the cohomology of the middle complex plus the dimension of the cohomology of the
subcomplex in the next degree. -/
theorem finrank_le_range_add (n : ℕ) [Module.Finite (ZMod 2) (H K'' n)]
    [Module.Finite (ZMod 2) (H K' (n + 1))] :
    finrank (ZMod 2) (H K'' n) ≤
      finrank (ZMod 2) (LinearMap.range (Hmap π n)) + finrank (ZMod 2) (H K' (n + 1)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (delta h n)
  have h2 : LinearMap.ker (delta h n) ≤ LinearMap.range (Hmap π n) := fun y hy =>
    exact_delta h n y (LinearMap.mem_ker.mp hy)
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_le (LinearMap.range (delta h n))
  omega

end

end Finsler.OrdinaryDelta
