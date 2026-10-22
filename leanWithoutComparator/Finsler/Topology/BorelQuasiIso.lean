module

public import Finsler.Topology.BorelIterate
public import Finsler.Topology.BorelExact

/-! Comparison of Borel cohomology through ordinary cohomology. An equivariant cochain map which
is an isomorphism on ordinary cohomology in every degree is an isomorphism on Borel cohomology in
every degree: injectivity and surjectivity are proved by induction on the degree with the two
four-lemmas in the Gysin sequence, starting from the injectivity of forgetting in degree zero.
The same holds for the iterated Borel cohomology of two commuting involutions, and a degreewise
short exact sequence of complexes with commuting involutions induces a degreewise short exact
sequence of the iterated Borel complexes, hence the long exact sequence of the iterated Borel
cohomology. No topological statement is made in this file. -/

@[expose] public section

namespace Finsler.BorelQuasiIso

open Finsler.BorelCochain Finsler.BorelIterate

noncomputable section

/-- Forgetting the action is injective on Borel cohomology of degree zero. -/
theorem forget_zero_injective (K : InvComplex) : Function.Injective (forget K 0) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [forget, Submodule.mapQ_apply, mk_eq_zero_iff_coboundary] at hx
  have h0 : (c : Seq K) 0 = 0 := (Submodule.mem_bot (ZMod 2)).mp hx
  have hc : c = 0 := by
    apply Subtype.ext
    funext j
    cases j with
    | zero => exact h0
    | succ i => exact ((mem_bcocycles K).mp c.2).1 (i + 1) (by omega)
  rw [hc, Submodule.Quotient.mk_zero]

variable {K L : InvComplex} (φ : InvHom K L)

/-- An ordinary cohomology isomorphism is injective on Borel cohomology. -/
theorem injective_of_ordinary (hinj : ∀ n, Function.Injective (Hmap φ n))
    (hsurj : ∀ n, Function.Surjective (Hmap φ n)) : ∀ n, Function.Injective (HRmap φ n) := by
  intro n
  induction n with
  | zero =>
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply forget_zero_injective K
    apply hinj 0
    rw [Hmap_forget, hx]
    simp only [map_zero]
  | succ n ih =>
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hf : forget K (n + 1) x = 0 := by
      apply hinj (n + 1)
      rw [Hmap_forget, hx]
      simp only [map_zero]
    obtain ⟨y, rfl⟩ := (exact_forget K n x).mp hf
    rw [HRmap_w] at hx
    obtain ⟨z', hz'⟩ := (exact_w L n _).mp hx
    obtain ⟨z, rfl⟩ := hsurj n z'
    rw [← HRmap_transfer] at hz'
    have hy : transfer K n z = y := ih hz'
    rw [← hy]
    exact (exact_w K n _).mpr ⟨z, rfl⟩

/-- An ordinary cohomology isomorphism is surjective on Borel cohomology. -/
theorem surjective_of_ordinary (hinj : ∀ n, Function.Injective (Hmap φ n))
    (hsurj : ∀ n, Function.Surjective (Hmap φ n)) : ∀ n, Function.Surjective (HRmap φ n) := by
  have hI := injective_of_ordinary φ hinj hsurj
  intro n
  induction n with
  | zero =>
    intro y'
    obtain ⟨z, hz⟩ := hsurj 0 (forget L 0 y')
    have ht : transfer K 0 z = 0 := by
      apply hI 0
      rw [HRmap_transfer, hz, map_zero]
      exact (exact_transfer L 0 _).mpr ⟨y', rfl⟩
    obtain ⟨y, rfl⟩ := (exact_transfer K 0 z).mp ht
    refine ⟨y, ?_⟩
    apply forget_zero_injective L
    rw [← Hmap_forget, hz]
  | succ n ih =>
    intro y'
    obtain ⟨z, hz⟩ := hsurj (n + 1) (forget L (n + 1) y')
    have ht : transfer K (n + 1) z = 0 := by
      apply hI (n + 1)
      rw [HRmap_transfer, hz, map_zero]
      exact (exact_transfer L (n + 1) _).mpr ⟨y', rfl⟩
    obtain ⟨y, rfl⟩ := (exact_transfer K (n + 1) z).mp ht
    have hf : forget L (n + 1) (HRmap φ (n + 1) y - y') = 0 := by
      rw [map_sub, ← Hmap_forget, hz, sub_self]
    obtain ⟨u', hu'⟩ := (exact_forget L n _).mp hf
    obtain ⟨u, rfl⟩ := ih u'
    refine ⟨y - w K n u, ?_⟩
    rw [map_sub, HRmap_w, hu']
    abel

/-- An equivariant cochain map which is an isomorphism on ordinary cohomology in every degree is
an isomorphism on Borel cohomology in every degree. -/
theorem bijective_of_ordinary (h : ∀ n, Function.Bijective (Hmap φ n)) :
    ∀ n, Function.Bijective (HRmap φ n) := fun n =>
  ⟨injective_of_ordinary φ (fun k => (h k).1) (fun k => (h k).2) n,
    surjective_of_ordinary φ (fun k => (h k).1) (fun k => (h k).2) n⟩

section Iterated

variable {SK : Commuting K} {SL : Commuting L} (Φ : CommHom SK SL)

/-- The ordinary cohomology map of the iterated Borel complexes is the Borel cohomology map. -/
theorem Hmap_borelHom (n : ℕ) (z : H (borelInv SK) n) :
    Hmap (borelHom Φ) n z =
      (cohomologyEquiv SL n).symm (HRmap Φ.φ n (cohomologyEquiv SK n z)) :=
  (LinearEquiv.eq_symm_apply _).mpr (cohomologyEquiv_natural Φ n z)

/-- An ordinary cohomology isomorphism commuting with two commuting involutions is an
isomorphism on the iterated Borel cohomology. -/
theorem bijective_iterated (h : ∀ n, Function.Bijective (Hmap Φ.φ n)) :
    ∀ n, Function.Bijective (HRmap (borelHom Φ) n) := by
  apply bijective_of_ordinary
  intro n
  have hR := bijective_of_ordinary Φ.φ h n
  have hcomp : ⇑(Hmap (borelHom Φ) n) =
      ⇑(cohomologyEquiv SL n).symm ∘ ⇑(HRmap Φ.φ n) ∘ ⇑(cohomologyEquiv SK n) := by
    funext z
    exact Hmap_borelHom Φ n z
  rw [hcomp]
  exact (cohomologyEquiv SL n).symm.bijective.comp (hR.comp (cohomologyEquiv SK n).bijective)

end Iterated

/-- A degreewise short exact sequence of complexes with commuting second involutions induces a
degreewise short exact sequence of the iterated Borel complexes. -/
theorem shortExact_iterated {K' K K'' : InvComplex} {S' : Commuting K'} {S : Commuting K}
    {S'' : Commuting K''} (I : CommHom S' S) (P : CommHom S S'')
    (h : BorelExact.ShortExact I.φ P.φ) : BorelExact.ShortExact (borelHom I) (borelHom P) where
  inj n := by
    intro x y hxy
    apply Subtype.ext
    exact BorelExact.seqMap_injective h (congrArg Subtype.val hxy)
  surj n := by
    intro c
    obtain ⟨b, hb, hπ⟩ := BorelExact.exists_seq_preimage h c.2
    exact ⟨⟨b, hb⟩, Subtype.ext hπ⟩
  zero n z := Subtype.ext (BorelExact.seqMap_comp_zero h _)
  exact n x hx := by
    obtain ⟨z, hz, hι⟩ := BorelExact.exists_seq_lift h x.2 (congrArg Subtype.val hx)
    exact ⟨⟨z, hz⟩, Subtype.ext hι⟩

end

end Finsler.BorelQuasiIso
