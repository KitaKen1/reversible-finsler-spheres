module

public import Finsler.Topology.TrivialK
public import Finsler.Topology.TripleK

/-! The components of iterated Borel classes for a trivial second involution, the class v and
connecting maps. For a complex with a trivial second involution a class of degree n of the
iterated Borel cohomology has components of the degrees j ≤ n in the Borel cohomology of the
inner complex. Multiplication by the class v of the second involution raises the degree and
leaves every component unchanged; the components of degree above n vanish. For a short exact
sequence of complexes with trivial second involutions, the component of degree j + 1 of the
connecting class of the iterated sequence is the connecting class of the component of degree j.
With the rule for the reflection class (`TrivialK.theta_innerStep_succ`) these are the rules of
the normalized restriction to the fixed loops: v leaves a vector unchanged, w raises the root
degree, and the connecting maps raise the root degree by one. -/

@[expose] public section

namespace Finsler.ThetaLadder

open Finsler.BorelCochain Finsler.BorelIterate Finsler.BorelExact Finsler.BorelFreeK
open Finsler.TrivialK

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section One

variable {K : InvComplex} (S : Commuting K) (hS : ∀ j x, S.s j x = x)

/-- Multiplication by the class of the second involution leaves the components unchanged. -/
theorem theta_w (n j : ℕ) (x : HR (borelInv S) n) :
    theta S hS (n + 1) j (w (borelInv S) n x) = theta S hS n j x := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- The components of degree above the degree of the class vanish. -/
theorem theta_high (n j : ℕ) (hj : n < j) (x : HR (borelInv S) n) : theta S hS n j x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h0 : (c : Seq (borelInv S)) j = 0 :=
    ((mem_bcocycles (borelInv S)).mp c.2).1 j (by omega)
  have e : compCocycle (borelInv S) (borelInv_trivial S hS) n j c = 0 := Subtype.ext h0
  rw [theta_mk, e, (cocycleEquiv S j).map_zero]
  exact Submodule.Quotient.mk_zero _

end One

section Sequence

variable {K' K K'' : InvComplex} {S' : Commuting K'} {S : Commuting K} {S'' : Commuting K''}
  (I : CommHom S' S) (P : CommHom S S'') (h : ShortExact I.φ P.φ)
  (hS' : ∀ j x, S'.s j x = x) (hS : ∀ j x, S.s j x = x) (hS'' : ∀ j x, S''.s j x = x)

include hS in
/-- For trivial second involutions, the component of degree j + 1 of the connecting class of the
iterated sequence is the connecting class of the component of degree j. -/
theorem theta_delta (n j : ℕ) (x : HR (borelInv S'') n) :
    theta S' hS' (n + 1) (j + 1) (delta (BorelQuasiIso.shortExact_iterated I P h) n x) =
      delta h j (theta S'' hS'' n j x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ :=
    exists_delta_lift (BorelQuasiIso.shortExact_iterated I P h) n c
  rw [delta_mk (BorelQuasiIso.shortExact_iterated I P h) n c b hb hπb ⟨z, hz⟩ hιz, theta_mk,
    theta_mk]
  symm
  refine delta_mk h j _ (seqOf S j (b j)) (toLow S j (b j)).2 ?_ _ ?_
  · exact congrArg (seqOf S'' j) (congrFun hπb j)
  · have h1 := congrFun hιz (j + 1)
    rw [D_succ, tr_eq_zero_of_trivial (borelInv S) (borelInv_trivial S hS), add_zero] at h1
    exact congrArg (seqOf S (j + 1)) h1

include hS in
/-- For trivial second involutions, the component of degree zero of a connecting class of the
iterated sequence vanishes. -/
theorem theta_delta_zero (n : ℕ) (x : HR (borelInv S'') n) :
    theta S' hS' (n + 1) 0 (delta (BorelQuasiIso.shortExact_iterated I P h) n x) = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ :=
    exists_delta_lift (BorelQuasiIso.shortExact_iterated I P h) n c
  rw [delta_mk (BorelQuasiIso.shortExact_iterated I P h) n c b hb hπb ⟨z, hz⟩ hιz, theta_mk]
  have h1 := congrFun hιz 0
  rw [D_zero, tr_eq_zero_of_trivial (borelInv S) (borelInv_trivial S hS)] at h1
  have hz0 : z 0 = 0 := (BorelQuasiIso.shortExact_iterated I P h).inj 0
    (h1.trans (map_zero ((borelHom I).f 0)).symm)
  have e : compCocycle (borelInv S') (borelInv_trivial S' hS') (n + 1) 0 ⟨z, hz⟩ = 0 :=
    Subtype.ext hz0
  rw [e, (cocycleEquiv S' 0).map_zero]
  exact Submodule.Quotient.mk_zero _

end Sequence

end

end Finsler.ThetaLadder
