module

public import Finsler.Topology.BorelExact
public import Finsler.Topology.BorelGraded
public import Finsler.Topology.OrdinaryDelta
public import Finsler.Topology.BorelCup
public import Finsler.Topology.PairTriple
public import Finsler.Topology.BorelCrossing

/-! The connecting map is linear over compatible graded maps.

For a degreewise short exact sequence 0 → K' → K → K'' → 0 of involutive complexes and
degree-p equivariant cochain maps A', A, A'' of the three complexes commuting with the two maps
of the sequence, the connecting map of reflection Borel cohomology commutes with the induced
actions: δ(A'' x) = A'(δ x). Cochain level: if b lifts the cocycle c and ι z = D b, then the
total map of A applied to b lifts A'' c and its differential is ι of the total map of A' applied to
z. The main use is the cup with the pullback of an absolute cocycle (`BorelCup.gradedCup`), which
commutes with restriction to subpairs: the connecting map of a triple is linear over cup with
absolute classes (the suspension linearity needed for the e-compatibility of Thom pairs). -/

@[expose] public section

namespace Finsler.GradedDelta

open Finsler.BorelCochain Finsler.BorelExact Finsler.BorelGraded

noncomputable section

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)
  {p : ℕ} (A' : Map K' K' p) (A : Map K K p) (A'' : Map K'' K'' p)
  (hl : ∀ j z, ι.f (p + j) (A'.f j z) = A.f j (ι.f j z))
  (hr : ∀ j x, π.f (p + j) (A.f j x) = A''.f j (π.f j x))

include hl hr in
/-- **The connecting map is linear over compatible graded maps.** -/
theorem delta_onHR (n : ℕ) (x : HR K'' n) :
    delta h (p + n) (onHR A'' n x) =
      castHR (Nat.add_assoc p n 1).symm (onHR A' (n + 1) (delta h n x)) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨b, z, hb, hπb, hz, hιz⟩ := exists_delta_lift h n c
  rw [delta_mk h n c b hb hπb ⟨z, hz⟩ hιz, onHR_mk, onHR_mk]
  have hb' : total A b ∈ low K (p + n + 1) := total_low A hb
  have hπb' : seqMap π (total A b) = (cyclesMap A'' n c : Seq K'') := by
    change seqMap π (total A b) = total A'' (c : Seq K'')
    rw [total_natural A A'' π π hr b, hπb]
  have hz' : total A' z ∈ bcocycles K' (p + n + 1) := (cyclesMap A' (n + 1) ⟨z, hz⟩).2
  have hιz' : seqMap ι (total A' z) = D K (total A b) := by
    rw [total_natural A' A ι ι hl z, hιz, total_D]
  rw [delta_mk h (p + n) (cyclesMap A'' n c) (total A b) hb' hπb' ⟨total A' z, hz'⟩ hιz']
  exact (castHR_mk _ _ _ _).symm

/-! ### Ordinary cohomology -/

section Ordinary

variable {L : InvComplex}

theorem f_cocycle (B : Map K L p) (q : ℕ) (x : K.C q) (hx : K.d q x = 0) :
    L.d (p + q) (B.f q x) = 0 := by
  rw [B.comm_d, hx, map_zero, map_zero]

/-- A graded map on cocycles. -/
def cocMap (B : Map K L p) (q : ℕ) : cocycles K q →ₗ[ZMod 2] cocycles L (p + q) :=
  LinearMap.codRestrict (cocycles L (p + q)) (B.f q ∘ₗ (cocycles K q).subtype)
    fun c => f_cocycle B q c c.2

theorem cocMap_boundary (B : Map K L p) (q : ℕ) :
    (coboundaries K q).comap (cocycles K q).subtype ≤
      ((coboundaries L (p + q)).comap (cocycles L (p + q)).subtype).comap (cocMap B q) := by
  intro c hc
  change B.f q (c : K.C q) ∈ coboundaries L (p + q)
  have hc' : (c : K.C q) ∈ coboundaries K q := hc
  cases q with
  | zero =>
    have h0 : (c : K.C 0) = 0 := (Submodule.mem_bot (ZMod 2)).mp hc'
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨u, hu⟩ := hc'
    refine ⟨B.f m u, ?_⟩
    exact (B.comm_d m u).trans (by rw [hu]; rfl)

/-- The action of a graded map on ordinary cohomology. -/
def onH (B : Map K L p) (q : ℕ) : H K q →ₗ[ZMod 2] H L (p + q) :=
  Submodule.mapQ _ _ (cocMap B q) (cocMap_boundary B q)

include hl hr in
/-- **The ordinary connecting map is linear over compatible graded maps.** -/
theorem odelta_onH (n : ℕ) (x : H K'' n) :
    OrdinaryDelta.delta h (p + n) (onH A'' n x) = onH A' (n + 1) (OrdinaryDelta.delta h n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (OrdinaryDelta.deltaCocycle h (p + n) (cocMap A'' n c)) =
    Submodule.Quotient.mk (cocMap A' (n + 1) (OrdinaryDelta.deltaCocycle h n c))
  rw [Submodule.Quotient.eq]
  change ret h (p + n + 1) (K.d (p + n) (sec h (p + n) (A''.f n (c : K''.C n)))) -
      A'.f (n + 1) (ret h (n + 1) (K.d n (sec h n (c : K''.C n)))) ∈ coboundaries K' (p + n + 1)
  have hb : π.f (p + n) (A.f n (sec h n (c : K''.C n))) = A''.f n (c : K''.C n) := by
    rw [hr, proj_sec]
  obtain ⟨v, hv⟩ := OrdinaryDelta.d_sec_eq h (p + n) _ _ hb
  have hd : K.d (p + n) (A.f n (sec h n (c : K''.C n))) =
      ι.f (p + n + 1) (A'.f (n + 1) (ret h (n + 1) (K.d n (sec h n (c : K''.C n))))) := by
    rw [A.comm_d]
    change A.f (n + 1) (K.d n (sec h n (c : K''.C n))) = _
    have e := OrdinaryDelta.incl_ret_d_sec h n _ c.2
    calc A.f (n + 1) (K.d n (sec h n (c : K''.C n))) =
        A.f (n + 1) (ι.f (n + 1) (ret h (n + 1) (K.d n (sec h n (c : K''.C n))))) := by rw [e]
      _ = _ := (hl (n + 1) _).symm
  rw [hv, hd, ← map_add, ret_incl, add_sub_cancel_left]
  exact ⟨v, rfl⟩

end Ordinary

/-! ### The connecting map of a triple and cup with an absolute cocycle -/

section Triple

open CategoryTheory SphereOddDegree Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.BorelCrossing

variable {X : TopCat.{0}} {s t u : Set X} (hst : s ⊆ t) (htu : t ⊆ u) {q : ℕ}
  (α : singularCochainGroup (ZMod 2) (TopCat.of ↥u) q)
  (hα : cochainCoboundary (ZMod 2) (TopCat.of ↥u) q α = 0)

/-- The restriction of the cocycle to t. -/
def resα : singularCochainGroup (ZMod 2) (pairOf hst).fst q :=
  cochainPullback (TopPair.Hom.fst (incPair hst htu)) q α

include hα in
theorem resα_cocycle :
    cochainCoboundary (ZMod 2) (pairOf hst).fst q (resα hst htu α) = 0 :=
  cochainPullback_cocycle _ q α hα

/-- The cup with the cocycle on the cochains of (u, t). -/
def cupUT : BorelGraded.Map (triv (pairOf htu)) (triv (pairOf htu)) q :=
  BorelCup.gradedCup (pairOf htu) (𝟙 _) (Category.comp_id _) q α hα (cochain_id q α)

/-- The cup with the cocycle on the cochains of (u, s). -/
def cupUS : BorelGraded.Map (triv (pairOf (hst.trans htu))) (triv (pairOf (hst.trans htu))) q :=
  BorelCup.gradedCup (pairOf (hst.trans htu)) (𝟙 _) (Category.comp_id _) q α hα (cochain_id q α)

/-- The cup with the restricted cocycle on the cochains of (t, s). -/
def cupTS : BorelGraded.Map (triv (pairOf hst)) (triv (pairOf hst)) q :=
  BorelCup.gradedCup (pairOf hst) (𝟙 _) (Category.comp_id _) q (resα hst htu α)
    (resα_cocycle hst htu α hα) (cochain_id q _)

/-- **The connecting map of a triple is linear over cup with an absolute cocycle.** -/
theorem tripleDelta_cup (n : ℕ) (x : H (triv (pairOf hst)) n) :
    tripleDelta hst htu (q + n) (onH (cupTS hst htu α hα) n x) =
      onH (cupUT htu α hα) (n + 1) (tripleDelta hst htu n x) := by
  refine odelta_onH (tripleExact hst htu) (cupUT htu α hα) (cupUS hst htu α hα)
    (cupTS hst htu α hα) (fun j z => ?_) (fun j z => ?_) n x
  · change RelativeCupCochain.pullback (relPair hst htu) (q + j)
        (RelativeCupCochain.cup (pairOf htu) q j α z) =
      RelativeCupCochain.cup (pairOf (hst.trans htu)) q j α
        (RelativeCupCochain.pullback (relPair hst htu) j z)
    have h1 := RelativeCupCochain.naturality (relPair hst htu) q j α z
    have h2 : cochainPullback (TopPair.Hom.fst (relPair hst htu)) q α = α := by
      rw [relPair_fst]
      exact cochain_id q α
    rw [h2] at h1
    exact h1
  · change RelativeCupCochain.pullback (incPair hst htu) (q + j)
        (RelativeCupCochain.cup (pairOf (hst.trans htu)) q j α z) =
      RelativeCupCochain.cup (pairOf hst) q j (resα hst htu α)
        (RelativeCupCochain.pullback (incPair hst htu) j z)
    exact RelativeCupCochain.naturality (incPair hst htu) q j α z

end Triple

end

end Finsler.GradedDelta
