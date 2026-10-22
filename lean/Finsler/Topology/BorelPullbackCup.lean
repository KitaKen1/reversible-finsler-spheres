module

public import Finsler.Topology.BorelHomotopy
public import Finsler.Topology.BorelEvaluation

/-! Relative Borel cup pulled back along an actual strictly invariant map. Primitives pulled back from the target are strictly invariant, so a target boundary acts by a total coboundary. The linear action of target cocycles descends through the actual homology cokernel. This does not assert that an arbitrary invariant ambient cochain has an invariant primitive. -/

@[expose] public section

namespace Finsler.BorelPullbackCup
open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (P : TopPair.{0}) (r : P ⟶ P) (hr : r≫r=𝟙 P)

def cupFamily (m : ℕ) (η : singularCochainGroup (ZMod 2) P.fst m)
    (hi : cochainPullback (TopPair.Hom.fst r) m η=η) :
    BorelHomotopy.Family (ofPair P r hr) (ofPair P r hr) m where
  f j := {
    toFun := RelativeCupCochain.cup P m j η
    map_add' := RelativeCupCochain.add_right P m j η
    map_smul' := fun a ψ => RelativeCupCochain.smul_right P m j a η ψ }
  comm_t j x := by
    change RelativeCupCochain.pullback r (m+j) (RelativeCupCochain.cup P m j η x) =
      RelativeCupCochain.cup P m j η (RelativeCupCochain.pullback r j x)
    rw [RelativeCupCochain.naturality, hi]

theorem invariantCup_congr (p : ℕ) {α β : singularCochainGroup (ZMod 2) P.fst p}
    (he : α=β) (hα : cochainCoboundary (ZMod 2) P.fst p α=0)
    (hβ : cochainCoboundary (ZMod 2) P.fst p β=0)
    (hi : cochainPullback (TopPair.Hom.fst r) p α=α)
    (hj : cochainPullback (TopPair.Hom.fst r) p β=β) (q : ℕ) :
    BorelCup.cup P r hr p α hα hi q = BorelCup.cup P r hr p β hβ hj q := by
  subst β
  rfl

theorem invariant_boundary_zero (m : ℕ) (η : singularCochainGroup (ZMod 2) P.fst m)
    (hi : cochainPullback (TopPair.Hom.fst r) m η=η)
    (hα : cochainCoboundary (ZMod 2) P.fst (m+1) (cochainCoboundary (ZMod 2) P.fst m η)=0)
    (hj : cochainPullback (TopPair.Hom.fst r) (m+1) (cochainCoboundary (ZMod 2) P.fst m η)=
      cochainCoboundary (ZMod 2) P.fst m η)
    (q : ℕ) (x : HR (ofPair P r hr) q) :
    BorelCup.cup P r hr (m+1) (cochainCoboundary (ZMod 2) P.fst m η) hα hj q x=0 := by
  apply BorelHomotopy.onHR_zero (cupFamily P r hr m η hi)
  intro j y
  change RelativeCupCochain.differential P (m+j) (RelativeCupCochain.cup P m j η y) = _
  have h := RelativeCupCochain.differential_cup P m j η y
  rw [BorelCup.cast_relative P r hr, BorelCup.cast_relative P r hr] at h
  exact h

variable {X : TopCat.{0}} (f : P.fst ⟶ X) (hf : TopPair.Hom.fst r≫f=f)

def cochainCup (p : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (q : ℕ) :
    HR (ofPair P r hr) q →ₗ[ZMod 2] HR (ofPair P r hr) (p+q) :=
  BorelCup.cup P r hr p (cochainPullback f p α) (cochainPullback_cocycle f p α hα)
    (BorelEvaluation.cochain_invariant r f hf p α) q

theorem cochainCup_congr (p : ℕ) {α β : singularCochainGroup (ZMod 2) X p}
    (heq : α=β) (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hβ : cochainCoboundary (ZMod 2) X p β=0) (q : ℕ) :
    cochainCup P r hr f hf p α hα q = cochainCup P r hr f hf p β hβ q := by
  subst β
  rfl

theorem cochainCup_boundary_zero (i p : ℕ) (η : (cochainCxZMod2 X).X i)
    (hα : cochainCoboundary (ZMod 2) X p (((cochainCxZMod2 X).d i p).hom η)=0)
    (q : ℕ) (x : HR (ofPair P r hr) q) :
    cochainCup P r hr f hf p (((cochainCxZMod2 X).d i p).hom η) hα q x=0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i+1=p := h
    have he : cochainPullback f (i+1) (((cochainCxZMod2 X).d i (i+1)).hom η) =
        cochainCoboundary (ZMod 2) P.fst i (cochainPullback f i η) :=
      (cochainPullback_cochainCoboundary f i η).symm
    have hc := cochainPullback_cocycle f (i+1) _ hα
    have hi := BorelEvaluation.cochain_invariant r f hf (i+1) (((cochainCxZMod2 X).d i (i+1)).hom η)
    have hb : cochainCoboundary (ZMod 2) P.fst (i+1)
        (cochainCoboundary (ZMod 2) P.fst i (cochainPullback f i η))=0 := by
      rw [← he]
      exact hc
    have hj : cochainPullback (TopPair.Hom.fst r) (i+1)
        (cochainCoboundary (ZMod 2) P.fst i (cochainPullback f i η))=
        cochainCoboundary (ZMod 2) P.fst i (cochainPullback f i η) := by
      rw [← he]
      exact hi
    calc
      _ = BorelCup.cup P r hr (i+1) (cochainCoboundary (ZMod 2) P.fst i
          (cochainPullback f i η)) hb hj q x :=
        congrArg (fun A => A x) (invariantCup_congr P r hr (i+1) he hc hb hi hj q)
      _ = 0 := invariant_boundary_zero P r hr i (cochainPullback f i η)
        (BorelEvaluation.cochain_invariant r f hf i η) hb hj q x
  · have hz : ((cochainCxZMod2 X).d i p).hom η=0 := by
      rw [(cochainCxZMod2 X).shape i p h, ModuleCat.hom_zero, LinearMap.zero_apply]
    -- The zero cup is immediate from its component formula.
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    unfold cochainCup BorelCup.cup
    rw [BorelGraded.onHR_mk, Submodule.Quotient.mk_eq_zero]
    have ht : BorelGraded.total (BorelCup.gradedCup P r hr p (cochainPullback f p
        (((cochainCxZMod2 X).d i p).hom η))
        (cochainPullback_cocycle f p _ hα)
        (BorelEvaluation.cochain_invariant r f hf p (((cochainCxZMod2 X).d i p).hom η))) (c : Seq (ofPair P r hr))=0 := by
      funext j
      by_cases hp : p≤j
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
        rw [BorelGraded.total_at]
        change RelativeCupCochain.cup P p k (cochainPullback f p
          (((cochainCxZMod2 X).d i p).hom η)) (c.val k)=0
        rw [hz]
        have h0 : cochainPullback f p 0=0 := map_zero ((singularCochainComplexZMod2.map f.op).f p).hom
        rw [h0, RelativeCupCochain.zero_left]
      · exact BorelGraded.total_below _ _ (by omega)
    change (BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val) ∈ bcoboundaries (ofPair P r hr) (p+q)
    rw [ht]
    exact Submodule.zero_mem _

theorem cochainCup_add (p : ℕ) (α β : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hβ : cochainCoboundary (ZMod 2) X p β=0)
    (hs : cochainCoboundary (ZMod 2) X p (α+β)=0) (q : ℕ) :
    cochainCup P r hr f hf p (α+β) hs q =
      cochainCup P r hr f hf p α hα q + cochainCup P r hr f hf p β hβ q := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cochainCup, BorelCup.cup, LinearMap.add_apply, BorelGraded.onHR_mk]
  rw [← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  funext j
  by_cases hp : p≤j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    change BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val (p+k) = BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val (p+k) + BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val (p+k)
    rw [BorelGraded.total_at, BorelGraded.total_at, BorelGraded.total_at]
    change RelativeCupCochain.cup P p k (cochainPullback f p (α+β)) (c.val k) =
      RelativeCupCochain.cup P p k (cochainPullback f p α) (c.val k) +
      RelativeCupCochain.cup P p k (cochainPullback f p β) (c.val k)
    have he : cochainPullback f p (α+β)=cochainPullback f p α+cochainPullback f p β :=
      map_add ((singularCochainComplexZMod2.map f.op).f p).hom α β
    rw [he, RelativeCupCochain.add_left]
  · change BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val j = BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val j + BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val j
    rw [BorelGraded.total_below _ _ (by omega), BorelGraded.total_below _ _ (by omega), BorelGraded.total_below _ _ (by omega), add_zero]

theorem cochainCup_smul (p : ℕ) (a : ZMod 2) (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hs : cochainCoboundary (ZMod 2) X p (a • α)=0) (q : ℕ) :
    cochainCup P r hr f hf p (a • α) hs q = a • cochainCup P r hr f hf p α hα q := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cochainCup, BorelCup.cup, LinearMap.smul_apply, BorelGraded.onHR_mk]
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  funext j
  by_cases hp : p≤j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    change BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val (p+k) = a • BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val (p+k)
    rw [BorelGraded.total_at, BorelGraded.total_at]
    change RelativeCupCochain.cup P p k (cochainPullback f p (a • α)) (c.val k) =
      a • RelativeCupCochain.cup P p k (cochainPullback f p α) (c.val k)
    have he : cochainPullback f p (a • α)=a • cochainPullback f p α :=
      map_smul ((singularCochainComplexZMod2.map f.op).f p).hom a α
    rw [he, RelativeCupCochain.smul_left]
  · change BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val j = a • BorelGraded.total (K := ofPair P r hr) (L := ofPair P r hr) (p := p) _ c.val j
    rw [BorelGraded.total_below _ _ (by omega), BorelGraded.total_below _ _ (by omega), smul_zero]

/-- A linear action of actual target cocycles, valued in linear operators on relative Borel cohomology. -/
def cycleAction (p q : ℕ) : (cochainCxZMod2 X).cycles p ⟶
    ModuleCat.of (ZMod 2) (HR (ofPair P r hr) q →ₗ[ZMod 2] HR (ofPair P r hr) (p+q)) :=
  ModuleCat.ofHom {
    toFun c := cochainCup P r hr f hf p (((cochainCxZMod2 X).iCycles p).hom c)
      (CochainClass.closed_iCycles (cochainCxZMod2 X) p c) q
    map_add' c d := by
      simp only [map_add]
      exact cochainCup_add P r hr f hf p _ _ _ _ _ q
    map_smul' a c := by
      simp only [map_smul]
      exact cochainCup_smul P r hr f hf p a _ _ _ q }

theorem cycleAction_boundary (p q : ℕ) :
    (cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cycleAction P r hr f hf p q=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro η
  apply LinearMap.ext
  intro x
  change cochainCup P r hr f hf p
      (((cochainCxZMod2 X).iCycles p).hom (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev p) p).hom η))
      (CochainClass.closed_iCycles _ _ _) q x=0
  have he := ConcreteCategory.congr_hom
    ((cochainCxZMod2 X).toCycles_i ((ComplexShape.up ℕ).prev p) p) η
  have hc := CochainClass.closed_boundary (cochainCxZMod2 X) ((ComplexShape.up ℕ).prev p) p η
  exact (congrArg (fun A => A x) (cochainCup_congr P r hr f hf p he _ hc q)).trans
    (cochainCup_boundary_zero P r hr f hf ((ComplexShape.up ℕ).prev p) p η hc q x)

/-- Representative-independent action of actual target cohomology classes. -/
def classAction (p q : ℕ) : cohomologyZMod2 X p ⟶
    ModuleCat.of (ZMod 2) (HR (ofPair P r hr) q →ₗ[ZMod 2] HR (ofPair P r hr) (p+q)) :=
  CochainClass.descend (cochainCxZMod2 X) p (cycleAction P r hr f hf p q)
    (cycleAction_boundary P r hr f hf p q)

theorem classAction_mk (p : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (q : ℕ) :
    (classAction P r hr f hf p q).hom (CochainClass.classOf (cochainCxZMod2 X) p α hα)=
      cochainCup P r hr f hf p α hα q := by
  rw [classAction, CochainClass.descend_classOf]
  change cochainCup P r hr f hf p (((cochainCxZMod2 X).iCycles p).hom
    ((cochainCxZMod2 X).cyclesMk α (p+1) (CochainClass.next_eq p) hα))
    (CochainClass.closed_iCycles _ _ _) q = _
  exact cochainCup_congr P r hr f hf p ((cochainCxZMod2 X).i_cyclesMk _ _ _ _) _ hα q

theorem cochainCup_class_congr (p : ℕ) (α β : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (hβ : cochainCoboundary (ZMod 2) X p β=0)
    (he : CochainClass.classOf (cochainCxZMod2 X) p α hα = CochainClass.classOf (cochainCxZMod2 X) p β hβ)
    (q : ℕ) : cochainCup P r hr f hf p α hα q = cochainCup P r hr f hf p β hβ q := by
  rw [← classAction_mk P r hr f hf p α hα q, ← classAction_mk P r hr f hf p β hβ q, he]
end
end Finsler.BorelPullbackCup
