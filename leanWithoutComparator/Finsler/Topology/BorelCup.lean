module

public import Finsler.Topology.BorelGraded
public import Finsler.Topology.BorelComparison

/-! Actual relative Alexander--Whitney cup by a closed strictly reflection-invariant
ambient cochain. The quotient action commutes with w, forget to native relative
cohomology, transfer, and actual equivariant pair maps. Independence from changing
the left cocycle representative and full left module laws remain separate. -/

@[expose] public section

namespace Finsler.BorelCup
open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (P : TopPair.{0}) (r : P ⟶ P) (hr : r ≫ r = 𝟙 P)
variable (p : ℕ) (α : singularCochainGroup (ZMod 2) P.fst p)
variable (hα : cochainCoboundary (ZMod 2) P.fst p α = 0)
variable (hi : cochainPullback (TopPair.Hom.fst r) p α = α)

theorem cast_relative {a b : ℕ} (h : a=b) (x : RelativeCupCochain.relative P a) :
    RelativeCupCochain.cast P h x = BorelGraded.castC (ofPair P r hr) h x := by
  subst b
  rfl

/-- Actual Alexander--Whitney multiplication by a closed, strictly invariant cochain. -/
def gradedCup : BorelGraded.Map (ofPair P r hr) (ofPair P r hr) p where
  f j := {
    toFun := RelativeCupCochain.cup P p j α
    map_add' := RelativeCupCochain.add_right P p j α
    map_smul' := fun r ψ => RelativeCupCochain.smul_right P p j r α ψ }
  comm_d j x := by
    change RelativeCupCochain.differential P (p+j) (RelativeCupCochain.cup P p j α x) = _
    have h := RelativeCupCochain.differential_cup P p j α x
    rw [hα, RelativeCupCochain.zero_left, RelativeCupCochain.cast_zero, zero_add] at h
    exact h.trans (cast_relative P r hr _ _)
  comm_t j x := by
    change RelativeCupCochain.pullback r (p+j) (RelativeCupCochain.cup P p j α x) =
      RelativeCupCochain.cup P p j α (RelativeCupCochain.pullback r j x)
    rw [RelativeCupCochain.naturality, hi]

/-- Reflection-equivariant relative cup by an invariant cocycle, on actual Borel quotients. -/
def cup (q : ℕ) : HR (ofPair P r hr) q →ₗ[ZMod 2] HR (ofPair P r hr) (p+q) :=
  BorelGraded.onHR (gradedCup P r hr p α hα hi) q

theorem cup_w (q : ℕ) (x : HR (ofPair P r hr) q) :
    BorelGraded.castHR (Nat.add_assoc p q 1).symm (cup P r hr p α hα hi (q+1) (w _ q x)) =
      w _ (p+q) (cup P r hr p α hα hi q x) :=
  BorelGraded.onHR_w _ q x

theorem forgetNative_mk (q : ℕ) (c : bcocycles (ofPair P r hr) q) :
    BorelComparison.forgetNative P r hr q (Submodule.Quotient.mk c) =
      CochainClass.classOf (cochains P) q (c.val q) (bcocycle_comp _ q c) :=
  BorelComparison.ordinaryEquiv_mk P r hr q (forgetCocycle _ q c)

theorem cup_forgetNative (q : ℕ) (x : HR (ofPair P r hr) q) :
    BorelComparison.forgetNative P r hr (p+q) (cup P r hr p α hα hi q x) =
      RelativeCup.cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα)
        (BorelComparison.forgetNative P r hr q x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let A := gradedCup P r hr p α hα hi
  let z := BorelGraded.cyclesMap A q c
  let v := RelativeCupCochain.cup P p q α (c.val q)
  have hv : RelativeCupCochain.differential P (p+q) v = 0 :=
    RelativeCupCochain.preserves_cocycles P p q α (c.val q) hα (bcocycle_comp _ q c)
  calc
    _ = CochainClass.classOf (cochains P) (p+q) (z.val (p+q)) (bcocycle_comp _ _ z) :=
      forgetNative_mk P r hr (p+q) z
    _ = CochainClass.classOf (cochains P) (p+q) v hv :=
      CochainClass.classOf_congr (cochains P) (p+q) (BorelGraded.total_at A c.val q) _ _
    _ = RelativeCup.cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα)
        (CochainClass.classOf (cochains P) q (c.val q) (bcocycle_comp _ q c)) :=
      (RelativeCup.cup_mk P p q α hα (c.val q) (bcocycle_comp _ q c)).symm
    _ = _ := congrArg (RelativeCup.cup P p q (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα))
      (forgetNative_mk P r hr q c).symm

theorem ordinaryCup_mk (q : ℕ) (x : cocycles (ofPair P r hr) q) :
    BorelComparison.ordinaryCup P r hr p q (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα)
      (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk (⟨RelativeCupCochain.cup P p q α x.val,
      RelativeCupCochain.preserves_cocycles P p q α x.val hα x.property⟩ : cocycles (ofPair P r hr) (p+q)) := by
  apply (BorelComparison.ordinaryEquiv P r hr (p+q)).injective
  rw [BorelComparison.ordinaryCup_native, BorelComparison.ordinaryEquiv_mk,
    BorelComparison.ordinaryEquiv_mk, RelativeCup.cup_mk]

theorem cup_transfer (q : ℕ) (x : H (ofPair P r hr) q) :
    cup P r hr p α hα hi q (transfer _ q x) =
    transfer _ (p+q) (BorelComparison.ordinaryCup P r hr p q
      (CochainClass.classOf (cochainCxZMod2 P.fst) p α hα) x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [ordinaryCup_mk, transfer, Submodule.mapQ_apply]
  change Submodule.Quotient.mk (BorelGraded.cyclesMap (gradedCup P r hr p α hα hi) q (trCocycle _ q c)) = _
  rw [transfer, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change BorelGraded.total (gradedCup P r hr p α hα hi)
      (Pi.single q (tr _ q c.val)) = Pi.single (p+q) (tr _ (p+q) (RelativeCupCochain.cup P p q α c.val))
  rw [BorelGraded.total_single]
  exact congrArg (Pi.single (p+q)) (BorelGraded.comm_tr (gradedCup P r hr p α hα hi) q c.val).symm

theorem cup_natural {P Q : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q}
    (hr : r≫r=𝟙 P) (hs : s≫s=𝟙 Q) (f : P ⟶ Q) (hf : f≫s=r≫f)
    (p : ℕ) (α : singularCochainGroup (ZMod 2) Q.fst p)
    (hα : cochainCoboundary (ZMod 2) Q.fst p α=0)
    (hi : cochainPullback (TopPair.Hom.fst s) p α=α)
    (β : singularCochainGroup (ZMod 2) P.fst p)
    (hβ : cochainCoboundary (ZMod 2) P.fst p β=0)
    (hj : cochainPullback (TopPair.Hom.fst r) p β=β)
    (he : cochainPullback (TopPair.Hom.fst f) p α=β) (q : ℕ) (x : HR (ofPair Q s hs) q) :
    HRmap (pullHom hr hs f hf) (p+q) (cup Q s hs p α hα hi q x) =
      cup P r hr p β hβ hj q (HRmap (pullHom hr hs f hf) q x) := by
  apply BorelGraded.onHR_natural
  intro j z
  change RelativeCupCochain.pullback f (p+j) (RelativeCupCochain.cup Q p j α z) =
    RelativeCupCochain.cup P p j β (RelativeCupCochain.pullback f j z)
  rw [RelativeCupCochain.naturality, he]

end
end Finsler.BorelCup
