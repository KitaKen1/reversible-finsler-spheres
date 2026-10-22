module

public import Finsler.Topology.BorelPair
public import Finsler.Topology.CochainClass
public import Finsler.Topology.RelativeCup
public import Finsler.Topology.CupUnit
public import Finsler.Topology.CupAssociativity


/-! The ordinary cohomology of the involutive relative cochains is naturally
isomorphic to Tau Ceti's actual relative singular cohomology, including degree zero.
The comparison transports the reflection Gysin sequence and the already-verified
ordinary relative cup. Equivariant cup, O(2), and localization are separate obligations. -/

@[expose] public section


namespace Finsler.BorelComparison

open CategoryTheory Finsler.BorelCochain Finsler.BorelPair

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (P : TopPair.{0}) (r : P ⟶ P) (hr : r ≫ r = 𝟙 P)

abbrev ordinary (n : ℕ) := H (ofPair P r hr) n
abbrev native (n : ℕ) := (cochains P).homology n
abbrev sc (n : ℕ) := (cochains P).sc' ((ComplexShape.up ℕ).prev n) n (n + 1)

abbrev boundaries (n : ℕ) :=
  (coboundaries (ofPair P r hr) n).comap (cocycles (ofPair P r hr) n).subtype

theorem boundaries_eq (n : ℕ) :
    boundaries P r hr n = (sc P n).moduleCatToCycles.range := by
  rw [LinearMap.range_codRestrict]
  change (coboundaries (ofPair P r hr) n).comap (cocycles (ofPair P r hr) n).subtype =
    (((cochains P).d ((ComplexShape.up ℕ).prev n) n).hom.range).comap
      (cocycles (ofPair P r hr) n).subtype
  congr 1
  cases n with
  | zero =>
    rw [CochainComplex.prev_nat_zero]
    have hz : (cochains P).d 0 0 = 0 := (cochains P).shape 0 0 (by simp)
    rw [hz]
    simp [coboundaries]
  | succ m =>
    rw [CochainComplex.prev_nat_succ]
    rfl

def kernelEquiv (n : ℕ) : cocycles (ofPair P r hr) n ≃ₗ[ZMod 2]
    (sc P n).g.hom.ker where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem boundaries_map (n : ℕ) :
    (boundaries P r hr n).map (kernelEquiv P r hr n).toLinearMap =
      (sc P n).moduleCatToCycles.range := by
  ext x
  rw [← boundaries_eq P r hr n]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨(kernelEquiv P r hr n).symm x, hx, rfl⟩

def nativeQuotientIso (n : ℕ) :
    (cochains P).homology n ≅ (sc P n).moduleCatLeftHomologyData.H :=
  (cochains P).homologyIsoSc' _ n (n + 1) rfl (Finsler.CochainClass.next_eq n) ≪≫
    (sc P n).moduleCatHomologyIso


def ordinaryEquiv (n : ℕ) : ordinary P r hr n ≃ₗ[ZMod 2] native P n :=
  (Submodule.Quotient.equiv (boundaries P r hr n) ((sc P n).moduleCatToCycles.range)
    (kernelEquiv P r hr n) (boundaries_map P r hr n)).trans
    ((nativeQuotientIso P n).toLinearEquiv.symm)

theorem nativeQuotientIso_classOf (n : ℕ) (x : cocycles (ofPair P r hr) n) :
    ((nativeQuotientIso P n).hom).hom
      (Finsler.CochainClass.classOf (cochains P) n x.val x.property) =
      (Submodule.mkQ (sc P n).moduleCatToCycles.range) (kernelEquiv P r hr n x) := by
  let c := (cochains P).cyclesMk x.val (n + 1) (Finsler.CochainClass.next_eq n) x.property
  let z := (((cochains P).cyclesIsoSc' _ n (n + 1) rfl
    (Finsler.CochainClass.next_eq n)).hom).hom c
  have hx : ((sc P n).moduleCatCyclesIso.hom).hom z = kernelEquiv P r hr n x := by
    apply Subtype.ext
    calc
      _ = ((sc P n).iCycles).hom z :=
        ConcreteCategory.congr_hom ((sc P n).moduleCatCyclesIso_hom_i) z
      _ = ((cochains P).iCycles n).hom c :=
        ConcreteCategory.congr_hom ((cochains P).cyclesIsoSc'_hom_iCycles _ n (n + 1)
          rfl (Finsler.CochainClass.next_eq n)) c
      _ = x.val := (cochains P).i_cyclesMk _ _ _ _
  change ((sc P n).moduleCatHomologyIso.hom).hom
    (((cochains P).homologyIsoSc' _ n (n + 1) rfl
      (Finsler.CochainClass.next_eq n)).hom.hom ((cochains P).homologyπ n |>.hom c)) = _
  calc
    _ = ((sc P n).moduleCatHomologyIso.hom).hom ((sc P n).homologyπ.hom z) :=
      congrArg ((sc P n).moduleCatHomologyIso.hom).hom
        (ConcreteCategory.congr_hom ((cochains P).π_homologyIsoSc'_hom _ n (n + 1)
          rfl (Finsler.CochainClass.next_eq n)) c)
    _ = ((sc P n).moduleCatLeftHomologyData.π).hom
        (((sc P n).moduleCatCyclesIso.hom).hom z) :=
      ConcreteCategory.congr_hom ((sc P n).π_moduleCatCyclesIso_hom) z
    _ = _ := congrArg ((sc P n).moduleCatLeftHomologyData.π).hom hx

theorem ordinaryEquiv_mk (n : ℕ) (x : cocycles (ofPair P r hr) n) :
    ordinaryEquiv P r hr n (Submodule.Quotient.mk x) =
      Finsler.CochainClass.classOf (cochains P) n x.val x.property := by
  apply (nativeQuotientIso P n).toLinearEquiv.injective
  calc
    _ = (Submodule.mkQ (sc P n).moduleCatToCycles.range) (kernelEquiv P r hr n x) :=
      (nativeQuotientIso P n).toLinearEquiv.apply_symm_apply _
    _ = _ := (nativeQuotientIso_classOf P r hr n x).symm

/-- Pullback on the actual relative singular cohomology. -/
abbrev nativePull {P Q : TopPair.{0}} (f : P ⟶ Q) (n : ℕ) :
    native Q n →ₗ[ZMod 2] native P n :=
  (HomologicalComplex.homologyMap (pull f) n).hom

/-- The comparison is natural in actual equivariant maps of pairs. -/
theorem ordinaryEquiv_natural {P Q : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q}
    (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q) (f : P ⟶ Q)
    (hf : f ≫ s = r ≫ f) (n : ℕ) (x : ordinary Q s hs n) :
    ordinaryEquiv P r hr n (Hmap (pullHom hr hs f hf) n x) =
      nativePull f n (ordinaryEquiv Q s hs n x) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change ordinaryEquiv P r hr n
    (Submodule.Quotient.mk (cocycleMap (pullHom hr hs f hf) n c)) = _
  rw [ordinaryEquiv_mk, ordinaryEquiv_mk]
  exact (Finsler.CochainClass.classOf_map (cochains Q) (pull f) n c.val c.property
    (cocycleMap (pullHom hr hs f hf) n c).property).symm

/-- Forgetting to the actual relative singular cohomology. -/
def forgetNative (n : ℕ) : HR (ofPair P r hr) n →ₗ[ZMod 2] native P n :=
  (ordinaryEquiv P r hr n).toLinearMap ∘ₗ forget (ofPair P r hr) n

/-- Transfer from the actual relative singular cohomology. -/
def transferNative (n : ℕ) : native P n →ₗ[ZMod 2] HR (ofPair P r hr) n :=
  transfer (ofPair P r hr) n ∘ₗ (ordinaryEquiv P r hr n).symm.toLinearMap

theorem exact_forgetNative (n : ℕ) (x : HR (ofPair P r hr) (n + 1)) :
    forgetNative P r hr (n + 1) x = 0 ↔
      ∃ y, w (ofPair P r hr) n y = x := by
  rw [← exact_forget]
  change ordinaryEquiv P r hr (n + 1) (forget (ofPair P r hr) (n + 1) x) = 0 ↔ _
  exact (ordinaryEquiv P r hr (n + 1)).map_eq_zero_iff

theorem exact_wNative (n : ℕ) (y : HR (ofPair P r hr) n) :
    w (ofPair P r hr) n y = 0 ↔ ∃ z, transferNative P r hr n z = y := by
  rw [exact_w]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨ordinaryEquiv P r hr n z, ?_⟩
    simpa [transferNative] using hz
  · rintro ⟨z, hz⟩
    exact ⟨(ordinaryEquiv P r hr n).symm z, hz⟩

theorem exact_transferNative (n : ℕ) (z : native P n) :
    transferNative P r hr n z = 0 ↔ ∃ y, forgetNative P r hr n y = z := by
  change transfer (ofPair P r hr) n ((ordinaryEquiv P r hr n).symm z) = 0 ↔ _
  rw [exact_transfer]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change ordinaryEquiv P r hr n (forget (ofPair P r hr) n y) = z
    rw [hy, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (ordinaryEquiv P r hr n).injective
    simpa [forgetNative] using hy

theorem forgetNative_natural {P Q : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q}
    (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q) (f : P ⟶ Q)
    (hf : f ≫ s = r ≫ f) (n : ℕ) (x : HR (ofPair Q s hs) n) :
    forgetNative P r hr n (HRmap (pullHom hr hs f hf) n x) =
      nativePull f n (forgetNative Q s hs n x) := by
  change ordinaryEquiv P r hr n (forget _ n (HRmap _ n x)) = _
  rw [← Hmap_forget, ordinaryEquiv_natural]
  rfl

theorem transferNative_natural {P Q : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q}
    (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q) (f : P ⟶ Q)
    (hf : f ≫ s = r ≫ f) (n : ℕ) (z : native Q n) :
    HRmap (pullHom hr hs f hf) n (transferNative Q s hs n z) =
      transferNative P r hr n (nativePull f n z) := by
  change HRmap _ n (transfer _ n ((ordinaryEquiv Q s hs n).symm z)) = _
  rw [HRmap_transfer]
  change transfer (ofPair P r hr) n
    (Hmap (pullHom hr hs f hf) n ((ordinaryEquiv Q s hs n).symm z)) =
      transfer (ofPair P r hr) n ((ordinaryEquiv P r hr n).symm (nativePull f n z))
  apply congrArg (transfer (ofPair P r hr) n)
  apply (ordinaryEquiv P r hr n).injective
  rw [ordinaryEquiv_natural, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The already-verified ambient-relative cup, transported to the ordinary
cohomology of the involutive complex. This is not an equivariant cup product. -/
def ordinaryCup (p q : ℕ) (a : SphereOddDegree.cohomologyZMod2 P.fst p)
    (b : ordinary P r hr q) : ordinary P r hr (p + q) :=
  (ordinaryEquiv P r hr (p + q)).symm
    (Finsler.RelativeCup.cup P p q a (ordinaryEquiv P r hr q b))

theorem ordinaryCup_native (p q : ℕ) (a : SphereOddDegree.cohomologyZMod2 P.fst p)
    (b : ordinary P r hr q) :
    ordinaryEquiv P r hr (p + q) (ordinaryCup P r hr p q a b) =
      Finsler.RelativeCup.cup P p q a (ordinaryEquiv P r hr q b) :=
  (ordinaryEquiv P r hr (p + q)).apply_symm_apply _

theorem ordinaryCup_natural {P Q : TopPair.{0}} {r : P ⟶ P} {s : Q ⟶ Q}
    (hr : r ≫ r = 𝟙 P) (hs : s ≫ s = 𝟙 Q) (f : P ⟶ Q)
    (hf : f ≫ s = r ≫ f) (p q : ℕ)
    (a : SphereOddDegree.cohomologyZMod2 Q.fst p) (b : ordinary Q s hs q) :
    Hmap (pullHom hr hs f hf) (p + q) (ordinaryCup Q s hs p q a b) =
      ordinaryCup P r hr p q ((SphereOddDegree.cohPullback (TopPair.Hom.fst f) p).hom a)
        (Hmap (pullHom hr hs f hf) q b) := by
  apply (ordinaryEquiv P r hr (p + q)).injective
  rw [ordinaryEquiv_natural, ordinaryCup_native, ordinaryCup_native, ordinaryEquiv_natural]
  exact Finsler.RelativeCup.naturality f p q a (ordinaryEquiv Q s hs q b)

theorem ordinaryCup_add_left (p q : ℕ) (a a' : SphereOddDegree.cohomologyZMod2 P.fst p)
    (b : ordinary P r hr q) :
    ordinaryCup P r hr p q (a + a') b =
      ordinaryCup P r hr p q a b + ordinaryCup P r hr p q a' b := by
  unfold ordinaryCup
  rw [Finsler.RelativeCup.add_left, (ordinaryEquiv P r hr (p + q)).symm.map_add]

theorem ordinaryCup_smul_left (p q : ℕ) (c : ZMod 2)
    (a : SphereOddDegree.cohomologyZMod2 P.fst p) (b : ordinary P r hr q) :
    ordinaryCup P r hr p q (c • a) b = c • ordinaryCup P r hr p q a b := by
  unfold ordinaryCup
  rw [Finsler.RelativeCup.smul_left, (ordinaryEquiv P r hr (p + q)).symm.map_smul]

theorem ordinaryCup_add_right (p q : ℕ) (a : SphereOddDegree.cohomologyZMod2 P.fst p)
    (b b' : ordinary P r hr q) :
    ordinaryCup P r hr p q a (b + b') =
      ordinaryCup P r hr p q a b + ordinaryCup P r hr p q a b' := by
  unfold ordinaryCup
  rw [(ordinaryEquiv P r hr q).map_add, Finsler.RelativeCup.add_right,
    (ordinaryEquiv P r hr (p + q)).symm.map_add]

theorem ordinaryCup_smul_right (p q : ℕ) (c : ZMod 2)
    (a : SphereOddDegree.cohomologyZMod2 P.fst p) (b : ordinary P r hr q) :
    ordinaryCup P r hr p q a (c • b) = c • ordinaryCup P r hr p q a b := by
  unfold ordinaryCup
  rw [(ordinaryEquiv P r hr q).map_smul, Finsler.RelativeCup.smul_right,
    (ordinaryEquiv P r hr (p + q)).symm.map_smul]

/-- Degree transport on the ordinary quotient. -/
def ordinaryCast {m n : ℕ} (h : m = n) (x : ordinary P r hr m) : ordinary P r hr n := h ▸ x

theorem ordinaryEquiv_cast {m n : ℕ} (h : m = n) (x : ordinary P r hr m) :
    ordinaryEquiv P r hr n (ordinaryCast P r hr h x) =
      Finsler.CupBoundary.castClass P h (ordinaryEquiv P r hr m x) := by
  subst n
  rfl

theorem ordinaryCup_one_left (q : ℕ) (b : ordinary P r hr q) :
    ordinaryCast P r hr (Nat.zero_add q)
      (ordinaryCup P r hr 0 q (SphereOddDegree.oneZMod2 P.fst) b) = b := by
  apply (ordinaryEquiv P r hr q).injective
  rw [ordinaryEquiv_cast, ordinaryCup_native]
  exact Finsler.CupUnit.relative_one_left P q (ordinaryEquiv P r hr q b)

theorem ordinaryCup_assoc (p q k : ℕ)
    (a : SphereOddDegree.cohomologyZMod2 P.fst p)
    (a' : SphereOddDegree.cohomologyZMod2 P.fst q) (b : ordinary P r hr k) :
    ordinaryCast P r hr (Nat.add_assoc p q k)
      (ordinaryCup P r hr (p + q) k (SphereOddDegree.cupZMod2 a a') b) =
      ordinaryCup P r hr p (q + k) a (ordinaryCup P r hr q k a' b) := by
  apply (ordinaryEquiv P r hr (p + (q + k))).injective
  rw [ordinaryEquiv_cast, ordinaryCup_native, ordinaryCup_native, ordinaryCup_native]
  exact Finsler.CupAssociativity.relative_assoc P p q k a a' (ordinaryEquiv P r hr k b)

end
end Finsler.BorelComparison
