module
public import Finsler.Topology.BorelTwistedCup
/-! Actual target singular cohomology acts on the absolute reflection Borel quotient along a strictly invariant map. Pulled-back primitives give a support-preserving total homotopy, so target boundaries act by zero; actual homology cokernel descent proves representative independence. The action has unit, graded associativity, w-compatibility, forgetting to ordinary cup and equivariant pullback naturality. It multiplies lifted target classes, and commutes with the actual relative-to-ambient map. On all full/cut sphere-loop spaces the canonical action recovers the v0.74 e element when applied to the lifted unit, is square-zero, annihilates canonical e itself and agrees with the old relative action under the ambient map. This proves the required evaluation sector comparison, without claiming a product of arbitrary absolute Borel classes, K/O(2) extension, localization or geometric Borel comparison. -/

@[expose] public section
namespace Finsler.BorelAbsoluteCup
open CategoryTheory SphereOddDegree Finsler.BorelCochain
noncomputable section
section Generic
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X)

def cup (p : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (hi : cochainPullback r p α=α) (q : ℕ) :
    HR (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2] HR (BorelAbsolute.ofSpace X r hr) (p+q) :=
  BorelGraded.onHR (BorelTwistedCup.gradedCup r hr p α hα hi) q

def cupFamily (m : ℕ) (η : singularCochainGroup (ZMod 2) X m)
    (hi : cochainPullback r m η=η) :
    BorelHomotopy.Family (BorelAbsolute.ofSpace X r hr) (BorelAbsolute.ofSpace X r hr) m where
  f j := {
    toFun := SphereOddDegree.cochainCup m j η
    map_add' := cochainCup_add_right m j η
    map_smul' := fun a ψ => cochainCup_smul_right m j a η ψ }
  comm_t j x := by
    change cochainPullback r (m+j) (SphereOddDegree.cochainCup m j η x)=
      SphereOddDegree.cochainCup m j η (cochainPullback r j x)
    rw [cochainCup_naturality,hi]

theorem pull_invariant {Y : TopCat.{0}} (f : X ⟶ Y) (hf : r≫f=f) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) Y p) : cochainPullback r p (cochainPullback f p α)=cochainPullback f p α := by
  rw [Finsler.BorelEvaluation.cochain_comp,hf]

theorem invariantCup_congr (p : ℕ) {α β : singularCochainGroup (ZMod 2) X p}
    (he : α=β) (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hβ : cochainCoboundary (ZMod 2) X p β=0)
    (hi : cochainPullback (r) p α=α)
    (hj : cochainPullback (r) p β=β) (q : ℕ) :
    cup r hr p α hα hi q = cup r hr p β hβ hj q := by
  subst β
  rfl

theorem invariant_boundary_zero (m : ℕ) (η : singularCochainGroup (ZMod 2) X m)
    (hi : cochainPullback (r) m η=η)
    (hα : cochainCoboundary (ZMod 2) X (m+1) (cochainCoboundary (ZMod 2) X m η)=0)
    (hj : cochainPullback (r) (m+1) (cochainCoboundary (ZMod 2) X m η)=
      cochainCoboundary (ZMod 2) X m η)
    (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    cup r hr (m+1) (cochainCoboundary (ZMod 2) X m η) hα hj q x=0 := by
  apply BorelHomotopy.onHR_zero (cupFamily r hr m η hi)
  intro j y
  change cochainCoboundary (ZMod 2) X (m+j) (SphereOddDegree.cochainCup m j η y) = _
  have h := cochainCupZMod2_differential m j η y
  rw [BorelTwistedCup.cast_absolute r hr, BorelTwistedCup.cast_absolute r hr] at h
  exact h

variable {Y : TopCat.{0}} (f : X ⟶ Y) (hf : r≫f=f)

def cochainCup (p : ℕ) (α : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0) (q : ℕ) :
    HR (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2] HR (BorelAbsolute.ofSpace X r hr) (p+q) :=
  cup r hr p (cochainPullback f p α) (cochainPullback_cocycle f p α hα)
    (pull_invariant r f hf p α) q

theorem cochainCup_congr (p : ℕ) {α β : singularCochainGroup (ZMod 2) Y p}
    (heq : α=β) (hα : cochainCoboundary (ZMod 2) Y p α=0)
    (hβ : cochainCoboundary (ZMod 2) Y p β=0) (q : ℕ) :
    cochainCup r hr f hf p α hα q = cochainCup r hr f hf p β hβ q := by
  subst β
  rfl

theorem cochainCup_boundary_zero (i p : ℕ) (η : (cochainCxZMod2 Y).X i)
    (hα : cochainCoboundary (ZMod 2) Y p (((cochainCxZMod2 Y).d i p).hom η)=0)
    (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    cochainCup r hr f hf p (((cochainCxZMod2 Y).d i p).hom η) hα q x=0 := by
  by_cases h : (ComplexShape.up ℕ).Rel i p
  · obtain rfl : i+1=p := h
    have he : cochainPullback f (i+1) (((cochainCxZMod2 Y).d i (i+1)).hom η) =
        cochainCoboundary (ZMod 2) X i (cochainPullback f i η) :=
      (cochainPullback_cochainCoboundary f i η).symm
    have hc := cochainPullback_cocycle f (i+1) _ hα
    have hi := pull_invariant r f hf (i+1) (((cochainCxZMod2 Y).d i (i+1)).hom η)
    have hb : cochainCoboundary (ZMod 2) X (i+1)
        (cochainCoboundary (ZMod 2) X i (cochainPullback f i η))=0 := by
      rw [← he]
      exact hc
    have hj : cochainPullback (r) (i+1)
        (cochainCoboundary (ZMod 2) X i (cochainPullback f i η))=
        cochainCoboundary (ZMod 2) X i (cochainPullback f i η) := by
      rw [← he]
      exact hi
    calc
      _ = cup r hr (i+1) (cochainCoboundary (ZMod 2) X i
          (cochainPullback f i η)) hb hj q x :=
        congrArg (fun A => A x) (invariantCup_congr r hr (i+1) he hc hb hi hj q)
      _ = 0 := invariant_boundary_zero r hr i (cochainPullback f i η)
        (pull_invariant r f hf i η) hb hj q x
  · have hz : ((cochainCxZMod2 Y).d i p).hom η=0 := by
      rw [(cochainCxZMod2 Y).shape i p h, ModuleCat.hom_zero, LinearMap.zero_apply]
    -- The zero cup is immediate from its component formula.
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    unfold cochainCup cup
    rw [BorelGraded.onHR_mk, Submodule.Quotient.mk_eq_zero]
    have ht : BorelGraded.total (BorelTwistedCup.gradedCup r hr p (cochainPullback f p
        (((cochainCxZMod2 Y).d i p).hom η))
        (cochainPullback_cocycle f p _ hα)
        (pull_invariant r f hf p (((cochainCxZMod2 Y).d i p).hom η))) (c : Seq (BorelAbsolute.ofSpace X r hr))=0 := by
      funext j
      by_cases hp : p≤j
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
        rw [BorelGraded.total_at]
        change SphereOddDegree.cochainCup p k (cochainPullback f p
          (((cochainCxZMod2 Y).d i p).hom η)) (c.val k)=0
        rw [hz]
        have h0 : cochainPullback f p 0=0 := map_zero ((singularCochainComplexZMod2.map f.op).f p).hom
        rw [h0, cochainCup_zero_left]
      · exact BorelGraded.total_below _ _ (by omega)
    change (BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val) ∈ bcoboundaries (BorelAbsolute.ofSpace X r hr) (p+q)
    rw [ht]
    exact Submodule.zero_mem _

theorem cochainCup_add (p : ℕ) (α β : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0)
    (hβ : cochainCoboundary (ZMod 2) Y p β=0)
    (hs : cochainCoboundary (ZMod 2) Y p (α+β)=0) (q : ℕ) :
    cochainCup r hr f hf p (α+β) hs q =
      cochainCup r hr f hf p α hα q + cochainCup r hr f hf p β hβ q := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cochainCup, cup, LinearMap.add_apply, BorelGraded.onHR_mk]
  rw [← Submodule.Quotient.mk_add]
  congr 1
  apply Subtype.ext
  funext j
  by_cases hp : p≤j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    change BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val (p+k) = BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val (p+k) + BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val (p+k)
    rw [BorelGraded.total_at, BorelGraded.total_at, BorelGraded.total_at]
    change SphereOddDegree.cochainCup p k (cochainPullback f p (α+β)) (c.val k) =
      SphereOddDegree.cochainCup p k (cochainPullback f p α) (c.val k) +
      SphereOddDegree.cochainCup p k (cochainPullback f p β) (c.val k)
    have he : cochainPullback f p (α+β)=cochainPullback f p α+cochainPullback f p β :=
      map_add ((singularCochainComplexZMod2.map f.op).f p).hom α β
    rw [he, cochainCup_add_left]
  · change BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val j = BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val j + BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val j
    rw [BorelGraded.total_below _ _ (by omega), BorelGraded.total_below _ _ (by omega), BorelGraded.total_below _ _ (by omega), add_zero]

theorem cochainCup_smul (p : ℕ) (a : ZMod 2) (α : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0)
    (hs : cochainCoboundary (ZMod 2) Y p (a • α)=0) (q : ℕ) :
    cochainCup r hr f hf p (a • α) hs q = a • cochainCup r hr f hf p α hα q := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cochainCup, cup, LinearMap.smul_apply, BorelGraded.onHR_mk]
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  funext j
  by_cases hp : p≤j
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    change BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val (p+k) = a • BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val (p+k)
    rw [BorelGraded.total_at, BorelGraded.total_at]
    change SphereOddDegree.cochainCup p k (cochainPullback f p (a • α)) (c.val k) =
      a • SphereOddDegree.cochainCup p k (cochainPullback f p α) (c.val k)
    have he : cochainPullback f p (a • α)=a • cochainPullback f p α :=
      map_smul ((singularCochainComplexZMod2.map f.op).f p).hom a α
    rw [he, cochainCup_smul_left]
  · change BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val j = a • BorelGraded.total (K := BorelAbsolute.ofSpace X r hr) (L := BorelAbsolute.ofSpace X r hr) (p := p) _ c.val j
    rw [BorelGraded.total_below _ _ (by omega), BorelGraded.total_below _ _ (by omega), smul_zero]

/-- A linear action of actual target cocycles, valued in linear operators on absolute Borel cohomology. -/
def cycleAction (p q : ℕ) : (cochainCxZMod2 Y).cycles p ⟶
    ModuleCat.of (ZMod 2) (HR (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2] HR (BorelAbsolute.ofSpace X r hr) (p+q)) :=
  ModuleCat.ofHom {
    toFun c := cochainCup r hr f hf p (((cochainCxZMod2 Y).iCycles p).hom c)
      (CochainClass.closed_iCycles (cochainCxZMod2 Y) p c) q
    map_add' c d := by
      simp only [map_add]
      exact cochainCup_add r hr f hf p _ _ _ _ _ q
    map_smul' a c := by
      simp only [map_smul]
      exact cochainCup_smul r hr f hf p a _ _ _ q }

theorem cycleAction_boundary (p q : ℕ) :
    (cochainCxZMod2 Y).toCycles ((ComplexShape.up ℕ).prev p) p ≫ cycleAction r hr f hf p q=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro η
  apply LinearMap.ext
  intro x
  change cochainCup r hr f hf p
      (((cochainCxZMod2 Y).iCycles p).hom (((cochainCxZMod2 Y).toCycles ((ComplexShape.up ℕ).prev p) p).hom η))
      (CochainClass.closed_iCycles _ _ _) q x=0
  have he := ConcreteCategory.congr_hom
    ((cochainCxZMod2 Y).toCycles_i ((ComplexShape.up ℕ).prev p) p) η
  have hc := CochainClass.closed_boundary (cochainCxZMod2 Y) ((ComplexShape.up ℕ).prev p) p η
  exact (congrArg (fun A => A x) (cochainCup_congr r hr f hf p he _ hc q)).trans
    (cochainCup_boundary_zero r hr f hf ((ComplexShape.up ℕ).prev p) p η hc q x)

/-- Representative-independent action of actual target cohomology classes. -/
def classAction (p q : ℕ) : cohomologyZMod2 Y p ⟶
    ModuleCat.of (ZMod 2) (HR (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2] HR (BorelAbsolute.ofSpace X r hr) (p+q)) :=
  CochainClass.descend (cochainCxZMod2 Y) p (cycleAction r hr f hf p q)
    (cycleAction_boundary r hr f hf p q)

theorem classAction_mk (p : ℕ) (α : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0) (q : ℕ) :
    (classAction r hr f hf p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα)=
      cochainCup r hr f hf p α hα q := by
  rw [classAction, CochainClass.descend_classOf]
  change cochainCup r hr f hf p (((cochainCxZMod2 Y).iCycles p).hom
    ((cochainCxZMod2 Y).cyclesMk α (p+1) (CochainClass.next_eq p) hα))
    (CochainClass.closed_iCycles _ _ _) q = _
  exact cochainCup_congr r hr f hf p ((cochainCxZMod2 Y).i_cyclesMk _ _ _ _) _ hα q

theorem cochainCup_class_congr (p : ℕ) (α β : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0) (hβ : cochainCoboundary (ZMod 2) Y p β=0)
    (he : CochainClass.classOf (cochainCxZMod2 Y) p α hα = CochainClass.classOf (cochainCxZMod2 Y) p β hβ)
    (q : ℕ) : cochainCup r hr f hf p α hα q = cochainCup r hr f hf p β hβ q := by
  rw [← classAction_mk r hr f hf p α hα q, ← classAction_mk r hr f hf p β hβ q, he]
theorem pullback_one : cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := Y))=
    cochainOne (R := ZMod 2) (Z := X) := by
  apply cochain_ext
  intro σ
  rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]

theorem total_one (c : Seq (BorelAbsolute.ofSpace X r hr)) :
    BorelGraded.total (BorelTwistedCup.gradedCup r hr 0
      (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := Y)))
      (cochainPullback_cocycle f 0 _ (cochainCoboundary_cochainOne Y))
      (pull_invariant r f hf 0 _)) c=c := by
  let A := BorelTwistedCup.gradedCup r hr 0
    (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := Y)))
    (cochainPullback_cocycle f 0 _ (cochainCoboundary_cochainOne Y))
    (pull_invariant r f hf 0 _)
  change BorelGraded.total A c=c
  funext j
  calc
    _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j) (BorelGraded.total A c (0+j)) :=
      BorelGraded.cast_seq (Nat.zero_add j) _
    _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j) (A.f j (c j)) :=
      congrArg (BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j)) (BorelGraded.total_at A c j)
    _ = c j := by
      change BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j)
        (SphereOddDegree.cochainCup 0 j (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := Y))) (c j))=c j
      rw [← BorelTwistedCup.cast_absolute r hr, pullback_one]
      rw [CupUnit.cochain_one_left,cochainCast_cast]

theorem classAction_one (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelGraded.castHR (Nat.zero_add q)
      ((classAction r hr f hf 0 q).hom (oneZMod2 Y) x)=x := by
  change BorelGraded.castHR (Nat.zero_add q)
    ((classAction r hr f hf 0 q).hom
      (CochainClass.classOf (cochainCxZMod2 Y) 0 (cochainOne (R := ZMod 2) (Z := Y))
        (cochainCoboundary_cochainOne Y)) x)=x
  rw [classAction_mk]
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let A := BorelTwistedCup.gradedCup r hr 0
    (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := Y)))
    (cochainPullback_cocycle f 0 _ (cochainCoboundary_cochainOne Y))
    (pull_invariant r f hf 0 _)
  have ht : BorelGraded.total A c.val=c.val := total_one r hr f hf c.val
  have hc : BorelGraded.total A c.val ∈ bcocycles (BorelAbsolute.ofSpace X r hr) q := by
    rw [ht]
    exact c.2
  change BorelGraded.castHR (Nat.zero_add q) (Submodule.Quotient.mk (BorelGraded.cyclesMap A q c))=
    Submodule.Quotient.mk c
  calc
    _ = Submodule.Quotient.mk (⟨BorelGraded.total A c.val,hc⟩ : bcocycles (BorelAbsolute.ofSpace X r hr) q) :=
      BorelGraded.castHR_mk _ _ _ _
    _ = Submodule.Quotient.mk c := congrArg Submodule.Quotient.mk (Subtype.ext ht)

def graded (p : ℕ) (α : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0) : BorelGraded.Map (BorelAbsolute.ofSpace X r hr) (BorelAbsolute.ofSpace X r hr) p :=
  BorelTwistedCup.gradedCup r hr p (cochainPullback f p α) (cochainPullback_cocycle f p α hα)
    (pull_invariant r f hf p α)

theorem castC_injective (K : InvComplex) {a b : ℕ} (h : a=b) :
    Function.Injective (BorelGraded.castC K h) := by
  subst b
  exact fun _ _ h => h

theorem total_comp (p s : ℕ) (α : singularCochainGroup (ZMod 2) Y p)
    (β : singularCochainGroup (ZMod 2) Y s)
    (hα : cochainCoboundary (ZMod 2) Y p α=0)
    (hβ : cochainCoboundary (ZMod 2) Y s β=0) (c : Seq (BorelAbsolute.ofSpace X r hr)) :
    BorelGraded.total (graded r hr f hf (p+s) (SphereOddDegree.cochainCup p s α β)
      (cochainCupZMod2_respects_cocycles p s α β hα hβ)) c =
    BorelGraded.total (graded r hr f hf p α hα)
      (BorelGraded.total (graded r hr f hf s β hβ) c) := by
  let A := graded r hr f hf p α hα
  let B := graded r hr f hf s β hβ
  let C := graded r hr f hf (p+s) (SphereOddDegree.cochainCup p s α β)
    (cochainCupZMod2_respects_cocycles p s α β hα hβ)
  change BorelGraded.total C c = BorelGraded.total A (BorelGraded.total B c)
  funext j
  by_cases hj : p+s≤j
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
    apply castC_injective (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)
    have he : BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k) (C.f k (c k)) =
        A.f (s+k) (B.f k (c k)) := by
      change BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)
        (SphereOddDegree.cochainCup (p+s) k (cochainPullback f (p+s) (SphereOddDegree.cochainCup p s α β)) (c k)) =
        SphereOddDegree.cochainCup p (s+k) (cochainPullback f p α)
          (SphereOddDegree.cochainCup s k (cochainPullback f s β) (c k))
      rw [← BorelTwistedCup.cast_absolute r hr, cochainCup_naturality]
      exact CupAssociativity.cochain_assoc X p s k _ _ _
    calc
      _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k) (C.f k (c k)) :=
        congrArg (BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)) (BorelGraded.total_at C c k)
      _ = A.f (s+k) (B.f k (c k)) := he
      _ = BorelGraded.total A (BorelGraded.total B c) (p+(s+k)) := by
        rw [BorelGraded.total_at, BorelGraded.total_at]
      _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.add_assoc p s k)
          (BorelGraded.total A (BorelGraded.total B c) ((p+s)+k)) :=
        BorelGraded.cast_seq (Nat.add_assoc p s k) _
  · rw [BorelGraded.total_below C c (by omega)]
    by_cases hp : p≤j
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
      rw [BorelGraded.total_at, BorelGraded.total_below B c (by omega), map_zero]
    · rw [BorelGraded.total_below A _ (by omega)]

theorem cochainCup_assoc (p s : ℕ) (α : singularCochainGroup (ZMod 2) Y p)
    (β : singularCochainGroup (ZMod 2) Y s)
    (hα : cochainCoboundary (ZMod 2) Y p α=0)
    (hβ : cochainCoboundary (ZMod 2) Y s β=0) (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelGraded.castHR (Nat.add_assoc p s q)
      (cochainCup r hr f hf (p+s) (SphereOddDegree.cochainCup p s α β)
        (cochainCupZMod2_respects_cocycles p s α β hα hβ) q x) =
    cochainCup r hr f hf p α hα (s+q)
      (cochainCup r hr f hf s β hβ q x) := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let A := graded r hr f hf p α hα
  let B := graded r hr f hf s β hβ
  let C := graded r hr f hf (p+s) (SphereOddDegree.cochainCup p s α β)
    (cochainCupZMod2_respects_cocycles p s α β hα hβ)
  have ht : BorelGraded.total C c.val=BorelGraded.total A (BorelGraded.total B c.val) :=
    total_comp r hr f hf p s α β hα hβ c.val
  have hc : BorelGraded.total C c.val ∈ bcocycles (BorelAbsolute.ofSpace X r hr) (p+(s+q)) := by
    rw [ht]
    exact (BorelGraded.cyclesMap A (s+q) (BorelGraded.cyclesMap B q c)).2
  change BorelGraded.castHR (Nat.add_assoc p s q) (Submodule.Quotient.mk (BorelGraded.cyclesMap C q c))=
    Submodule.Quotient.mk (BorelGraded.cyclesMap A (s+q) (BorelGraded.cyclesMap B q c))
  calc
    _ = Submodule.Quotient.mk (⟨BorelGraded.total C c.val,hc⟩ : bcocycles (BorelAbsolute.ofSpace X r hr) (p+(s+q))) :=
      BorelGraded.castHR_mk _ _ _ _
    _ = _ := congrArg Submodule.Quotient.mk (Subtype.ext ht)

theorem classAction_assoc (p s : ℕ) (a : cohomologyZMod2 Y p) (b : cohomologyZMod2 Y s)
    (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelGraded.castHR (Nat.add_assoc p s q)
      ((classAction r hr f hf (p+s) q).hom (cupZMod2 a b) x)=
    (classAction r hr f hf p (s+q)).hom a
      ((classAction r hr f hf s q).hom b x) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p a
  obtain ⟨β,hβ,rfl⟩ := cocycleClass_surjective Y s b
  rw [cupZMod2_mk]
  change BorelGraded.castHR (Nat.add_assoc p s q)
    ((classAction r hr f hf (p+s) q).hom
      (CochainClass.classOf (cochainCxZMod2 Y) (p+s) (SphereOddDegree.cochainCup p s α β)
        (cochainCupZMod2_respects_cocycles p s α β hα hβ)) x)=
    (classAction r hr f hf p (s+q)).hom
      (CochainClass.classOf (cochainCxZMod2 Y) p α hα)
      ((classAction r hr f hf s q).hom
        (CochainClass.classOf (cochainCxZMod2 Y) s β hβ) x)
  rw [classAction_mk, classAction_mk, classAction_mk]
  exact cochainCup_assoc r hr f hf p s α β hα hβ q x



/-- The descended target action multiplies the actual lifted target classes. -/
theorem classAction_lift (p q : ℕ) (a : cohomologyZMod2 Y p) (b : cohomologyZMod2 Y q) :
    (classAction r hr f hf p q).hom a (BorelAbsolute.lift r hr f hf q b)=
      BorelAbsolute.lift r hr f hf (p+q) (cupZMod2 a b) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p a
  obtain ⟨β,hβ,rfl⟩ := cocycleClass_surjective Y q b
  rw [cupZMod2_mk]
  change (classAction r hr f hf p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα)
    (BorelAbsolute.lift r hr f hf q (CochainClass.classOf (cochainCxZMod2 Y) q β hβ))=
    BorelAbsolute.lift r hr f hf (p+q)
      (CochainClass.classOf (cochainCxZMod2 Y) (p+q) (SphereOddDegree.cochainCup p q α β)
        (cochainCupZMod2_respects_cocycles p q α β hα hβ))
  rw [classAction_mk,BorelAbsolute.lift_mk,BorelAbsolute.lift_mk]
  unfold cochainCup cup BorelAbsolute.singleClass
  rw [BorelGraded.onHR_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change BorelGraded.total (BorelTwistedCup.gradedCup r hr p (cochainPullback f p α) (cochainPullback_cocycle f p α hα) (pull_invariant r f hf p α)) (Pi.single q (cochainPullback f q β))=
    Pi.single (p+q) (cochainPullback f (p+q) (SphereOddDegree.cochainCup p q α β))
  rw [BorelGraded.total_single]
  change Pi.single (p+q) (SphereOddDegree.cochainCup p q (cochainPullback f p α) (cochainPullback f q β))=_
  exact congrArg (fun z => (Pi.single (p+q) z : Seq (BorelAbsolute.ofSpace X r hr)))
    (cochainCup_naturality f p q α β).symm

theorem classAction_w (p : ℕ) (a : cohomologyZMod2 Y p) (q : ℕ)
    (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelGraded.castHR (Nat.add_assoc p q 1).symm
      ((classAction r hr f hf p (q+1)).hom a (w _ q x))=
      w _ (p+q) ((classAction r hr f hf p q).hom a x) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p a
  change BorelGraded.castHR (Nat.add_assoc p q 1).symm
    ((classAction r hr f hf p (q+1)).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) (w _ q x))=
    w _ (p+q) ((classAction r hr f hf p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) x)
  rw [classAction_mk,classAction_mk]
  exact BorelGraded.onHR_w _ q x

end Generic

/-- The actual relative-to-ambient map of reflection total complexes. No injectivity on cohomology is assumed. -/
def toAbsolute (P : TopPair.{0}) (r : P ⟶ P) (hr : r≫r=𝟙 P) :
    InvHom (BorelPair.ofPair P r hr)
      (BorelAbsolute.ofSpace P.fst (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr)) where
  f j := RelativeCupCochain.toAmbient P j
  comm_d j x := RelativeCupCochain.toAmbient_differential P j x
  comm_t j x := RelativeCupCochain.toAmbient_pullback r j x

/-- The old relative action and the new absolute action commute with the actual ambient map. -/
theorem classAction_toAbsolute (P : TopPair.{0}) (r : P ⟶ P) (hr : r≫r=𝟙 P)
    {Y : TopCat.{0}} (f : P.fst ⟶ Y) (hf : TopPair.Hom.fst r≫f=f)
    (p : ℕ) (a : cohomologyZMod2 Y p) (q : ℕ) (x : HR (BorelPair.ofPair P r hr) q) :
    HRmap (toAbsolute P r hr) (p+q) ((BorelPullbackCup.classAction P r hr f hf p q).hom a x)=
      (classAction (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr) f hf p q).hom a
        (HRmap (toAbsolute P r hr) q x) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p a
  change HRmap (toAbsolute P r hr) (p+q)
    ((BorelPullbackCup.classAction P r hr f hf p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) x)=
    (classAction (TopPair.Hom.fst r) (BorelAbsolute.fst_sq P r hr) f hf p q).hom
      (CochainClass.classOf (cochainCxZMod2 Y) p α hα) (HRmap (toAbsolute P r hr) q x)
  rw [BorelPullbackCup.classAction_mk,classAction_mk]
  apply BorelGraded.onHR_natural
  intro j y
  exact RelativeCupCochain.toAmbient_cup P p j (cochainPullback f p α) y

open Finsler.BorelEvaluation Finsler.SphereTopClass

def fullE (n : ℕ) (hn : 1≤n) (q : ℕ) :
    HR (BorelAbsolute.fullComplex n) q →ₗ[ZMod 2] HR (BorelAbsolute.fullComplex n) (n+q) :=
  (classAction (TopPair.Hom.fst (BorelLoop.revFullPair n))
    (BorelAbsolute.fst_sq _ _ (BorelLoop.revFullPair_sq n)) (fullEval n) (fullEval_invariant n) n q).hom
      (topClass n hn)

def levE {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) (q : ℕ) :
    HR (BorelAbsolute.levComplex F a) q →ₗ[ZMod 2] HR (BorelAbsolute.levComplex F a) (n+q) :=
  (classAction (TopPair.Hom.fst (BorelLoop.revPair F a))
    (BorelAbsolute.fst_sq _ _ (BorelLoop.revPair_sq F a)) (levEval F a) (levEval_invariant F a) n q).hom
      (topClass n hn)

theorem fullE_square_zero (n : ℕ) (hn : 1≤n) (q : ℕ) (x : HR (BorelAbsolute.fullComplex n) q) :
    fullE n hn (n+q) (fullE n hn q x)=0 := by
  have h := classAction_assoc _ _ _ (fullEval_invariant n) n n (topClass n hn) (topClass n hn) q x
  rw [topClass_cup_self,map_zero,LinearMap.zero_apply,map_zero] at h
  exact h.symm

theorem levE_square_zero {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (BorelAbsolute.levComplex F a) q) : levE F a hn (n+q) (levE F a hn q x)=0 := by
  have h := classAction_assoc _ _ _ (levEval_invariant F a) n n (topClass n hn) (topClass n hn) q x
  rw [topClass_cup_self,map_zero,LinearMap.zero_apply,map_zero] at h
  exact h.symm

theorem fullE_top_zero (n : ℕ) (hn : 1≤n) : fullE n hn n (BorelAbsolute.fullTop n hn)=0 := by
  have h := classAction_lift (TopPair.Hom.fst (BorelLoop.revFullPair n)) (BorelAbsolute.fst_sq _ _ (BorelLoop.revFullPair_sq n)) (fullEval n) (fullEval_invariant n) n n (topClass n hn) (topClass n hn)
  rw [topClass_cup_self,map_zero] at h
  exact h

theorem levE_top_zero {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    levE F a hn n (BorelAbsolute.levTop F a hn)=0 := by
  have h := classAction_lift (TopPair.Hom.fst (BorelLoop.revPair F a)) (BorelAbsolute.fst_sq _ _ (BorelLoop.revPair_sq F a)) (levEval F a) (levEval_invariant F a) n n (topClass n hn) (topClass n hn)
  rw [topClass_cup_self,map_zero] at h
  exact h

theorem fullE_toAbsolute (n : ℕ) (hn : 1≤n) (q : ℕ) (x : HR (BorelLoop.fullComplex n) q) :
    HRmap (toAbsolute (BorelLoop.fullPair n) (BorelLoop.revFullPair n) (BorelLoop.revFullPair_sq n)) (n+q)
      (BorelCanonicalEvaluation.fullE n hn q x)=fullE n hn q
        (HRmap (toAbsolute (BorelLoop.fullPair n) (BorelLoop.revFullPair n) (BorelLoop.revFullPair_sq n)) q x) := by
  change HRmap _ _ (BorelEvaluation.fullClassCup n n (topClass n hn) q x)=_
  rw [BorelEvaluationClass.fullClassCup_eq_action]
  exact classAction_toAbsolute _ _ _ _ (fullEval_invariant n) n (topClass n hn) q x

theorem levE_toAbsolute {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (BorelLoop.levComplex F a) q) :
    HRmap (toAbsolute (BorelLoop.levPair F a) (BorelLoop.revPair F a) (BorelLoop.revPair_sq F a)) (n+q)
      (BorelCanonicalEvaluation.levE F a hn q x)=levE F a hn q
        (HRmap (toAbsolute (BorelLoop.levPair F a) (BorelLoop.revPair F a) (BorelLoop.revPair_sq F a)) q x) := by
  change HRmap _ _ (BorelEvaluation.levClassCup F a n (topClass n hn) q x)=_
  rw [BorelEvaluationClass.levClassCup_eq_action]
  exact classAction_toAbsolute _ _ _ _ (levEval_invariant F a) n (topClass n hn) q x


theorem classAction_natural {A B Y : TopCat.{0}} (rA : A ⟶ A) (rB : B ⟶ B)
    (hA : rA≫rA=𝟙 A) (hB : rB≫rB=𝟙 B) (f : A ⟶ B) (hf : f≫rB=rA≫f)
    (g : B ⟶ Y) (gA : A ⟶ Y) (hg : rB≫g=g) (hga : rA≫gA=gA) (he : f≫g=gA)
    (p : ℕ) (a : cohomologyZMod2 Y p) (q : ℕ) (x : HR (BorelAbsolute.ofSpace B rB hB) q) :
    HRmap (BorelAbsolute.pullHom rA rB hA hB f hf) (p+q) ((classAction rB hB g hg p q).hom a x)=
      (classAction rA hA gA hga p q).hom a (HRmap (BorelAbsolute.pullHom rA rB hA hB f hf) q x) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p a
  change HRmap _ _ ((classAction rB hB g hg p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) x)=
    (classAction rA hA gA hga p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) (HRmap _ q x)
  rw [classAction_mk,classAction_mk]
  apply BorelGraded.onHR_natural
  intro j y
  change singularCochainGroup (ZMod 2) B j at y
  change cochainPullback f (p+j) (SphereOddDegree.cochainCup p j (cochainPullback g p α) y)=
    SphereOddDegree.cochainCup p j (cochainPullback gA p α) (cochainPullback f j y)
  rw [cochainCup_naturality,Finsler.BorelEvaluation.cochain_comp,he]

theorem forgetNative_mk {X : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X) (q : ℕ)
    (c : bcocycles (BorelAbsolute.ofSpace X r hr) q) :
    BorelAbsolute.forgetNative X r hr q (Submodule.Quotient.mk c)=
      CochainClass.classOf (cochainCxZMod2 X) q (c.val q) (bcocycle_comp _ q c) := by
  change BorelAbsolute.ordinaryCycleClass X r hr q (forgetCocycle (BorelAbsolute.ofSpace X r hr) q c)=_
  exact BorelAbsolute.ordinaryCycleClass_apply X r hr q _

theorem classAction_forget {X Y : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X)
    (f : X ⟶ Y) (hf : r≫f=f) (p : ℕ) (a : cohomologyZMod2 Y p) (q : ℕ)
    (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelAbsolute.forgetNative X r hr (p+q) ((classAction r hr f hf p q).hom a x)=
      cupZMod2 ((cohPullback f p).hom a) (BorelAbsolute.forgetNative X r hr q x) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p a
  change BorelAbsolute.forgetNative X r hr (p+q)
    ((classAction r hr f hf p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) x)=
    cupZMod2 ((cohPullback f p).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα)) _
  rw [classAction_mk,←Finsler.BorelEvaluation.classOf_pull f p α hα]
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [forgetNative_mk]
  unfold cochainCup cup
  rw [BorelGraded.onHR_mk,forgetNative_mk]
  have ht := BorelGraded.total_at (BorelTwistedCup.gradedCup r hr p (cochainPullback f p α)
    (cochainPullback_cocycle f p α hα) (pull_invariant r f hf p α)) c.val q
  calc
    _ = CochainClass.classOf (cochainCxZMod2 X) (p+q)
        (SphereOddDegree.cochainCup p q (cochainPullback f p α) (c.val q))
        (cochainCupZMod2_respects_cocycles p q _ _ (cochainPullback_cocycle f p α hα) (bcocycle_comp _ q c)) :=
      CochainClass.classOf_congr _ _ ht _ _
    _ = _ := (cupZMod2_mk _ _ _ _).symm

theorem fullE_res {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (BorelAbsolute.fullComplex n) q) :
    HRmap (BorelAbsolute.fullRes F a) (n+q) (fullE n hn q x)=
      levE F a hn q (HRmap (BorelAbsolute.fullRes F a) q x) := by
  exact classAction_natural _ _ _ _ _ (congrArg TopPair.Hom.fst (BorelLoop.resPair_equivariant F a))
    _ _ (fullEval_invariant n) (levEval_invariant F a) (res_eval F a) n (topClass n hn) q x

theorem levE_cut {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b) (hn : 1≤n)
    (q : ℕ) (x : HR (BorelAbsolute.levComplex F b) q) :
    HRmap (BorelAbsolute.cutRes F hab) (n+q) (levE F b hn q x)=
      levE F a hn q (HRmap (BorelAbsolute.cutRes F hab) q x) := by
  exact classAction_natural _ _ _ _ _ (congrArg TopPair.Hom.fst (BorelLoop.cutPair_equivariant F hab))
    _ _ (levEval_invariant F b) (levEval_invariant F a) (cut_eval F hab) n (topClass n hn) q x


/-- Applying canonical e to the actual lifted unit recovers the v0.74 absolute e element. -/
theorem fullE_on_one (n : ℕ) (hn : 1≤n) :
    fullE n hn 0 (BorelAbsolute.lift (TopPair.Hom.fst (BorelLoop.revFullPair n))
      (BorelAbsolute.fst_sq _ _ (BorelLoop.revFullPair_sq n)) (fullEval n) (fullEval_invariant n) 0
      (oneZMod2 (sphere n)))=BorelAbsolute.fullTop n hn := by
  change (classAction _ _ _ _ n 0).hom (topClass n hn) (BorelAbsolute.lift _ _ _ _ 0 (oneZMod2 (sphere n)))=_
  rw [classAction_lift,CupUnit.absolute_one_right]
  rfl

theorem levE_on_one {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    levE F a hn 0 (BorelAbsolute.lift (TopPair.Hom.fst (BorelLoop.revPair F a))
      (BorelAbsolute.fst_sq _ _ (BorelLoop.revPair_sq F a)) (levEval F a) (levEval_invariant F a) 0
      (oneZMod2 (sphere n)))=BorelAbsolute.levTop F a hn := by
  change (classAction _ _ _ _ n 0).hom (topClass n hn) (BorelAbsolute.lift _ _ _ _ 0 (oneZMod2 (sphere n)))=_
  rw [classAction_lift,CupUnit.absolute_one_right]
  rfl

end
end Finsler.BorelAbsoluteCup
