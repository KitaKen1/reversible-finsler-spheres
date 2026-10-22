module
public import Finsler.Topology.SpherePuncturedEvaluation
/-! Absolute reflection Borel cohomology from the actual singular cochains. A strictly invariant map lifts actual target cohomology through the actual homology cokernel; pulled-back primitives give Borel boundaries, including degree zero. The native forgetting map recovers ordinary singular-cohomology pullback. On the actual full/cut sphere-loop ambient spaces this constructs nonzero canonical reflection e elements, naturally under every inclusion. Target composition and punctured-sphere factorization give vanishing of the lifted element itself under point avoidance. The relative evaluation action is in BorelCanonicalEvaluation; geometric Borel comparison, a full absolute Borel cup ring, K/O(2) extension and localization remain separate. -/

@[expose] public section
namespace Finsler.BorelAbsolute
open CategoryTheory SphereOddDegree Finsler.BorelCochain
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual absolute singular cochains with the involution induced by r. -/
def ofSpace (X : TopCat.{0}) (r : X ⟶ X) (hr : r≫r=𝟙 X) : InvComplex where
  C j := singularCochainGroup (ZMod 2) X j
  d j := ((cochainCxZMod2 X).d j (j+1)).hom
  t j := ((singularCochainComplexZMod2.map r.op).f j).hom
  dd j α := by
    have h := (cochainCxZMod2 X).d_comp_d j (j+1) (j+1+1)
    exact congrArg (fun φ => φ.hom α) h
  tt j α := by
    have h := Finsler.BorelEvaluation.cochain_comp r r j α
    rw [hr] at h
    have hi := singularCochainComplexZMod2.map_id (Opposite.op X)
    have hi' := congrArg (fun φ => (φ.f j).hom α) hi
    exact h.trans hi'
  td j α := (cochainPullback_cochainCoboundary r j α).symm

def singleCycles (X : TopCat.{0}) (r : X ⟶ X) (hr : r≫r=𝟙 X) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hi : cochainPullback r p α=α) : bcocycles (ofSpace X r hr) p := by
  refine ⟨Pi.single p α,single_mem_low _ _ _,?_⟩
  change D (ofSpace X r hr) (Pi.single p α)=0
  rw [D_single]
  have ht : tr (ofSpace X r hr) p α=0 := by
    change α+cochainPullback r p α=0
    rw [hi]
    exact two_eq_zero_of_mod _
  have hd : (ofSpace X r hr).d p α=0 := hα
  rw [ht,hd,single_zero_seq,single_zero_seq,zero_add]

def singleClass (X : TopCat.{0}) (r : X ⟶ X) (hr : r≫r=𝟙 X) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hi : cochainPullback r p α=α) : HR (ofSpace X r hr) p :=
  Submodule.Quotient.mk (singleCycles X r hr p α hα hi)


/-- Nonzero ordinary image obstructs a Borel boundary of a strictly invariant single cocycle. -/
theorem singleClass_ne_zero (X : TopCat.{0}) (r : X ⟶ X) (hr : r≫r=𝟙 X) (m : ℕ)
    (α : singularCochainGroup (ZMod 2) X (m+1))
    (hα : cochainCoboundary (ZMod 2) X (m+1) α=0)
    (hi : cochainPullback r (m+1) α=α)
    (hn : CochainClass.classOf (cochainCxZMod2 X) (m+1) α hα≠0) :
    singleClass X r hr (m+1) α hα hi≠0 := by
  intro hz
  unfold singleClass at hz
  rw [Submodule.Quotient.mk_eq_zero] at hz
  have hb : (Pi.single (m+1) α : Seq (ofSpace X r hr)) ∈ bcoboundaries (ofSpace X r hr) (m+1) :=
    hz
  obtain ⟨b,hb,heq⟩ := hb
  have hc : b (m+1)=0 := hb (m+1) le_rfl
  have he := congrArg (fun c => c (m+1)) heq
  rw [D_succ,hc,map_zero,add_zero] at he
  have he' : (ofSpace X r hr).d m (b m)=α := he.trans (single_same (ofSpace X r hr) (m+1) α)
  apply hn
  have hclosed := CochainClass.closed_boundary (cochainCxZMod2 X) m (m+1) (b m)
  calc
    _ = CochainClass.classOf (cochainCxZMod2 X) (m+1)
        (((cochainCxZMod2 X).d m (m+1)).hom (b m)) hclosed :=
      CochainClass.classOf_congr _ _ he'.symm _ _
    _ = 0 := CochainClass.classOf_boundary _ _ _ _ _


variable {X Y : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X) (f : X ⟶ Y) (hf : r≫f=f)

def pullSingleCycles (p : ℕ) : (cochainCxZMod2 Y).cycles p →ₗ[ZMod 2] bcocycles (ofSpace X r hr) p :=
  LinearMap.codRestrict (bcocycles (ofSpace X r hr) p)
    (LinearMap.single (ZMod 2) (ofSpace X r hr).C p ∘ₗ ((singularCochainComplexZMod2.map f.op).f p).hom
      ∘ₗ ((cochainCxZMod2 Y).iCycles p).hom) (fun c =>
        (singleCycles X r hr p (cochainPullback f p (((cochainCxZMod2 Y).iCycles p).hom c))
          (cochainPullback_cocycle f p _ (CochainClass.closed_iCycles _ _ c)) (by
            rw [Finsler.BorelEvaluation.cochain_comp, hf])).2)

def nativeCycles (p : ℕ) : (cochainCxZMod2 Y).cycles p ⟶ ModuleCat.of (ZMod 2) (HR (ofSpace X r hr) p) :=
  ModuleCat.ofHom ((Submodule.mkQ _).comp (pullSingleCycles r hr f hf p))

include hf in
theorem single_pull_boundary (i p : ℕ) (η : (cochainCxZMod2 Y).X i) :
    (Pi.single p (cochainPullback f p (((cochainCxZMod2 Y).d i p).hom η)) : Seq (ofSpace X r hr)) ∈
      bcoboundaries (ofSpace X r hr) p := by
  by_cases hip : i+1=p
  · subst p
    refine ⟨Pi.single i (cochainPullback f i η),single_mem_low _ _ _,?_⟩
    rw [D_single]
    have ht : tr (ofSpace X r hr) i (cochainPullback f i η)=0 := by
      change cochainPullback f i η+cochainPullback r i (cochainPullback f i η)=0
      rw [Finsler.BorelEvaluation.cochain_comp,hf]
      exact two_eq_zero_of_mod _
    rw [ht,single_zero_seq,zero_add]
    have hd : (ofSpace X r hr).d i (cochainPullback f i η)=
        cochainPullback f (i+1) (((cochainCxZMod2 Y).d i (i+1)).hom η) := cochainPullback_cochainCoboundary f i η
    exact congrArg (fun z => (Pi.single (i+1) z : Seq (ofSpace X r hr))) hd
  · have hd : (cochainCxZMod2 Y).d i p=0 := (cochainCxZMod2 Y).shape i p hip
    rw [hd,ModuleCat.hom_zero,LinearMap.zero_apply]
    have hz : cochainPullback f p 0=0 := map_zero ((singularCochainComplexZMod2.map f.op).f p).hom
    rw [hz]
    have he : (Pi.single p (0 : (ofSpace X r hr).C p) : Seq (ofSpace X r hr))=0 := single_zero_seq _ _
    rw [he]
    exact Submodule.zero_mem _


theorem nativeCycles_boundary (p : ℕ) : (cochainCxZMod2 Y).toCycles ((ComplexShape.up ℕ).prev p) p ≫
    nativeCycles r hr f hf p=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro η
  let i := (ComplexShape.up ℕ).prev p
  change Submodule.Quotient.mk ((pullSingleCycles r hr f hf p) (((cochainCxZMod2 Y).toCycles i p).hom η))=0
  rw [Submodule.Quotient.mk_eq_zero]
  change (Pi.single p (cochainPullback f p
    (((cochainCxZMod2 Y).iCycles p).hom (((cochainCxZMod2 Y).toCycles i p).hom η))) : Seq (ofSpace X r hr)) ∈ bcoboundaries (ofSpace X r hr) p
  have hto : ((cochainCxZMod2 Y).iCycles p).hom (((cochainCxZMod2 Y).toCycles i p).hom η)=
      ((cochainCxZMod2 Y).d i p).hom η := ConcreteCategory.congr_hom ((cochainCxZMod2 Y).toCycles_i i p) η
  rw [hto]
  exact single_pull_boundary r hr f hf i p η

/-- A strictly invariant target map lifts its actual target cohomology classes to absolute reflection Borel classes. -/
def lift (p : ℕ) : cohomologyZMod2 Y p →ₗ[ZMod 2] HR (ofSpace X r hr) p :=
  (CochainClass.descend (cochainCxZMod2 Y) p (nativeCycles r hr f hf p) (nativeCycles_boundary r hr f hf p)).hom

theorem lift_mk (p : ℕ) (α : singularCochainGroup (ZMod 2) Y p)
    (hα : cochainCoboundary (ZMod 2) Y p α=0) :
    lift r hr f hf p (CochainClass.classOf (cochainCxZMod2 Y) p α hα)=
      singleClass X r hr p (cochainPullback f p α) (cochainPullback_cocycle f p α hα) (by
        rw [Finsler.BorelEvaluation.cochain_comp,hf]) := by
  rw [lift,CochainClass.descend_classOf]
  change Submodule.Quotient.mk ((pullSingleCycles r hr f hf p)
      ((cochainCxZMod2 Y).cyclesMk α (p+1) (CochainClass.next_eq p) hα))=singleClass X r hr p _ _ _
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change (Pi.single p (cochainPullback f p (((cochainCxZMod2 Y).iCycles p).hom
    ((cochainCxZMod2 Y).cyclesMk α (p+1) (CochainClass.next_eq p) hα))) : Seq (ofSpace X r hr))=Pi.single p (cochainPullback f p α)
  have he : ((cochainCxZMod2 Y).iCycles p).hom
      ((cochainCxZMod2 Y).cyclesMk α (p+1) (CochainClass.next_eq p) hα)=α :=
    (cochainCxZMod2 Y).i_cyclesMk _ _ _ _
  exact congrArg (fun z => (Pi.single p (cochainPullback f p z) : Seq (ofSpace X r hr))) he


theorem singleClass_ne_zero_pos (X : TopCat.{0}) (r : X ⟶ X) (hr : r≫r=𝟙 X) (p : ℕ) (hp : 1≤p)
    (α : singularCochainGroup (ZMod 2) X p) (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hi : cochainPullback r p α=α)
    (hn : CochainClass.classOf (cochainCxZMod2 X) p α hα≠0) : singleClass X r hr p α hα hi≠0 := by
  cases p with
  | zero => omega
  | succ m => exact singleClass_ne_zero X r hr m α hα hi hn

theorem lift_ne_zero_of_pull_ne_zero (p : ℕ) (hp : 1≤p) (s : cohomologyZMod2 Y p)
    (hs : (cohPullback f p).hom s≠0) : lift r hr f hf p s≠0 := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p s
  change lift r hr f hf p (CochainClass.classOf (cochainCxZMod2 Y) p α hα)≠0
  rw [lift_mk]
  apply singleClass_ne_zero_pos _ _ _ _ hp
  rw [Finsler.BorelEvaluation.classOf_pull]
  exact hs


variable (X : TopCat.{0}) (r : X ⟶ X) (hr : r≫r=𝟙 X)

def cycleIncl (p : ℕ) : ModuleCat.of (ZMod 2) (cocycles (ofSpace X r hr) p) ⟶ (cochainCxZMod2 X).X p :=
  ModuleCat.ofHom (cocycles (ofSpace X r hr) p).subtype

theorem cycleIncl_closed (p : ℕ) : cycleIncl X r hr p ≫ (cochainCxZMod2 X).d p (p+1)=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact c.2

def ordinaryCycleClass (p : ℕ) : cocycles (ofSpace X r hr) p →ₗ[ZMod 2] cohomologyZMod2 X p :=
  ((cochainCxZMod2 X).liftCycles (cycleIncl X r hr p) (p+1) (CochainClass.next_eq p) (cycleIncl_closed X r hr p)
    ≫ (cochainCxZMod2 X).homologyπ p).hom

theorem ordinaryCycleClass_apply (p : ℕ) (c : cocycles (ofSpace X r hr) p) :
    ordinaryCycleClass X r hr p c=CochainClass.classOf (cochainCxZMod2 X) p c.val c.2 :=
  CochainClass.classOf_liftCycles (cochainCxZMod2 X) p (cycleIncl X r hr p) (cycleIncl_closed X r hr p) c

theorem ordinaryCycleClass_boundary (p : ℕ) :
    (coboundaries (ofSpace X r hr) p).comap (cocycles (ofSpace X r hr) p).subtype ≤
      (ordinaryCycleClass X r hr p).ker := by
  intro c hc
  change ordinaryCycleClass X r hr p c=0
  rw [ordinaryCycleClass_apply]
  cases p with
  | zero =>
    have hz : c.val=0 := (Submodule.mem_bot (ZMod 2)).mp hc
    have h0 : ((cochainCxZMod2 X).d 0 1).hom 0=0 := map_zero _
    exact (CochainClass.classOf_congr _ _ hz _ h0).trans (CochainClass.classOf_zero _ _ h0)
  | succ m =>
    obtain ⟨η,hη⟩ := hc
    have hclosed := CochainClass.closed_boundary (cochainCxZMod2 X) m (m+1) η
    calc
      _ = CochainClass.classOf (cochainCxZMod2 X) (m+1) (((cochainCxZMod2 X).d m (m+1)).hom η) hclosed :=
        CochainClass.classOf_congr _ _ hη.symm _ _
      _ = 0 := CochainClass.classOf_boundary _ _ _ _ _

def ordinaryNative (p : ℕ) : H (ofSpace X r hr) p →ₗ[ZMod 2] cohomologyZMod2 X p :=
  Submodule.liftQ _ (ordinaryCycleClass X r hr p) (ordinaryCycleClass_boundary X r hr p)

def forgetNative (p : ℕ) : HR (ofSpace X r hr) p →ₗ[ZMod 2] cohomologyZMod2 X p :=
  (ordinaryNative X r hr p).comp (forget (ofSpace X r hr) p)

theorem forgetNative_singleClass (p : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (hi : cochainPullback r p α=α) :
    forgetNative X r hr p (singleClass X r hr p α hα hi)=CochainClass.classOf (cochainCxZMod2 X) p α hα := by
  change ordinaryCycleClass X r hr p (forgetCocycle (ofSpace X r hr) p (singleCycles X r hr p α hα hi))=_
  rw [ordinaryCycleClass_apply]
  apply CochainClass.classOf_congr
  exact single_same (ofSpace X r hr) p α

variable {X Y : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X) (f : X ⟶ Y) (hf : r≫f=f)

theorem forgetNative_lift (p : ℕ) (s : cohomologyZMod2 Y p) :
    forgetNative X r hr p (lift r hr f hf p s)=(cohPullback f p).hom s := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p s
  change forgetNative X r hr p (lift r hr f hf p (CochainClass.classOf (cochainCxZMod2 Y) p α hα))=
    (cohPullback f p).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα)
  rw [lift_mk,forgetNative_singleClass]
  exact Finsler.BorelEvaluation.classOf_pull f p α hα


variable {A B Z : TopCat.{0}}

def pullHom (rA : A ⟶ A) (rB : B ⟶ B) (hA : rA≫rA=𝟙 A) (hB : rB≫rB=𝟙 B)
    (f : A ⟶ B) (hf : f≫rB=rA≫f) : InvHom (ofSpace B rB hB) (ofSpace A rA hA) where
  f j := ((singularCochainComplexZMod2.map f.op).f j).hom
  comm_d j α := (cochainPullback_cochainCoboundary f j α).symm
  comm_t j α := by
    have h₁ := Finsler.BorelEvaluation.cochain_comp f rB j α
    have h₂ := Finsler.BorelEvaluation.cochain_comp rA f j α
    rw [hf] at h₁
    exact h₁.trans h₂.symm

theorem invariant_composite (rA : A ⟶ A) (rB : B ⟶ B) (f : A ⟶ B) (hf : f≫rB=rA≫f)
    (g : B ⟶ Z) (hg : rB≫g=g) : rA≫(f≫g)=f≫g := by
  rw [←Category.assoc,←hf,Category.assoc,hg]

theorem lift_natural (rA : A ⟶ A) (rB : B ⟶ B) (hA : rA≫rA=𝟙 A) (hB : rB≫rB=𝟙 B)
    (f : A ⟶ B) (hf : f≫rB=rA≫f) (g : B ⟶ Z) (hg : rB≫g=g)
    (p : ℕ) (s : cohomologyZMod2 Z p) :
    HRmap (pullHom rA rB hA hB f hf) p (lift rB hB g hg p s)=
      lift rA hA (f≫g) (invariant_composite rA rB f hf g hg) p s := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Z p s
  change HRmap (pullHom rA rB hA hB f hf) p (lift rB hB g hg p (CochainClass.classOf (cochainCxZMod2 Z) p α hα))=
    lift rA hA (f≫g) _ p (CochainClass.classOf (cochainCxZMod2 Z) p α hα)
  rw [lift_mk,lift_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  change seqMap (pullHom rA rB hA hB f hf) (Pi.single p (cochainPullback g p α))=
    (Pi.single p (cochainPullback (f≫g) p α) : Seq (ofSpace A rA hA))
  calc
    _ = (Pi.single p (cochainPullback f p (cochainPullback g p α)) : Seq (ofSpace A rA hA)) :=
      seqMap_single _ _ _
    _ = _ := congrArg (fun z => (Pi.single p z : Seq (ofSpace A rA hA))) (Finsler.BorelEvaluation.cochain_comp f g p α)

theorem lift_congr_map (rA : A ⟶ A) (hA : rA≫rA=𝟙 A) (f g : A ⟶ Z)
    (hf : rA≫f=f) (hg : rA≫g=g) (he : f=g) (p : ℕ) : lift rA hA f hf p=lift rA hA g hg p := by
  subst g
  rfl

open Finsler.BorelEvaluation Finsler.BorelLoop Finsler.SphereTopClass

theorem fst_sq (P : TopPair.{0}) (r : P ⟶ P) (hr : r≫r=𝟙 P) :
    TopPair.Hom.fst r≫TopPair.Hom.fst r=𝟙 P.fst := congrArg TopPair.Hom.fst hr

abbrev fullComplex (n : ℕ) : InvComplex := ofSpace (fullPair n).fst (TopPair.Hom.fst (revFullPair n))
  (fst_sq _ _ (revFullPair_sq n))

abbrev levComplex {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) : InvComplex :=
  ofSpace (levPair F a).fst (TopPair.Hom.fst (revPair F a)) (fst_sq _ _ (revPair_sq F a))

/-- An actual ambient absolute reflection Borel element, distinguished from the relative action. -/
def fullTop (n : ℕ) (hn : 1≤n) : HR (fullComplex n) n :=
  lift (TopPair.Hom.fst (revFullPair n)) (fst_sq _ _ (revFullPair_sq n)) (fullEval n)
    (fullEval_invariant n) n (topClass n hn)

def levTop {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) : HR (levComplex F a) n :=
  lift (TopPair.Hom.fst (revPair F a)) (fst_sq _ _ (revPair_sq F a)) (levEval F a)
    (levEval_invariant F a) n (topClass n hn)

theorem fullTop_ne_zero (n : ℕ) (hn : 1≤n) : fullTop n hn≠0 :=
  lift_ne_zero_of_pull_ne_zero _ _ _ (fullEval_invariant n) n hn _ (eFullTop_ne_zero n hn)

theorem levTop_ne_zero {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    levTop F a hn≠0 :=
  lift_ne_zero_of_pull_ne_zero _ _ _ (levEval_invariant F a) n hn _ (eLevTop_ne_zero F a hn)

theorem fullTop_forget (n : ℕ) (hn : 1≤n) :
    forgetNative (fullPair n).fst (TopPair.Hom.fst (revFullPair n)) (fst_sq _ _ (revFullPair_sq n)) n
      (fullTop n hn)=eFullTop n hn :=
  forgetNative_lift _ _ _ (fullEval_invariant n) n (topClass n hn)

theorem levTop_forget {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    forgetNative (levPair F a).fst (TopPair.Hom.fst (revPair F a)) (fst_sq _ _ (revPair_sq F a)) n
      (levTop F a hn)=eLevTop F a hn :=
  forgetNative_lift _ _ _ (levEval_invariant F a) n (topClass n hn)


theorem lift_injective {X Y : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X) (f : X ⟶ Y)
    (hf : r≫f=f) (p : ℕ) (hp : Function.Injective (cohPullback f p).hom) :
    Function.Injective (lift r hr f hf p) := by
  intro a b hab
  apply hp
  have h := congrArg (forgetNative X r hr p) hab
  simpa only [forgetNative_lift] using h

def fullRes {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) :
    InvHom (fullComplex n) (levComplex F a) :=
  pullHom (TopPair.Hom.fst (revPair F a)) (TopPair.Hom.fst (revFullPair n))
    (fst_sq _ _ (revPair_sq F a)) (fst_sq _ _ (revFullPair_sq n)) (TopPair.Hom.fst (resPair F a))
    (congrArg TopPair.Hom.fst (resPair_equivariant F a))

def cutRes {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b) :
    InvHom (levComplex F b) (levComplex F a) :=
  pullHom (TopPair.Hom.fst (revPair F a)) (TopPair.Hom.fst (revPair F b))
    (fst_sq _ _ (revPair_sq F a)) (fst_sq _ _ (revPair_sq F b)) (TopPair.Hom.fst (cutPair F hab))
    (congrArg TopPair.Hom.fst (cutPair_equivariant F hab))

theorem fullTop_res {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    HRmap (fullRes F a) n (fullTop n hn)=levTop F a hn := by
  have h := lift_natural (TopPair.Hom.fst (revPair F a)) (TopPair.Hom.fst (revFullPair n))
    (fst_sq _ _ (revPair_sq F a)) (fst_sq _ _ (revFullPair_sq n)) (TopPair.Hom.fst (resPair F a))
    (congrArg TopPair.Hom.fst (resPair_equivariant F a)) (fullEval n) (fullEval_invariant n) n (topClass n hn)
  have he := lift_congr_map (TopPair.Hom.fst (revPair F a)) (fst_sq _ _ (revPair_sq F a))
    (TopPair.Hom.fst (resPair F a)≫fullEval n) (levEval F a)
    (invariant_composite _ _ _ (congrArg TopPair.Hom.fst (resPair_equivariant F a)) _ (fullEval_invariant n))
    (levEval_invariant F a) (res_eval F a) n
  exact h.trans (congrArg (fun l : cohomologyZMod2 (sphere n) n →ₗ[ZMod 2] HR (levComplex F a) n => l (topClass n hn)) he)

theorem levTop_cut {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b) (hn : 1≤n) :
    HRmap (cutRes F hab) n (levTop F b hn)=levTop F a hn := by
  have h := lift_natural (TopPair.Hom.fst (revPair F a)) (TopPair.Hom.fst (revPair F b))
    (fst_sq _ _ (revPair_sq F a)) (fst_sq _ _ (revPair_sq F b)) (TopPair.Hom.fst (cutPair F hab))
    (congrArg TopPair.Hom.fst (cutPair_equivariant F hab)) (levEval F b) (levEval_invariant F b) n (topClass n hn)
  have he := lift_congr_map (TopPair.Hom.fst (revPair F a)) (fst_sq _ _ (revPair_sq F a))
    (TopPair.Hom.fst (cutPair F hab)≫levEval F b) (levEval F a)
    (invariant_composite _ _ _ (congrArg TopPair.Hom.fst (cutPair_equivariant F hab)) _ (levEval_invariant F b))
    (levEval_invariant F a) (cut_eval F hab) n
  exact h.trans (congrArg (fun l : cohomologyZMod2 (sphere n) n →ₗ[ZMod 2] HR (levComplex F a) n => l (topClass n hn)) he)


theorem singleClass_congr (X : TopCat.{0}) (r : X ⟶ X) (hr : r≫r=𝟙 X) (p : ℕ)
    {α β : singularCochainGroup (ZMod 2) X p} (he : α=β)
    (hα : cochainCoboundary (ZMod 2) X p α=0) (hβ : cochainCoboundary (ZMod 2) X p β=0)
    (hi : cochainPullback r p α=α) (hj : cochainPullback r p β=β) :
    singleClass X r hr p α hα hi=singleClass X r hr p β hβ hj := by
  subst β
  rfl

theorem strict_comp {X Y Z : TopCat.{0}} (r : X ⟶ X) (f : X ⟶ Y) (hf : r≫f=f) (g : Y ⟶ Z) :
    r≫(f≫g)=f≫g := by
  rw [←Category.assoc,hf]

theorem lift_comp {X Y Z : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X) (f : X ⟶ Y) (hf : r≫f=f)
    (g : Y ⟶ Z) (p : ℕ) (s : cohomologyZMod2 Z p) :
    lift r hr (f≫g) (strict_comp r f hf g) p s=lift r hr f hf p ((cohPullback g p).hom s) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Z p s
  rw [cohPullback_cocycleClass]
  change lift r hr (f≫g) _ p (CochainClass.classOf (cochainCxZMod2 Z) p α hα)=
    lift r hr f hf p (CochainClass.classOf (cochainCxZMod2 Y) p (cochainPullback g p α) (cochainPullback_cocycle g p α hα))
  rw [lift_mk,lift_mk]
  apply singleClass_congr
  exact (Finsler.BorelEvaluation.cochain_comp f g p α).symm

theorem lift_topClass_zero_of_avoids {X : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X) (n : ℕ) (hn : 1≤n)
    (p : Finsler.SphereGeometry.Sphere n) (e : X ⟶ sphere n) (he : r≫e=e) (hp : ∀ x, e x≠p) :
    lift r hr e he n (topClass n hn)=0 := by
  let ep := SpherePuncturedEvaluation.avoidingMap n p e hp
  have hep : r≫ep=ep := by
    ext x : 1
    apply Subtype.ext
    exact congrArg (fun φ => φ x) he
  have hzero := lift_comp r hr ep hep (SpherePuncturedEvaluation.inclusion n p) n (topClass n hn)
  rw [SpherePuncturedEvaluation.pullback_topClass_zero,map_zero] at hzero
  have heq : ep≫SpherePuncturedEvaluation.inclusion n p=e := SpherePuncturedEvaluation.avoidingMap_include n p e hp
  rw [lift_congr_map r hr _ e _ he heq n] at hzero
  exact hzero

end
end Finsler.BorelAbsolute
