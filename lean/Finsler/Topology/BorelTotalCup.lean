module
public import Finsler.Topology.BorelTwistedDifferential
public import Finsler.Topology.BorelAbsoluteCup
public import Finsler.Topology.BorelInvolutionHomotopy
/-! The actual finite twisted singular-cochain convolution preserves Borel cocycles and both input boundaries in all degrees, including zero, and descends to a bilinear product of arbitrary absolute reflection Borel classes. The product has both native unit laws, equivariant pullback naturality and native ordinary-cup forgetting. Multiplication by any lifted target class equals the verified evaluation action and compares with the actual relative-to-ambient map; canonical full/cut e multiplication and its self-annihilation follow. The degree-one unit acts on both sides as the existing w inclusion; its left comparison uses the explicit parity homotopy. Full arbitrary-class associativity and the general absolute-relative module structure remain separate, as do K/O(2), localization, geometric Borel comparison and unconditional MAIN. -/

@[expose] public section
namespace Finsler.BorelTotalCup
open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelTwistedCup Finsler.BorelTwistedDifferential
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : TopCat.{0}} (r : X ⟶ X) (hr : r≫r=𝟙 X)

theorem convolution_low (p q : ℕ) (x y : Seq (BorelAbsolute.ofSpace X r hr))
    (hy : y ∈ low (BorelAbsolute.ofSpace X r hr) q) :
    convolution r hr p x y ∈ low (BorelAbsolute.ofSpace X r hr) (p+q) := by
  intro k hk
  change (∑ a ∈ Finset.range (k+1),term r p k a x y)=0
  apply Finset.sum_eq_zero
  intro a ha
  unfold term
  split_ifs with h
  · have hb : q≤k-a := by omega
    rw [hy (k-a) hb,map_zero,cochainCup_zero_right]
    exact cochainCast_zero _
  · rfl

theorem convolution_cocycle (p q : ℕ) (x : bcocycles (BorelAbsolute.ofSpace X r hr) p)
    (y : bcocycles (BorelAbsolute.ofSpace X r hr) q) :
    convolution r hr p x.val y.val ∈ bcocycles (BorelAbsolute.ofSpace X r hr) (p+q) := by
  obtain ⟨hx,hdx⟩ := (mem_bcocycles _).mp x.2
  obtain ⟨hy,hdy⟩ := (mem_bcocycles _).mp y.2
  refine ⟨?_,?_⟩
  · have he : p+(q+1)=p+q+1 := by omega
    rw [←he]
    exact convolution_low r hr p (q+1) x.val y.val hy
  · change D (BorelAbsolute.ofSpace X r hr) (convolution r hr p x.val y.val)=0
    rw [convolution_D r hr p x.val y.val hx,hdx,hdy]
    unfold convolution
    rw [totalCup_zero_left,totalCup_zero_right]
    exact zero_add _

theorem convolution_boundary_left (p q : ℕ) (x : bcocycles (BorelAbsolute.ofSpace X r hr) p)
    (hx : x.val ∈ bcoboundaries (BorelAbsolute.ofSpace X r hr) p)
    (y : bcocycles (BorelAbsolute.ofSpace X r hr) q) :
    convolution r hr p x.val y.val ∈ bcoboundaries (BorelAbsolute.ofSpace X r hr) (p+q) := by
  obtain ⟨b,hb,he⟩ := hx
  cases p with
  | zero =>
    have hb0 : b=0 := by
      funext j
      exact hb j (Nat.zero_le j)
    rw [hb0,map_zero] at he
    rw [←he]
    unfold convolution
    rw [totalCup_zero_left]
    exact Submodule.zero_mem _
  | succ m =>
    refine ⟨convolution r hr m b y.val,?_,?_⟩
    · have hdeg : m+(q+1)=(m+1)+q := by omega
      rw [←hdeg]
      exact convolution_low r hr m (q+1) b y.val ((mem_bcocycles _).mp y.2).1
    · rw [convolution_D r hr m b y.val hb,he,((mem_bcocycles _).mp y.2).2]
      unfold convolution
      rw [totalCup_zero_right,add_zero]

theorem convolution_boundary_right (p q : ℕ) (x : bcocycles (BorelAbsolute.ofSpace X r hr) p)
    (y : bcocycles (BorelAbsolute.ofSpace X r hr) q)
    (hy : y.val ∈ bcoboundaries (BorelAbsolute.ofSpace X r hr) q) :
    convolution r hr p x.val y.val ∈ bcoboundaries (BorelAbsolute.ofSpace X r hr) (p+q) := by
  obtain ⟨b,hb,he⟩ := hy
  refine ⟨convolution r hr p x.val b,convolution_low r hr p q x.val b hb,?_⟩
  rw [convolution_D r hr p x.val b ((mem_bcocycles _).mp x.2).1,((mem_bcocycles _).mp x.2).2,he]
  unfold convolution
  rw [totalCup_zero_left,zero_add]


/-- Actual bilinear pairing of reflection Borel cocycles. -/
def cyclePairing (p q : ℕ) : bcocycles (BorelAbsolute.ofSpace X r hr) p →ₗ[ZMod 2]
    bcocycles (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2]
    bcocycles (BorelAbsolute.ofSpace X r hr) (p+q) where
  toFun x := {
    toFun y := ⟨convolution r hr p x.val y.val,convolution_cocycle r hr p q x y⟩
    map_add' y z := by
      apply Subtype.ext
      exact totalCup_add_right r p x.val y.val z.val
    map_smul' a y := by
      apply Subtype.ext
      exact totalCup_smul_right r p a x.val y.val }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact totalCup_add_left r p x.val z.val y.val
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact totalCup_smul_left r p a x.val y.val

theorem cyclePairing_right_boundary (p q : ℕ) (x : bcocycles (BorelAbsolute.ofSpace X r hr) p) :
    (bcoboundaries (BorelAbsolute.ofSpace X r hr) q).comap (bcocycles (BorelAbsolute.ofSpace X r hr) q).subtype ≤
      ((bcoboundaries (BorelAbsolute.ofSpace X r hr) (p+q)).comap
        (bcocycles (BorelAbsolute.ofSpace X r hr) (p+q)).subtype).comap (cyclePairing r hr p q x) := by
  intro y hy
  exact convolution_boundary_right r hr p q x y hy

/-- First descend the right input to its actual quotient. -/
def onRight (p q : ℕ) (x : bcocycles (BorelAbsolute.ofSpace X r hr) p) :
    HR (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2] HR (BorelAbsolute.ofSpace X r hr) (p+q) :=
  Submodule.mapQ _ _ (cyclePairing r hr p q x) (cyclePairing_right_boundary r hr p q x)

theorem onRight_mk (p q : ℕ) (x : bcocycles (BorelAbsolute.ofSpace X r hr) p)
    (y : bcocycles (BorelAbsolute.ofSpace X r hr) q) :
    onRight r hr p q x (Submodule.Quotient.mk y)=Submodule.Quotient.mk (cyclePairing r hr p q x y) := rfl

/-- The right-quotient action is linear in the left cocycle. -/
def cycleOperators (p q : ℕ) : bcocycles (BorelAbsolute.ofSpace X r hr) p →ₗ[ZMod 2]
    (HR (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2] HR (BorelAbsolute.ofSpace X r hr) (p+q)) where
  toFun := onRight r hr p q
  map_add' x z := by
    apply LinearMap.ext
    intro y
    obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [LinearMap.add_apply,onRight_mk]
    rw [←Submodule.Quotient.mk_add]
    apply congrArg Submodule.Quotient.mk
    exact congrArg (fun A => A c) (map_add (cyclePairing r hr p q) x z)
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [LinearMap.smul_apply,onRight_mk]
    rw [←Submodule.Quotient.mk_smul]
    apply congrArg Submodule.Quotient.mk
    exact congrArg (fun A => A c) (map_smul (cyclePairing r hr p q) a x)

theorem cycleOperators_left_boundary (p q : ℕ) :
    (bcoboundaries (BorelAbsolute.ofSpace X r hr) p).comap (bcocycles (BorelAbsolute.ofSpace X r hr) p).subtype ≤
      (cycleOperators r hr p q).ker := by
  intro x hx
  change onRight r hr p q x=0
  apply LinearMap.ext
  intro y
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [onRight_mk,LinearMap.zero_apply,Submodule.Quotient.mk_eq_zero]
  exact convolution_boundary_left r hr p q x hx c

/-- Actual bilinear product of arbitrary absolute reflection Borel classes. -/
def cup (p q : ℕ) : HR (BorelAbsolute.ofSpace X r hr) p →ₗ[ZMod 2]
    HR (BorelAbsolute.ofSpace X r hr) q →ₗ[ZMod 2] HR (BorelAbsolute.ofSpace X r hr) (p+q) :=
  Submodule.liftQ _ (cycleOperators r hr p q) (cycleOperators_left_boundary r hr p q)

theorem cup_mk (p q : ℕ) (x : bcocycles (BorelAbsolute.ofSpace X r hr) p)
    (y : bcocycles (BorelAbsolute.ofSpace X r hr) q) :
    cup r hr p q (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)=
      Submodule.Quotient.mk (cyclePairing r hr p q x y) := rfl


variable {Y : TopCat.{0}} (f : X ⟶ Y) (hf : r≫f=f)

/-- Multiplication by an actual lifted class equals the already verified evaluation action. -/
theorem cup_lift (p : ℕ) (a : cohomologyZMod2 Y p) (q : ℕ)
    (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    cup r hr p q (BorelAbsolute.lift r hr f hf p a) x=
      (BorelAbsoluteCup.classAction r hr f hf p q).hom a x := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective Y p a
  change cup r hr p q (BorelAbsolute.lift r hr f hf p (CochainClass.classOf (cochainCxZMod2 Y) p α hα)) x=
    (BorelAbsoluteCup.classAction r hr f hf p q).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) x
  rw [BorelAbsolute.lift_mk,BorelAbsoluteCup.classAction_mk]
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  unfold BorelAbsolute.singleClass BorelAbsoluteCup.cochainCup BorelAbsoluteCup.cup
  rw [cup_mk,BorelGraded.onHR_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact totalCup_single_left r hr p (cochainPullback f p α) (cochainPullback_cocycle f p α hα)
    (BorelAbsoluteCup.pull_invariant r f hf p α) c.val

theorem cup_lift_one (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelGraded.castHR (Nat.zero_add q) (cup r hr 0 q (BorelAbsolute.lift r hr f hf 0 (oneZMod2 Y)) x)=x := by
  rw [cup_lift]
  exact BorelAbsoluteCup.classAction_one r hr f hf q x

open Finsler.BorelEvaluation Finsler.SphereTopClass

theorem fullTop_cup (n : ℕ) (hn : 1≤n) (q : ℕ) (x : HR (BorelAbsolute.fullComplex n) q) :
    cup (TopPair.Hom.fst (BorelLoop.revFullPair n)) (BorelAbsolute.fst_sq _ _ (BorelLoop.revFullPair_sq n)) n q
      (BorelAbsolute.fullTop n hn) x=BorelAbsoluteCup.fullE n hn q x :=
  cup_lift _ _ _ (fullEval_invariant n) n (topClass n hn) q x

theorem levTop_cup {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (BorelAbsolute.levComplex F a) q) :
    cup (TopPair.Hom.fst (BorelLoop.revPair F a)) (BorelAbsolute.fst_sq _ _ (BorelLoop.revPair_sq F a)) n q
      (BorelAbsolute.levTop F a hn) x=BorelAbsoluteCup.levE F a hn q x :=
  cup_lift _ _ _ (levEval_invariant F a) n (topClass n hn) q x

theorem fullTop_cup_self (n : ℕ) (hn : 1≤n) :
    cup (TopPair.Hom.fst (BorelLoop.revFullPair n)) (BorelAbsolute.fst_sq _ _ (BorelLoop.revFullPair_sq n)) n n
      (BorelAbsolute.fullTop n hn) (BorelAbsolute.fullTop n hn)=0 := by
  rw [fullTop_cup]
  exact BorelAbsoluteCup.fullE_top_zero n hn

theorem levTop_cup_self {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    cup (TopPair.Hom.fst (BorelLoop.revPair F a)) (BorelAbsolute.fst_sq _ _ (BorelLoop.revPair_sq F a)) n n
      (BorelAbsolute.levTop F a hn) (BorelAbsolute.levTop F a hn)=0 := by
  rw [levTop_cup]
  exact BorelAbsoluteCup.levE_top_zero F a hn


/-- The arbitrary-class product recovers the native ordinary cup under forgetting. -/
theorem cup_forget (p q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) p)
    (y : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelAbsolute.forgetNative X r hr (p+q) (cup r hr p q x y)=
      cupZMod2 (BorelAbsolute.forgetNative X r hr p x) (BorelAbsolute.forgetNative X r hr q y) := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨d,rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [cup_mk,BorelAbsoluteCup.forgetNative_mk,BorelAbsoluteCup.forgetNative_mk,BorelAbsoluteCup.forgetNative_mk]
  have ht := totalCup_top r hr p q c.val d.val ((mem_bcocycles _).mp d.2).1
  calc
    _ = CochainClass.classOf (cochainCxZMod2 X) (p+q) (SphereOddDegree.cochainCup p q (c.val p) (d.val q))
        (cochainCupZMod2_respects_cocycles p q _ _ (bcocycle_comp _ p c) (bcocycle_comp _ q d)) :=
      CochainClass.classOf_congr _ _ ht _ _
    _ = _ := (cupZMod2_mk _ _ _ _).symm

section Naturality
variable {A B : TopCat.{0}} (rA : A ⟶ A) (rB : B ⟶ B)
    (hA : rA≫rA=𝟙 A) (hB : rB≫rB=𝟙 B) (f : A ⟶ B) (hEquiv : f≫rB=rA≫f)

include hA hB hEquiv in
theorem act_natural (i k : ℕ) (α : singularCochainGroup (ZMod 2) B k) :
    cochainPullback f k (act rB i k α)=act rA i k (cochainPullback f k α) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [act_succ_left,act_succ_left]
    have ht := (BorelAbsolute.pullHom rA rB hA hB f hEquiv).comm_t k (act rB i k α)
    change cochainPullback f k (cochainPullback rB k (act rB i k α))=
      cochainPullback rA k (cochainPullback f k (act rB i k α)) at ht
    rw [ht,ih]

theorem pull_cast {i j : ℕ} (h : i=j) (α : singularCochainGroup (ZMod 2) B i) :
    cochainPullback f j (cochainCast h α)=cochainCast h (cochainPullback f i α) := by
  subst j
  rfl

theorem term_natural (p k a : ℕ) (x y : (j : ℕ) → singularCochainGroup (ZMod 2) B j) :
    cochainPullback f k (term rB p k a x y)=
      term rA p k a (seqMap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) x)
        (seqMap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) y) := by
  unfold term
  split_ifs with h
  · rw [pull_cast f,cochainCup_naturality,act_natural rA rB hA hB f hEquiv]
    rfl
  · exact map_zero (((singularCochainComplexZMod2.map f.op).f k).hom)

theorem convolution_natural (p : ℕ) (x y : Seq (BorelAbsolute.ofSpace B rB hB)) :
    seqMap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) (convolution rB hB p x y)=
      convolution rA hA p (seqMap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) x)
        (seqMap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) y) := by
  funext k
  change (((singularCochainComplexZMod2.map f.op).f k).hom)
    (∑ a ∈ Finset.range (k+1),term rB p k a x y)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact term_natural rA rB hA hB f hEquiv p k a x y

theorem cup_natural (p q : ℕ) (x : HR (BorelAbsolute.ofSpace B rB hB) p)
    (y : HR (BorelAbsolute.ofSpace B rB hB) q) :
    HRmap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) (p+q) (cup rB hB p q x y)=
      cup rA hA p q (HRmap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) p x)
        (HRmap (BorelAbsolute.pullHom rA rB hA hB f hEquiv) q y) := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨d,rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (bcocycleMap _ (p+q) (cyclePairing rB hB p q c d))=
    cup rA hA p q (Submodule.Quotient.mk (bcocycleMap _ p c)) (Submodule.Quotient.mk (bcocycleMap _ q d))
  rw [cup_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact convolution_natural rA rB hA hB f hEquiv p c.val d.val
end Naturality

/-- Compatibility of multiplication by every lifted target class with the actual relative-to-ambient map. -/
theorem cup_toAbsolute (P : TopPair.{0}) (s : P ⟶ P) (hs : s≫s=𝟙 P)
    {Y : TopCat.{0}} (f : P.fst ⟶ Y) (hf : TopPair.Hom.fst s≫f=f)
    (p : ℕ) (a : cohomologyZMod2 Y p) (q : ℕ) (x : HR (BorelPair.ofPair P s hs) q) :
    cup (TopPair.Hom.fst s) (BorelAbsolute.fst_sq P s hs) p q
      (BorelAbsolute.lift (TopPair.Hom.fst s) (BorelAbsolute.fst_sq P s hs) f hf p a)
      (HRmap (BorelAbsoluteCup.toAbsolute P s hs) q x)=
    HRmap (BorelAbsoluteCup.toAbsolute P s hs) (p+q)
      ((BorelPullbackCup.classAction P s hs f hf p q).hom a x) := by
  rw [cup_lift]
  exact (BorelAbsoluteCup.classAction_toAbsolute P s hs f hf p a q x).symm

/-- The native absolute Borel unit is the degree-zero single singular unit. -/
def one : HR (BorelAbsolute.ofSpace X r hr) 0 :=
  BorelAbsolute.singleClass X r hr 0 (cochainOne (R := ZMod 2) (Z := X))
    (cochainCoboundary_cochainOne X) (BorelAbsoluteCup.pullback_one r)

theorem convolution_one_left (y : Seq (BorelAbsolute.ofSpace X r hr)) :
    convolution r hr 0 (Pi.single 0 (cochainOne (R := ZMod 2) (Z := X))) y=y := by
  rw [convolution,totalCup_single_left r hr 0 _ (cochainCoboundary_cochainOne X) (BorelAbsoluteCup.pullback_one r)]
  let A := BorelTwistedCup.gradedCup r hr 0 (cochainOne (R := ZMod 2) (Z := X))
    (cochainCoboundary_cochainOne X) (BorelAbsoluteCup.pullback_one r)
  change BorelGraded.total A y=y
  funext j
  calc
    _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j) (BorelGraded.total A y (0+j)) :=
      BorelGraded.cast_seq (Nat.zero_add j) _
    _ = BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j) (A.f j (y j)) :=
      congrArg (BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j)) (BorelGraded.total_at A y j)
    _ = y j := by
      change BorelGraded.castC (BorelAbsolute.ofSpace X r hr) (Nat.zero_add j)
        (SphereOddDegree.cochainCup 0 j (cochainOne (R := ZMod 2) (Z := X)) (y j))=y j
      rw [←cast_absolute r hr,CupUnit.cochain_one_left,cochainCast_cast]

theorem convolution_one_right (p : ℕ) (x : (j : ℕ) → singularCochainGroup (ZMod 2) X j)
    (hx : x ∈ low (BorelAbsolute.ofSpace X r hr) (p+1)) :
    convolution r hr p x (Pi.single 0 (cochainOne (R := ZMod 2) (Z := X)))=x := by
  funext k
  change (∑ a ∈ Finset.range (k+1),term r p k a x (Pi.single 0 (cochainOne (R := ZMod 2) (Z := X))))=x k
  rw [Finset.sum_eq_single k]
  · unfold term
    split_ifs with h
    · have hk : k-k=0 := Nat.sub_self k
      rw [cast_absolute r hr]
      calc
        _ = SphereOddDegree.cochainCup k 0 (x k) (act r (p-k) 0 ((Pi.single 0 (cochainOne (R := ZMod 2) (Z := X))) 0)) :=
          cast_cup_act r hr hk k (p-k) (x k) (Pi.single 0 (cochainOne (R := ZMod 2) (Z := X)))
        _ = x k := by rw [Pi.single_eq_same,act_invariant r _ _ _ (BorelAbsoluteCup.pullback_one r),cochainCup_one]
    · have hp : p+1≤k := by omega
      exact (hx k hp).symm
  · intro a ha hak
    unfold term
    split_ifs with h
    · have hn : k-a≠0 := by omega
      rw [Pi.single_eq_of_ne hn,map_zero,cochainCup_zero_right]
      exact cochainCast_zero _
    · rfl
  · intro hk
    exact (hk (Finset.mem_range.mpr (Nat.lt_succ_self k))).elim

theorem cup_one_left (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelGraded.castHR (Nat.zero_add q) (cup r hr 0 q (one r hr) x)=x := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  unfold one BorelAbsolute.singleClass
  rw [cup_mk]
  have ht := convolution_one_left r hr c.val
  have hc : convolution r hr 0 (Pi.single 0 (cochainOne (R := ZMod 2) (Z := X))) c.val ∈ bcocycles (BorelAbsolute.ofSpace X r hr) q := by
    rw [ht];exact c.2
  calc
    _ = Submodule.Quotient.mk (⟨_,hc⟩ : bcocycles (BorelAbsolute.ofSpace X r hr) q) := BorelGraded.castHR_mk _ _ _ _
    _ = Submodule.Quotient.mk c := congrArg Submodule.Quotient.mk (Subtype.ext ht)

theorem cup_one_right (p : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) p) :
    cup r hr p 0 x (one r hr)=x := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  unfold one BorelAbsolute.singleClass
  rw [cup_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact convolution_one_right r hr p c.val ((mem_bcocycles _).mp c.2).1

/-- Multiplication by the group-degree-one unit twists every component by the original reflection. -/
theorem convolution_w_left (y : (j : ℕ) → singularCochainGroup (ZMod 2) X j) :
    convolution r hr 1 (Pi.single 0 (cochainOne (R := ZMod 2) (Z := X))) y=
      seqMap (BorelInvolutionHomotopy.involutionHom (BorelAbsolute.ofSpace X r hr)) y := by
  funext k
  change (∑ a ∈ Finset.range (k+1),term r 1 k a (Pi.single 0 (cochainOne (R := ZMod 2) (Z := X))) y)=cochainPullback r k (y k)
  rw [Finset.sum_eq_single 0]
  · unfold term
    rw [dite_eq_left (show 0≤k ∧ 0≤1 by omega)]
    simp only [Nat.sub_zero,Pi.single_eq_same]
    rw [CupUnit.cochain_one_left,cochainCast_cast]
    rfl
  · intro a ha ha0
    unfold term
    split_ifs with h
    · rw [Pi.single_eq_of_ne ha0,cochainCup_zero_left,cochainCast_zero]
    · rfl
  · intro h0
    exact (h0 (Finset.mem_range.mpr (by omega))).elim

/-- The degree-one Borel element represented by the singular unit in vertical degree zero. -/
def wElement : HR (BorelAbsolute.ofSpace X r hr) 1 := w (BorelAbsolute.ofSpace X r hr) 0 (one r hr)

/-- The native twisted cup by the degree-one unit equals the previously constructed w inclusion.
The equality uses the explicit parity boundary, rather than a false cochain equality. -/
theorem wElement_cup (q : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) q) :
    BorelGraded.castHR (Nat.add_comm 1 q) (cup r hr 1 q (wElement r hr) x)=w (BorelAbsolute.ofSpace X r hr) q x := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let K := BorelAbsolute.ofSpace X r hr
  let cw : bcocycles K (q+1) := ⟨c.val,bcocycles_mono K q c.2⟩
  let cu : bcocycles K 1 := ⟨Pi.single 0 (cochainOne (R := ZMod 2) (Z := X)),
    bcocycles_mono K 0 (BorelAbsolute.singleCycles X r hr 0 _ (cochainCoboundary_cochainOne X) (BorelAbsoluteCup.pullback_one r)).2⟩
  have ht : convolution r hr 1 cu.val c.val=seqMap (BorelInvolutionHomotopy.involutionHom K) cw.val := convolution_w_left r hr c.val
  have hc : convolution r hr 1 cu.val c.val ∈ bcocycles K (q+1) := by
    rw [ht]
    exact (bcocycleMap (BorelInvolutionHomotopy.involutionHom K) (q+1) cw).2
  change BorelGraded.castHR (Nat.add_comm 1 q) (cup r hr 1 q (Submodule.Quotient.mk cu) (Submodule.Quotient.mk c))=Submodule.Quotient.mk cw
  rw [cup_mk]
  calc
    _ = Submodule.Quotient.mk (⟨_,hc⟩ : bcocycles K (q+1)) := BorelGraded.castHR_mk _ _ _ _
    _ = HRmap (BorelInvolutionHomotopy.involutionHom K) (q+1) (Submodule.Quotient.mk cw) :=
      congrArg Submodule.Quotient.mk (Subtype.ext ht)
    _ = Submodule.Quotient.mk cw := BorelInvolutionHomotopy.involution_HR K (q+1) _

/-- Right multiplication by the same unit is already the old w at the cochain level. -/
theorem cup_wElement (p : ℕ) (x : HR (BorelAbsolute.ofSpace X r hr) p) :
    cup r hr p 1 x (wElement r hr)=w (BorelAbsolute.ofSpace X r hr) p x := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  unfold wElement one BorelAbsolute.singleClass
  change cup r hr p 1 (Submodule.Quotient.mk c)
    (Submodule.Quotient.mk (Submodule.inclusion (bcocycles_mono _ 0) (BorelAbsolute.singleCycles X r hr 0 _ _ _)))=
    Submodule.Quotient.mk (Submodule.inclusion (bcocycles_mono _ p) c)
  rw [cup_mk]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  exact convolution_one_right r hr p c.val ((mem_bcocycles _).mp c.2).1

end
end Finsler.BorelTotalCup
