module
public import Finsler.Topology.BorelEvaluationClass
public import Finsler.Topology.CupUnit
public import Finsler.Topology.CupAssociativity
/-! Unit and associativity of the actual reflection-equivariant evaluation cup, for a strictly invariant map and for every full/cut sphere-loop pair. These are explicit graded laws, including the required degree casts; no K/O(2) extension or geometric Borel comparison is assumed. -/

@[expose] public section
namespace Finsler.BorelEvaluationLaws
open CategoryTheory SphereOddDegree Finsler.BorelCochain Finsler.BorelPair
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (P : TopPair.{0}) (r : P ⟶ P) (hr : r≫r=𝟙 P)
variable {X : TopCat.{0}} (f : P.fst ⟶ X) (hf : TopPair.Hom.fst r≫f=f)

theorem pullback_one : cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := X))=
    cochainOne (R := ZMod 2) (Z := P.fst) := by
  apply cochain_ext
  intro σ
  rw [cochainPullback_eval, cochainOne_eval, cochainOne_eval]

theorem total_one (c : Seq (ofPair P r hr)) :
    BorelGraded.total (BorelCup.gradedCup P r hr 0
      (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := X)))
      (cochainPullback_cocycle f 0 _ (cochainCoboundary_cochainOne X))
      (BorelEvaluation.cochain_invariant r f hf 0 _)) c=c := by
  let A := BorelCup.gradedCup P r hr 0
    (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := X)))
    (cochainPullback_cocycle f 0 _ (cochainCoboundary_cochainOne X))
    (BorelEvaluation.cochain_invariant r f hf 0 _)
  change BorelGraded.total A c=c
  funext j
  calc
    _ = BorelGraded.castC (ofPair P r hr) (Nat.zero_add j) (BorelGraded.total A c (0+j)) :=
      BorelGraded.cast_seq (Nat.zero_add j) _
    _ = BorelGraded.castC (ofPair P r hr) (Nat.zero_add j) (A.f j (c j)) :=
      congrArg (BorelGraded.castC (ofPair P r hr) (Nat.zero_add j)) (BorelGraded.total_at A c j)
    _ = c j := by
      change BorelGraded.castC (ofPair P r hr) (Nat.zero_add j)
        (RelativeCupCochain.cup P 0 j (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := X))) (c j))=c j
      rw [← BorelCup.cast_relative P r hr, pullback_one]
      exact CupUnit.relative_cochain_one_left P j (c j)

theorem classAction_one (q : ℕ) (x : HR (ofPair P r hr) q) :
    BorelGraded.castHR (Nat.zero_add q)
      ((BorelPullbackCup.classAction P r hr f hf 0 q).hom (oneZMod2 X) x)=x := by
  change BorelGraded.castHR (Nat.zero_add q)
    ((BorelPullbackCup.classAction P r hr f hf 0 q).hom
      (CochainClass.classOf (cochainCxZMod2 X) 0 (cochainOne (R := ZMod 2) (Z := X))
        (cochainCoboundary_cochainOne X)) x)=x
  rw [BorelPullbackCup.classAction_mk]
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let A := BorelCup.gradedCup P r hr 0
    (cochainPullback f 0 (cochainOne (R := ZMod 2) (Z := X)))
    (cochainPullback_cocycle f 0 _ (cochainCoboundary_cochainOne X))
    (BorelEvaluation.cochain_invariant r f hf 0 _)
  have ht : BorelGraded.total A c.val=c.val := total_one P r hr f hf c.val
  have hc : BorelGraded.total A c.val ∈ bcocycles (ofPair P r hr) q := by
    rw [ht]
    exact c.2
  change BorelGraded.castHR (Nat.zero_add q) (Submodule.Quotient.mk (BorelGraded.cyclesMap A q c))=
    Submodule.Quotient.mk c
  calc
    _ = Submodule.Quotient.mk (⟨BorelGraded.total A c.val,hc⟩ : bcocycles (ofPair P r hr) q) :=
      BorelGraded.castHR_mk _ _ _ _
    _ = Submodule.Quotient.mk c := congrArg Submodule.Quotient.mk (Subtype.ext ht)

def graded (p : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (hα : cochainCoboundary (ZMod 2) X p α=0) : BorelGraded.Map (ofPair P r hr) (ofPair P r hr) p :=
  BorelCup.gradedCup P r hr p (cochainPullback f p α) (cochainPullback_cocycle f p α hα)
    (BorelEvaluation.cochain_invariant r f hf p α)

theorem castC_injective (K : InvComplex) {a b : ℕ} (h : a=b) :
    Function.Injective (BorelGraded.castC K h) := by
  subst b
  exact fun _ _ h => h

theorem total_comp (p s : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (β : singularCochainGroup (ZMod 2) X s)
    (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hβ : cochainCoboundary (ZMod 2) X s β=0) (c : Seq (ofPair P r hr)) :
    BorelGraded.total (graded P r hr f hf (p+s) (cochainCup p s α β)
      (cochainCupZMod2_respects_cocycles p s α β hα hβ)) c =
    BorelGraded.total (graded P r hr f hf p α hα)
      (BorelGraded.total (graded P r hr f hf s β hβ) c) := by
  let A := graded P r hr f hf p α hα
  let B := graded P r hr f hf s β hβ
  let C := graded P r hr f hf (p+s) (cochainCup p s α β)
    (cochainCupZMod2_respects_cocycles p s α β hα hβ)
  change BorelGraded.total C c = BorelGraded.total A (BorelGraded.total B c)
  funext j
  by_cases hj : p+s≤j
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
    apply castC_injective (ofPair P r hr) (Nat.add_assoc p s k)
    have he : BorelGraded.castC (ofPair P r hr) (Nat.add_assoc p s k) (C.f k (c k)) =
        A.f (s+k) (B.f k (c k)) := by
      change BorelGraded.castC (ofPair P r hr) (Nat.add_assoc p s k)
        (RelativeCupCochain.cup P (p+s) k (cochainPullback f (p+s) (cochainCup p s α β)) (c k)) =
        RelativeCupCochain.cup P p (s+k) (cochainPullback f p α)
          (RelativeCupCochain.cup P s k (cochainPullback f s β) (c k))
      rw [← BorelCup.cast_relative P r hr, cochainCup_naturality]
      exact CupAssociativity.relative_cochain_assoc P p s k _ _ _
    calc
      _ = BorelGraded.castC (ofPair P r hr) (Nat.add_assoc p s k) (C.f k (c k)) :=
        congrArg (BorelGraded.castC (ofPair P r hr) (Nat.add_assoc p s k)) (BorelGraded.total_at C c k)
      _ = A.f (s+k) (B.f k (c k)) := he
      _ = BorelGraded.total A (BorelGraded.total B c) (p+(s+k)) := by
        rw [BorelGraded.total_at, BorelGraded.total_at]
      _ = BorelGraded.castC (ofPair P r hr) (Nat.add_assoc p s k)
          (BorelGraded.total A (BorelGraded.total B c) ((p+s)+k)) :=
        BorelGraded.cast_seq (Nat.add_assoc p s k) _
  · rw [BorelGraded.total_below C c (by omega)]
    by_cases hp : p≤j
    · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hp
      rw [BorelGraded.total_at, BorelGraded.total_below B c (by omega), map_zero]
    · rw [BorelGraded.total_below A _ (by omega)]

theorem cochainCup_assoc (p s : ℕ) (α : singularCochainGroup (ZMod 2) X p)
    (β : singularCochainGroup (ZMod 2) X s)
    (hα : cochainCoboundary (ZMod 2) X p α=0)
    (hβ : cochainCoboundary (ZMod 2) X s β=0) (q : ℕ) (x : HR (ofPair P r hr) q) :
    BorelGraded.castHR (Nat.add_assoc p s q)
      (BorelPullbackCup.cochainCup P r hr f hf (p+s) (cochainCup p s α β)
        (cochainCupZMod2_respects_cocycles p s α β hα hβ) q x) =
    BorelPullbackCup.cochainCup P r hr f hf p α hα (s+q)
      (BorelPullbackCup.cochainCup P r hr f hf s β hβ q x) := by
  obtain ⟨c,rfl⟩ := Submodule.Quotient.mk_surjective _ x
  let A := graded P r hr f hf p α hα
  let B := graded P r hr f hf s β hβ
  let C := graded P r hr f hf (p+s) (cochainCup p s α β)
    (cochainCupZMod2_respects_cocycles p s α β hα hβ)
  have ht : BorelGraded.total C c.val=BorelGraded.total A (BorelGraded.total B c.val) :=
    total_comp P r hr f hf p s α β hα hβ c.val
  have hc : BorelGraded.total C c.val ∈ bcocycles (ofPair P r hr) (p+(s+q)) := by
    rw [ht]
    exact (BorelGraded.cyclesMap A (s+q) (BorelGraded.cyclesMap B q c)).2
  change BorelGraded.castHR (Nat.add_assoc p s q) (Submodule.Quotient.mk (BorelGraded.cyclesMap C q c))=
    Submodule.Quotient.mk (BorelGraded.cyclesMap A (s+q) (BorelGraded.cyclesMap B q c))
  calc
    _ = Submodule.Quotient.mk (⟨BorelGraded.total C c.val,hc⟩ : bcocycles (ofPair P r hr) (p+(s+q))) :=
      BorelGraded.castHR_mk _ _ _ _
    _ = _ := congrArg Submodule.Quotient.mk (Subtype.ext ht)

theorem classAction_assoc (p s : ℕ) (a : cohomologyZMod2 X p) (b : cohomologyZMod2 X s)
    (q : ℕ) (x : HR (ofPair P r hr) q) :
    BorelGraded.castHR (Nat.add_assoc p s q)
      ((BorelPullbackCup.classAction P r hr f hf (p+s) q).hom (cupZMod2 a b) x)=
    (BorelPullbackCup.classAction P r hr f hf p (s+q)).hom a
      ((BorelPullbackCup.classAction P r hr f hf s q).hom b x) := by
  obtain ⟨α,hα,rfl⟩ := cocycleClass_surjective X p a
  obtain ⟨β,hβ,rfl⟩ := cocycleClass_surjective X s b
  rw [cupZMod2_mk]
  change BorelGraded.castHR (Nat.add_assoc p s q)
    ((BorelPullbackCup.classAction P r hr f hf (p+s) q).hom
      (CochainClass.classOf (cochainCxZMod2 X) (p+s) (cochainCup p s α β)
        (cochainCupZMod2_respects_cocycles p s α β hα hβ)) x)=
    (BorelPullbackCup.classAction P r hr f hf p (s+q)).hom
      (CochainClass.classOf (cochainCxZMod2 X) p α hα)
      ((BorelPullbackCup.classAction P r hr f hf s q).hom
        (CochainClass.classOf (cochainCxZMod2 X) s β hβ) x)
  rw [BorelPullbackCup.classAction_mk, BorelPullbackCup.classAction_mk, BorelPullbackCup.classAction_mk]
  exact cochainCup_assoc P r hr f hf p s α β hα hβ q x

open Finsler.BorelEvaluation Finsler.BorelEvaluationClass Finsler.BorelLoop

theorem fullClassCup_one (n q : ℕ) (x : HR (fullComplex n) q) :
    BorelGraded.castHR (Nat.zero_add q) (fullClassCup n 0 (oneZMod2 (sphere n)) q x)=x := by
  rw [fullClassCup_eq_action]
  exact classAction_one _ _ _ _ (fullEval_invariant n) q x

theorem levClassCup_one {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ)
    (q : ℕ) (x : HR (levComplex F a) q) :
    BorelGraded.castHR (Nat.zero_add q) (levClassCup F a 0 (oneZMod2 (sphere n)) q x)=x := by
  rw [levClassCup_eq_action]
  exact classAction_one _ _ _ _ (levEval_invariant F a) q x

theorem fullClassCup_assoc (n p s : ℕ) (a : cohomologyZMod2 (sphere n) p)
    (b : cohomologyZMod2 (sphere n) s) (q : ℕ) (x : HR (fullComplex n) q) :
    BorelGraded.castHR (Nat.add_assoc p s q) (fullClassCup n (p+s) (cupZMod2 a b) q x)=
      fullClassCup n p a (s+q) (fullClassCup n s b q x) := by
  rw [fullClassCup_eq_action, fullClassCup_eq_action, fullClassCup_eq_action]
  exact classAction_assoc _ _ _ _ (fullEval_invariant n) p s a b q x

theorem levClassCup_assoc {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (c : ℝ)
    (p s : ℕ) (a : cohomologyZMod2 (sphere n) p) (b : cohomologyZMod2 (sphere n) s)
    (q : ℕ) (x : HR (levComplex F c) q) :
    BorelGraded.castHR (Nat.add_assoc p s q) (levClassCup F c (p+s) (cupZMod2 a b) q x)=
      levClassCup F c p a (s+q) (levClassCup F c s b q x) := by
  rw [levClassCup_eq_action, levClassCup_eq_action, levClassCup_eq_action]
  exact classAction_assoc _ _ _ _ (levEval_invariant F c) p s a b q x
end
end Finsler.BorelEvaluationLaws
