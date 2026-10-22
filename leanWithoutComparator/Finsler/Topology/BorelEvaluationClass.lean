module

public import Finsler.Topology.BorelPullbackCup

/-! Representative-independent reflection evaluation cup on the actual full sphere-loop pair and every actual energy cut. The fixed-representative API equals a bilinear action of actual sphere cohomology, with left addition, scalar multiplication, zero and w compatibility. Unit and associativity, a canonical nonzero sphere top class, K/O(2) extension and localization remain separate. -/

@[expose] public section

namespace Finsler.BorelEvaluationClass
open CategoryTheory SphereOddDegree Finsler.BorelEvaluation Finsler.BorelLoop
open Finsler.BorelCochain
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Bilinear evaluation action, descended from sphere cocycles to actual sphere cohomology. -/
def fullAction (n p q : ℕ) : cohomologyZMod2 (sphere n) p →ₗ[ZMod 2]
    (HR (fullComplex n) q →ₗ[ZMod 2] HR (fullComplex n) (p+q)) :=
  (BorelPullbackCup.classAction (fullPair n) (revFullPair n) (revFullPair_sq n)
    (fullEval n) (fullEval_invariant n) p q).hom

def levAction {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p q : ℕ) :
    cohomologyZMod2 (sphere n) p →ₗ[ZMod 2]
    (HR (levComplex F a) q →ₗ[ZMod 2] HR (levComplex F a) (p+q)) :=
  (BorelPullbackCup.classAction (levPair F a) (revPair F a) (revPair_sq F a)
    (levEval F a) (levEval_invariant F a) p q).hom

theorem fullAction_mk (n p : ℕ) (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0) (q : ℕ) :
    fullAction n p q (CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα)=fullCup n p α hα q :=
  BorelPullbackCup.classAction_mk _ _ _ _ _ p α hα q

theorem levAction_mk {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0) (q : ℕ) :
    levAction F a p q (CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα)=levCup F a p α hα q :=
  BorelPullbackCup.classAction_mk _ _ _ _ _ p α hα q

theorem fullClassCup_eq_action (n p : ℕ) (s : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    fullClassCup n p s q=fullAction n p q s := by
  have h := fullAction_mk n p (classRepr (sphere n) p s) (classRepr_isCocycle (sphere n) p s) q
  change fullAction n p q (cocycleClass (sphere n) p _ _)=fullClassCup n p s q at h
  rw [cocycleClass_classRepr] at h
  exact h.symm

theorem levClassCup_eq_action {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) (q : ℕ) : levClassCup F a p s q=levAction F a p q s := by
  have h := levAction_mk F a p (classRepr (sphere n) p s) (classRepr_isCocycle (sphere n) p s) q
  change levAction F a p q (cocycleClass (sphere n) p _ _)=levClassCup F a p s q at h
  rw [cocycleClass_classRepr] at h
  exact h.symm

theorem fullClassCup_any_representative (n p : ℕ) (s : cohomologyZMod2 (sphere n) p)
    (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0)
    (hs : CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα=s) (q : ℕ) :
    fullClassCup n p s q=fullCup n p α hα q := by
  rw [fullClassCup_eq_action, ← hs, fullAction_mk]

theorem levClassCup_any_representative {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ)
    (p : ℕ) (s : cohomologyZMod2 (sphere n) p) (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0)
    (hs : CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα=s) (q : ℕ) :
    levClassCup F a p s q=levCup F a p α hα q := by
  rw [levClassCup_eq_action, ← hs, levAction_mk]

theorem fullCup_class_congr (n p : ℕ) (α β : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0)
    (hβ : cochainCoboundary (ZMod 2) (sphere n) p β=0)
    (he : CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα =
      CochainClass.classOf (cochainCxZMod2 (sphere n)) p β hβ) (q : ℕ) :
    fullCup n p α hα q=fullCup n p β hβ q :=
  BorelPullbackCup.cochainCup_class_congr _ _ _ _ (fullEval_invariant n) p α β hα hβ he q

theorem levCup_class_congr {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (α β : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0)
    (hβ : cochainCoboundary (ZMod 2) (sphere n) p β=0)
    (he : CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα =
      CochainClass.classOf (cochainCxZMod2 (sphere n)) p β hβ) (q : ℕ) :
    levCup F a p α hα q=levCup F a p β hβ q :=
  BorelPullbackCup.cochainCup_class_congr _ _ _ _ (levEval_invariant F a) p α β hα hβ he q

theorem fullClassCup_add (n p : ℕ) (s t : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    fullClassCup n p (s+t) q=fullClassCup n p s q+fullClassCup n p t q := by
  simp only [fullClassCup_eq_action, map_add]

theorem levClassCup_add {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s t : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    levClassCup F a p (s+t) q=levClassCup F a p s q+levClassCup F a p t q := by
  simp only [levClassCup_eq_action, map_add]

theorem fullClassCup_smul (n p : ℕ) (a : ZMod 2) (s : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    fullClassCup n p (a • s) q=a • fullClassCup n p s q := by
  simp only [fullClassCup_eq_action, map_smul]

theorem levClassCup_smul {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (b : ZMod 2) (s : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    levClassCup F a p (b • s) q=b • levClassCup F a p s q := by
  simp only [levClassCup_eq_action, map_smul]

theorem fullClassCup_zero (n p q : ℕ) : fullClassCup n p 0 q=0 := by
  rw [fullClassCup_eq_action, map_zero]

theorem levClassCup_zero {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p q : ℕ) :
    levClassCup F a p 0 q=0 := by
  rw [levClassCup_eq_action, map_zero]

theorem fullClassCup_w (n p : ℕ) (s : cohomologyZMod2 (sphere n) p) (q : ℕ)
    (x : HR (fullComplex n) q) :
    BorelGraded.castHR (Nat.add_assoc p q 1).symm (fullClassCup n p s (q+1) (w _ q x))=
      w _ (p+q) (fullClassCup n p s q x) :=
  BorelCup.cup_w _ _ _ _ _ _ _ q x

theorem levClassCup_w {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) (q : ℕ) (x : HR (levComplex F a) q) :
    BorelGraded.castHR (Nat.add_assoc p q 1).symm (levClassCup F a p s (q+1) (w _ q x))=
      w _ (p+q) (levClassCup F a p s q x) :=
  BorelCup.cup_w _ _ _ _ _ _ _ q x
end
end Finsler.BorelEvaluationClass
