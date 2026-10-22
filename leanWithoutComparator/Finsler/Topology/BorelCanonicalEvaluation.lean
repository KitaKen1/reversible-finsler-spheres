module
public import Finsler.Topology.BorelEvaluationLaws
public import Finsler.Topology.SphereTopClass
/-! Canonical sphere evaluation action on the actual relative reflection Borel total complex. The unique nonzero sphere class defines a representative-independent action, compatible with full/cut restriction, w and forgetting to the actual ordinary relative cohomology. Its square is zero by the actual sphere cohomology calculation and the proved graded associativity. The ordinary ambient e is separately identified; no ambient equivariant element, K/O(2) extension or localization theorem is claimed. -/

@[expose] public section
namespace Finsler.BorelCanonicalEvaluation
open CategoryTheory SphereOddDegree Finsler.BorelEvaluation Finsler.BorelEvaluationClass
open Finsler.BorelLoop Finsler.BorelCochain Finsler.SphereTopClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The actual relative reflection-equivariant action of the canonical sphere top class. -/
def fullE (n : ℕ) (hn : 1≤n) (q : ℕ) : HR (fullComplex n) q →ₗ[ZMod 2] HR (fullComplex n) (n+q) :=
  fullClassCup n n (topClass n hn) q

def levE {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) (q : ℕ) :
    HR (levComplex F a) q →ₗ[ZMod 2] HR (levComplex F a) (n+q) :=
  levClassCup F a n (topClass n hn) q

theorem fullE_any_nonzero (n : ℕ) (hn : 1≤n) (s : cohomologyZMod2 (sphere n) n) (hs : s≠0) (q : ℕ) :
    fullClassCup n n s q=fullE n hn q := by
  rw [eq_topClass_of_ne_zero n hn s hs]
  rfl

theorem levE_any_nonzero {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (s : cohomologyZMod2 (sphere n) n) (hs : s≠0) (q : ℕ) : levClassCup F a n s q=levE F a hn q := by
  rw [eq_topClass_of_ne_zero n hn s hs]
  rfl

theorem fullE_any_representative (n : ℕ) (hn : 1≤n)
    (α : singularCochainGroup (ZMod 2) (sphere n) n)
    (hα : cochainCoboundary (ZMod 2) (sphere n) n α=0)
    (hs : CochainClass.classOf (cochainCxZMod2 (sphere n)) n α hα≠0) (q : ℕ) :
    fullE n hn q=fullCup n n α hα q :=
  fullClassCup_any_representative n n _ α hα (eq_topClass_of_ne_zero n hn _ hs) q

theorem levE_any_representative {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (α : singularCochainGroup (ZMod 2) (sphere n) n)
    (hα : cochainCoboundary (ZMod 2) (sphere n) n α=0)
    (hs : CochainClass.classOf (cochainCxZMod2 (sphere n)) n α hα≠0) (q : ℕ) :
    levE F a hn q=levCup F a n α hα q :=
  levClassCup_any_representative F a n _ α hα (eq_topClass_of_ne_zero n hn _ hs) q

theorem fullE_res {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (fullComplex n) q) :
    HRmap (resHom F a) (n+q) (fullE n hn q x)=levE F a hn q (HRmap (resHom F a) q x) :=
  fullClassCup_res F a n (topClass n hn) q x

theorem levE_cut {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b)
    (hn : 1≤n) (q : ℕ) (x : HR (levComplex F b) q) :
    HRmap (cutHom F hab) (n+q) (levE F b hn q x)=levE F a hn q (HRmap (cutHom F hab) q x) :=
  levClassCup_cut F hab n (topClass n hn) q x

theorem fullE_w (n : ℕ) (hn : 1≤n) (q : ℕ) (x : HR (fullComplex n) q) :
    BorelGraded.castHR (Nat.add_assoc n q 1).symm (fullE n hn (q+1) (w _ q x))=
      w _ (n+q) (fullE n hn q x) := fullClassCup_w n n (topClass n hn) q x

theorem levE_w {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (levComplex F a) q) :
    BorelGraded.castHR (Nat.add_assoc n q 1).symm (levE F a hn (q+1) (w _ q x))=
      w _ (n+q) (levE F a hn q x) := levClassCup_w F a n (topClass n hn) q x

theorem fullE_square_zero (n : ℕ) (hn : 1≤n) (q : ℕ) (x : HR (fullComplex n) q) :
    fullE n hn (n+q) (fullE n hn q x)=0 := by
  have h := BorelEvaluationLaws.fullClassCup_assoc n n n (topClass n hn) (topClass n hn) q x
  rw [topClass_cup_self, fullClassCup_zero, LinearMap.zero_apply] at h
  simpa only [fullE,map_zero] using h.symm

theorem levE_square_zero {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (levComplex F a) q) : levE F a hn (n+q) (levE F a hn q x)=0 := by
  have h := BorelEvaluationLaws.levClassCup_assoc F a n n (topClass n hn) (topClass n hn) q x
  rw [topClass_cup_self, levClassCup_zero, LinearMap.zero_apply] at h
  simpa only [levE,map_zero] using h.symm

theorem levClassCup_forget {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) (q : ℕ) (x : HR (levComplex F a) q) :
    BorelComparison.forgetNative (levPair F a) (revPair F a) (revPair_sq F a) (p+q)
      (levClassCup F a p s q x)=RelativeCup.cup (levPair F a) p q (eLev F a p s)
        (BorelComparison.forgetNative (levPair F a) (revPair F a) (revPair_sq F a) q x) := by
  have h := levCup_forget F a p (classRepr (sphere n) p s) (classRepr_isCocycle (sphere n) p s) q x
  change _ = RelativeCup.cup (levPair F a) p q (eLev F a p (cocycleClass (sphere n) p _ _)) _ at h
  rw [cocycleClass_classRepr] at h
  exact h

theorem fullE_forget (n : ℕ) (hn : 1≤n) (q : ℕ) (x : HR (fullComplex n) q) :
    BorelComparison.forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) (n+q) (fullE n hn q x)=
      RelativeCup.cup (fullPair n) n q (eFullTop n hn)
        (BorelComparison.forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) q x) :=
  fullClassCup_forget n (topClass n hn) q x

theorem levE_forget {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n)
    (q : ℕ) (x : HR (levComplex F a) q) :
    BorelComparison.forgetNative (levPair F a) (revPair F a) (revPair_sq F a) (n+q) (levE F a hn q x)=
      RelativeCup.cup (levPair F a) n q (eLevTop F a hn)
        (BorelComparison.forgetNative (levPair F a) (revPair F a) (revPair_sq F a) q x) :=
  levClassCup_forget F a n (topClass n hn) q x

theorem eFullTop_cup_self (n : ℕ) (hn : 1≤n) : cupZMod2 (eFullTop n hn) (eFullTop n hn)=0 := by
  rw [eFullTop,eFull,←Cup.naturality,topClass_cup_self,map_zero]

theorem eLevTop_cup_self {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (hn : 1≤n) :
    cupZMod2 (eLevTop F a hn) (eLevTop F a hn)=0 := by
  rw [eLevTop,eLev,←Cup.naturality,topClass_cup_self,map_zero]
end
end Finsler.BorelCanonicalEvaluation
