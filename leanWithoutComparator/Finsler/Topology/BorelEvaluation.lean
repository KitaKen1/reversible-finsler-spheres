module

public import Finsler.Topology.BorelCup
public import Finsler.Topology.BorelLoopComparison

/-! Evaluation at zero of the actual periodic strong H¹ sphere loop. Evaluation is
continuous, strictly reflection-invariant, and compatible with full/cut inclusions.
Pullback of any sphere class and the reflection-equivariant evaluation action
using a fixed cocycle representative are constructed. Canonical nonzero sphere
top-class construction and representative-independent left module laws are not
asserted in this module. -/

@[expose] public section

namespace Finsler.BorelEvaluation
open CategoryTheory SphereOddDegree Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.BorelLoop Finsler.BorelCochain Finsler.BorelPair
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
abbrev sphere (n : ℕ) : TopCat.{0} := TopCat.of (Finsler.SphereGeometry.Sphere n)
def zero : ClosedInterval := ⟨0, by norm_num⟩

/-- Evaluation at the actual H¹ continuous representative. -/
def eval (n : ℕ) : C(SphereLoop n, Finsler.SphereGeometry.Sphere n) :=
  ⟨fun u => sphereRepresentative u zero, by
    have h := (traceL n zero).continuous.comp (sphereLoop_data_isometry n).continuous
    exact h.subtype_mk _⟩

theorem eval_reverse {n : ℕ} (u : SphereLoop n) : eval n (reverseSphere u) = eval n u := by
  change sphereRepresentative (reverseSphere u) zero = sphereRepresentative u zero
  rw [sphereRepresentative_reverseSphere]
  have ht : reflectionInterval zero = (⟨1, by norm_num⟩ : ClosedInterval) := by
    apply Subtype.ext
    norm_num [reflectionInterval, reflection, zero]
  rw [ht]
  exact sphereRepresentative_endpoints u

theorem eval_constant {n : ℕ} (x : Finsler.SphereGeometry.Sphere n) :
    eval n (constantSphereLoop x) = x := sphereRepresentative_constantSphereLoop x zero

def fullEval (n : ℕ) : (fullPair n).fst ⟶ sphere n :=
  TopCat.ofHom ⟨fun u => eval n u.val, (eval n).continuous.comp continuous_subtype_val⟩

def levEval {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) :
    (levPair F a).fst ⟶ sphere n :=
  TopCat.ofHom ⟨fun u => eval n u.val, (eval n).continuous.comp continuous_subtype_val⟩

theorem fullEval_invariant (n : ℕ) : TopPair.Hom.fst (revFullPair n) ≫ fullEval n = fullEval n := by
  ext u : 1
  exact eval_reverse u.val

theorem levEval_invariant {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) :
    TopPair.Hom.fst (revPair F a) ≫ levEval F a = levEval F a := by
  ext u : 1
  exact eval_reverse u.val

theorem res_eval {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) :
    TopPair.Hom.fst (resPair F a) ≫ fullEval n = levEval F a := by
  ext u
  rfl

theorem cut_eval {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b) :
    TopPair.Hom.fst (cutPair F hab) ≫ levEval F b = levEval F a := by
  ext u
  rfl

theorem cochain_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) Z p) :
    cochainPullback f p (cochainPullback g p α) = cochainPullback (f≫g) p α := by
  have h := congrArg (fun φ => (φ.f p).hom α) (singularCochainComplexZMod2.map_comp g.op f.op)
  exact h.symm

theorem cochain_invariant {P : TopPair.{0}} (r : P ⟶ P) {Y : TopCat.{0}} (f : P.fst ⟶ Y)
    (hf : TopPair.Hom.fst r ≫ f = f) (p : ℕ) (α : singularCochainGroup (ZMod 2) Y p) :
    cochainPullback (TopPair.Hom.fst r) p (cochainPullback f p α) = cochainPullback f p α := by
  rw [cochain_comp, hf]

/-- Evaluation pullback of an actual sphere class; the canonical nonzero top class is separate. -/
def eFull (n p : ℕ) (s : cohomologyZMod2 (sphere n) p) : cohomologyZMod2 (fullPair n).fst p :=
  (cohPullback (fullEval n) p).hom s

def eLev {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) : cohomologyZMod2 (levPair F a).fst p :=
  (cohPullback (levEval F a) p).hom s

theorem e_res {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) :
    (cohPullback (TopPair.Hom.fst (resPair F a)) p).hom (eFull n p s) = eLev F a p s := by
  rw [eFull, ← Finsler.Cup.pullback_comp, res_eval]
  rfl

theorem e_cut {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) :
    (cohPullback (TopPair.Hom.fst (cutPair F hab)) p).hom (eLev F b p s) = eLev F a p s := by
  rw [eLev, ← Finsler.Cup.pullback_comp, cut_eval]
  rfl

/-- Actual reflection-equivariant evaluation cup for a closed sphere cochain. -/
def fullCup (n p : ℕ) (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α = 0) (q : ℕ) :
    HR (fullComplex n) q →ₗ[ZMod 2] HR (fullComplex n) (p+q) :=
  BorelCup.cup (fullPair n) (revFullPair n) (revFullPair_sq n) p
    (cochainPullback (fullEval n) p α) (cochainPullback_cocycle _ _ _ hα)
    (cochain_invariant _ _ (fullEval_invariant n) p α) q

def levCup {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α = 0) (q : ℕ) :
    HR (levComplex F a) q →ₗ[ZMod 2] HR (levComplex F a) (p+q) :=
  BorelCup.cup (levPair F a) (revPair F a) (revPair_sq F a) p
    (cochainPullback (levEval F a) p α) (cochainPullback_cocycle _ _ _ hα)
    (cochain_invariant _ _ (levEval_invariant F a) p α) q
theorem fullCup_res {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0) (q : ℕ) (x : HR (fullComplex n) q) :
    HRmap (resHom F a) (p+q) (fullCup n p α hα q x) =
      levCup F a p α hα q (HRmap (resHom F a) q x) := by
  apply BorelCup.cup_natural
  rw [cochain_comp, res_eval]

theorem levCup_cut {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0) (q : ℕ) (x : HR (levComplex F b) q) :
    HRmap (cutHom F hab) (p+q) (levCup F b p α hα q x) =
      levCup F a p α hα q (HRmap (cutHom F hab) q x) := by
  apply BorelCup.cup_natural
  rw [cochain_comp, cut_eval]

theorem classOf_pull {X Y : TopCat.{0}} (f : X ⟶ Y) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) Y p) (hα : cochainCoboundary (ZMod 2) Y p α=0) :
    CochainClass.classOf (cochainCxZMod2 X) p (cochainPullback f p α)
      (cochainPullback_cocycle f p α hα) =
    (cohPullback f p).hom (CochainClass.classOf (cochainCxZMod2 Y) p α hα) := by
  exact (cohPullback_cocycleClass f p α hα).symm

theorem fullCup_forget {n : ℕ} (p : ℕ) (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0) (q : ℕ) (x : HR (fullComplex n) q) :
    BorelComparison.forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) (p+q)
      (fullCup n p α hα q x) =
    RelativeCup.cup (fullPair n) p q (eFull n p (CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα))
      (BorelComparison.forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) q x) := by
  rw [fullCup, BorelCup.cup_forgetNative, classOf_pull]
  rfl

theorem levCup_forget {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (α : singularCochainGroup (ZMod 2) (sphere n) p)
    (hα : cochainCoboundary (ZMod 2) (sphere n) p α=0) (q : ℕ) (x : HR (levComplex F a) q) :
    BorelComparison.forgetNative (levPair F a) (revPair F a) (revPair_sq F a) (p+q)
      (levCup F a p α hα q x) =
    RelativeCup.cup (levPair F a) p q (eLev F a p (CochainClass.classOf (cochainCxZMod2 (sphere n)) p α hα))
      (BorelComparison.forgetNative (levPair F a) (revPair F a) (revPair_sq F a) q x) := by
  rw [levCup, BorelCup.cup_forgetNative, classOf_pull]
  rfl

/-- Evaluation action using the library's fixed representative of the sphere class.
No independence from a different representative or left module law is claimed here. -/
def fullClassCup (n p : ℕ) (s : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    HR (fullComplex n) q →ₗ[ZMod 2] HR (fullComplex n) (p+q) :=
  fullCup n p (classRepr (sphere n) p s) (classRepr_isCocycle (sphere n) p s) q

def levClassCup {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) (q : ℕ) :
    HR (levComplex F a) q →ₗ[ZMod 2] HR (levComplex F a) (p+q) :=
  levCup F a p (classRepr (sphere n) p s) (classRepr_isCocycle (sphere n) p s) q

theorem fullClassCup_res {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (a : ℝ) (p : ℕ)
    (s : cohomologyZMod2 (sphere n) p) (q : ℕ) (x : HR (fullComplex n) q) :
    HRmap (resHom F a) (p+q) (fullClassCup n p s q x) =
      levClassCup F a p s q (HRmap (resHom F a) q x) := fullCup_res F a p _ _ q x

theorem levClassCup_cut {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) {a b : ℝ} (hab : a≤b)
    (p : ℕ) (s : cohomologyZMod2 (sphere n) p) (q : ℕ) (x : HR (levComplex F b) q) :
    HRmap (cutHom F hab) (p+q) (levClassCup F b p s q x) =
      levClassCup F a p s q (HRmap (cutHom F hab) q x) := levCup_cut F hab p _ _ q x

theorem fullClassCup_forget {n : ℕ} (p : ℕ) (s : cohomologyZMod2 (sphere n) p)
    (q : ℕ) (x : HR (fullComplex n) q) :
    BorelComparison.forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) (p+q)
      (fullClassCup n p s q x) =
    RelativeCup.cup (fullPair n) p q (eFull n p s)
      (BorelComparison.forgetNative (fullPair n) (revFullPair n) (revFullPair_sq n) q x) := by
  have h := fullCup_forget p (classRepr (sphere n) p s) (classRepr_isCocycle (sphere n) p s) q x
  change _ = RelativeCup.cup (fullPair n) p q (eFull n p (cocycleClass (sphere n) p _ _)) _ at h
  rw [cocycleClass_classRepr] at h
  exact h

end
end Finsler.BorelEvaluation
