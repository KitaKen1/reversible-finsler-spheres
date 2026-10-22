module

public import Finsler.Loop.NativeMatchingRetainedFactors

/-! On EACH actual matching family the original full-loop
transgression is exactly the remaining meridian pullback: the two
repeated factors cancel over F2. Connect this to the ORIGINAL tested
and retained maps, including the nonadjacent retained factorization.
This is a genuine cohomology computation, not a Thom multiplicity. -/
@[expose] public section
namespace Finsler.NativeMatchingTransgression
open CategoryTheory MonoidalCategory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevCircleRepresentative Finsler.MeridianLoopFamily Finsler.NativeMeridianMatchingLoci
open Finsler.CochainComparison Finsler.BasedMeridianProducts Finsler.SobolevShift
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem pullback_comp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (q : ℕ) (a : cohomologyZMod2 Z q) :
    (cohPullback (f ≫ g) q).hom a = (cohPullback f q).hom ((cohPullback g q).hom a) :=
  ConcreteCategory.congr_hom ((singularCohomologyZMod2 q).map_comp g.op f.op) a

def pairPaths {n : ℕ} {P : Sphere n} {X : TopCat.{0}} (f g : X ⟶ space P) : X ⟶ space P ⊗ space P :=
  TopCat.ofHom ⟨fun x => (f x, g x), f.hom.continuous.prodMk g.hom.continuous⟩

def concat {n : ℕ} {P : Sphere n} {X : TopCat.{0}} (f g : X ⟶ space P) : X ⟶ space P :=
  pairPaths f g ≫ concatenate P

theorem concat_transgression {n : ℕ} (P : Sphere n) {X : TopCat.{0}} (f g : X ⟶ space P)
    (q : ℕ) (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (concat f g ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (f ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (g ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) := by
  have hl : pairPaths f g ≫ BasedLoopTransgressionPrimitive.left P = f ≫ forget P := by ext x : 1; rfl
  have hr : pairPaths f g ≫ BasedLoopTransgressionPrimitive.right P = g ≫ forget P := by ext x : 1; rfl
  change (cohPullback (pairPaths f g ≫ BasedLoopTransgressionPrimitive.joined P) q).hom _ = _
  rw [pullback_comp, BasedLoopTransgressionPrimitive.transgression_primitive, map_add,
    ← pullback_comp, ← pullback_comp, hl, hr]

def varying {n : ℕ} (P : Sphere n) (v₀ : equator P) : parameters P ⟶ space P :=
  TopCat.ofHom ⟨fun z => loop P v₀ z.2.1,
    (loop_continuous P v₀).comp continuous_snd.fst⟩

def remaining {n : ℕ} (P : Sphere n) (v₀ : equator P) : parameters P ⟶ space P :=
  TopCat.ofHom ⟨fun z => loop P v₀ z.2.2,
    (loop_continuous P v₀).comp continuous_snd.snd⟩

def underlyingPath {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : parameters P ⟶ space P :=
  TopCat.ofHom ⟨fun z => tripleFamily P v₀ (repeated b z.2.1 z.2.2), by
    have hc : Continuous (fun z : parameters P => repeated b z.2.1 z.2.2) :=
      continuous_snd.comp (continuous_snd.comp (intoSource P b).hom.continuous)
    exact (tripleFamily P v₀).hom.continuous.comp hc⟩

def underlying {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : parameters P ⟶ ContinuousLoopModel.space n :=
  underlyingPath P v₀ b ≫ forget P

theorem underlying_native {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    underlying P v₀ b z = sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2)) := by
  apply ContinuousMap.ext
  intro a
  exact (NativeH1TripleMeridian.circle_value P v₀ (repeated b z.2.1 z.2.2) a).symm

def source {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : parameters P ⟶ ContinuousLoopModel.space n :=
  intoDiagonal P v₀ b ≫ DiagonalCutRejoining.source n

def rotationHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    TopCat.Homotopy (underlying P v₀ b) (source P v₀ b) where
  toFun z := OrdinaryLoopRotation.rotate n
    ((((z.1 : ℝ) * (rotationTime b z.2.1 : ℝ)) : ℝ) : SobolevCircleRepresentative.Circle)
    (underlying P v₀ b z.2)
  continuous_toFun := by
    have ht : Continuous (fun z : _root_.unitInterval × parameters P =>
        (((z.1 : ℝ) * (rotationTime b z.2.1 : ℝ)) : ℝ)) := by
      fin_cases b <;> dsimp [rotationTime, pairLeft, legClock] <;> fun_prop
    exact (OrdinaryLoopRotation.joint_continuous n).comp
      (((underlying P v₀ b).hom.continuous.comp continuous_snd).prodMk ((AddCircle.continuous_mk' 1).comp ht))
  map_zero_left z := by
    change OrdinaryLoopRotation.rotate n (((0 : ℝ) * (rotationTime b z.1 : ℝ) : ℝ) : SobolevCircleRepresentative.Circle)
      (underlying P v₀ b z) = _
    rw [zero_mul, AddCircle.coe_zero, OrdinaryLoopRotation.rotate_zero]
  map_one_left z := by
    change OrdinaryLoopRotation.rotate n (((1 : ℝ) * (rotationTime b z.1 : ℝ) : ℝ) : SobolevCircleRepresentative.Circle)
      (underlying P v₀ b z) = sphereCircleMap
        (shiftSphere (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2)) (rotationTime b z.1 : ℝ))
    rw [one_mul, underlying_native, circleMap_shiftSphere]
    rfl

theorem underlying_transgression {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (underlying P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (remaining P v₀ ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) := by
  let V := varying P v₀
  let W := remaining P v₀
  let τ := ContinuousLoopSweep.transgression n q a
  have hz : (cohPullback (V ≫ forget P) q).hom τ + (cohPullback (V ≫ forget P) q).hom τ = 0 :=
    BorelCochain.two_eq_zero_of_mod _
  fin_cases b
  · change (cohPullback (underlying P v₀ 0) q).hom τ = (cohPullback (W ≫ forget P) q).hom τ
    have he : underlying P v₀ 0 = concat (concat V V) W ≫ forget P := by ext z : 1; rfl
    rw [he, concat_transgression, concat_transgression, hz, zero_add]
  · change (cohPullback (underlying P v₀ 1) q).hom τ = (cohPullback (W ≫ forget P) q).hom τ
    have he : underlying P v₀ 1 = concat (concat V W) V ≫ forget P := by ext z : 1; rfl
    rw [he, concat_transgression, concat_transgression]
    change ((cohPullback (V ≫ forget P) q).hom τ + (cohPullback (W ≫ forget P) q).hom τ) +
      (cohPullback (V ≫ forget P) q).hom τ = (cohPullback (W ≫ forget P) q).hom τ
    calc
      _ = ((cohPullback (V ≫ forget P) q).hom τ + (cohPullback (V ≫ forget P) q).hom τ) +
          (cohPullback (W ≫ forget P) q).hom τ := by abel
      _ = _ := by rw [hz, zero_add]
  · change (cohPullback (underlying P v₀ 2) q).hom τ = (cohPullback (W ≫ forget P) q).hom τ
    have he : underlying P v₀ 2 = concat (concat W V) V ≫ forget P := by ext z : 1; rfl
    rw [he, concat_transgression, concat_transgression]
    change ((cohPullback (W ≫ forget P) q).hom τ + (cohPullback (V ≫ forget P) q).hom τ) +
      (cohPullback (V ≫ forget P) q).hom τ = (cohPullback (W ≫ forget P) q).hom τ
    rw [add_assoc, hz, add_zero]

theorem source_transgression {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (source P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (remaining P v₀ ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) :=
  (LoopSweepTwoPiece.cohomology_homotopy (rotationHomotopy P v₀ b) q _).symm.trans
    (underlying_transgression P v₀ b q a)

theorem original_tested_retained_sum {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (NativeMatchingAdjacentFactors.testedMap P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (NativeMatchingRetainedFactors.retainedMap P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
    (cohPullback (remaining P v₀ ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) :=
  (NativeMeridianMatchingLoci.original_transgression_split n q P v₀ b a).symm.trans
    (source_transgression P v₀ b q a)

theorem original_tested_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (NativeMatchingAdjacentFactors.testedMap P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
    (cohPullback (remaining P v₀ ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (NativeMatchingRetainedFactors.retainedMap P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) := by
  let A := (cohPullback (NativeMatchingAdjacentFactors.testedMap P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a)
  let B := (cohPullback (NativeMatchingRetainedFactors.retainedMap P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a)
  have hz : B + B = 0 := BorelCochain.two_eq_zero_of_mod _
  calc
    _ = A + (B + B) := by rw [hz, add_zero]
    _ = (A + B) + B := (add_assoc _ _ _).symm
    _ = _ := congrArg (· + B) (original_tested_retained_sum P v₀ b q a)

theorem nonadjacent_tested_reduced {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (NativeMatchingAdjacentFactors.testedMap P v₀ 1) q).hom (ContinuousLoopSweep.transgression n q a) =
    (cohPullback (remaining P v₀ ≫ forget P) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (NativeMatchingAdjacentFactors.reducedProjection P ≫
        NativeMatchingRetainedFactors.nonadjacent P v₀) q).hom (ContinuousLoopSweep.transgression n q a) := by
  rw [original_tested_value, NativeMatchingRetainedFactors.nonadjacent_factor]

end
end Finsler.NativeMatchingTransgression
