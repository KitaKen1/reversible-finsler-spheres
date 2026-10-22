module

public import Finsler.Loop.NativeMeridianPairCoordinates
public import Finsler.Loop.PuncturedEquatorCohomology

/-! On ANY actual independent-time native pair family avoiding the
fixed equator direction in BOTH moving factors, the ORIGINAL rotated
triple-loop transgression reduces to the remaining primitive. This
uses the real TauCeti punctured-equator contraction, not an assumed
matching diagonal or local cap multiplicity. -/
@[expose] public section
namespace Finsler.NativePairPrimitiveLocalization
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BasedMeridianProducts
open Finsler.NativeMeridianPairCoordinates Finsler.NativeMatchingTransgression
open Finsler.SobolevCircleRepresentative Finsler.SobolevShift
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

def firstDirection {n : ℕ} (P : Sphere n) : parameters P ⟶ TopCat.of (equator P) :=
  TopCat.ofHom ⟨fun z => z.1.2, continuous_fst.snd⟩
def secondDirection {n : ℕ} (P : Sphere n) : parameters P ⟶ TopCat.of (equator P) :=
  TopCat.ofHom ⟨fun z => z.2.1.2, continuous_snd.fst.snd⟩
def remainingDirection {n : ℕ} (P : Sphere n) : parameters P ⟶ TopCat.of (equator P) :=
  TopCat.ofHom ⟨fun z => z.2.2, continuous_snd.snd⟩

def underlyingPath {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : parameters P ⟶ space P :=
  TopCat.ofHom ⟨fun z => tripleFamily P v₀ (assembly b z.1.2 z.2.1.2 z.2.2), by
    have hc := (tripleFamily P v₀).hom.continuous.comp (intoSource P b).hom.continuous.snd.snd
    exact hc⟩
def underlying {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : parameters P ⟶ ContinuousLoopModel.space n :=
  underlyingPath P v₀ b ≫ forget P

def forgetParameter (n : ℕ) : SelfCutThomCocycle.parameters n ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap z.2, (sphereCircleMap_continuous n).comp continuous_snd⟩
def shifted {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) : parameters P ⟶ ContinuousLoopModel.space n :=
  intoCut P v₀ b ≫ forgetParameter n

theorem underlying_native {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    underlying P v₀ b z = sphereCircleMap (NativeH1TripleMeridian.native P v₀ (assembly b z.1.2 z.2.1.2 z.2.2)) := by
  apply ContinuousMap.ext
  intro a
  exact (NativeH1TripleMeridian.circle_value P v₀ (assembly b z.1.2 z.2.1.2 z.2.2) a).symm

def rotationHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    TopCat.Homotopy (underlying P v₀ b) (shifted P v₀ b) where
  toFun z := OrdinaryLoopRotation.rotate n
    ((((z.1 : ℝ) * (NativeMeridianMatchingLoci.rotationTime b z.2.1.1 : ℝ)) : ℝ) : SobolevCircleRepresentative.Circle)
    (underlying P v₀ b z.2)
  continuous_toFun := by
    have ht : Continuous (fun z : _root_.unitInterval × parameters P =>
      (z.1 : ℝ) * (NativeMeridianMatchingLoci.rotationTime b z.2.1.1 : ℝ)) := by
      fin_cases b <;> dsimp [NativeMeridianMatchingLoci.rotationTime,
        NativeMeridianMatchingLoci.pairLeft, NativeMeridianMatchingLoci.legClock] <;> fun_prop
    exact (OrdinaryLoopRotation.joint_continuous n).comp
      (((underlying P v₀ b).hom.continuous.comp continuous_snd).prodMk ((AddCircle.continuous_mk' 1).comp ht))
  map_zero_left z := by
    change OrdinaryLoopRotation.rotate n (((0 : ℝ) * (NativeMeridianMatchingLoci.rotationTime b z.1.1 : ℝ) : ℝ) : SobolevCircleRepresentative.Circle) _ = _
    rw [zero_mul, AddCircle.coe_zero, OrdinaryLoopRotation.rotate_zero]
  map_one_left z := by
    change OrdinaryLoopRotation.rotate n (((1 : ℝ) * (NativeMeridianMatchingLoci.rotationTime b z.1.1 : ℝ) : ℝ) : SobolevCircleRepresentative.Circle)
      (underlying P v₀ b z) = sphereCircleMap
        (shiftSphere (NativeH1TripleMeridian.native P v₀ (assembly b z.1.2 z.2.1.2 z.2.2))
          (NativeMeridianMatchingLoci.rotationTime b z.1.1 : ℝ))
    rw [one_mul, underlying_native, circleMap_shiftSphere]
    rfl

theorem underlying_transgression {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (underlying P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      ((cohPullback (firstDirection P ≫ ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a) +
        (cohPullback (secondDirection P ≫ ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a)) +
        (cohPullback (remainingDirection P ≫ ordinary P v₀) q).hom (ContinuousLoopSweep.transgression n q a) := by
  let V := firstDirection P ≫ family P v₀
  let W := secondDirection P ≫ family P v₀
  let R := remainingDirection P ≫ family P v₀
  let τ := ContinuousLoopSweep.transgression n q a
  fin_cases b
  · change (cohPullback (underlying P v₀ 0) q).hom τ = _
    have he : underlying P v₀ 0 = concat (concat V W) R ≫ forget P := by ext z : 1; rfl
    rw [he, concat_transgression, concat_transgression]
    rfl
  · change (cohPullback (underlying P v₀ 1) q).hom τ = _
    have he : underlying P v₀ 1 = concat (concat V R) W ≫ forget P := by ext z : 1; rfl
    rw [he, concat_transgression, concat_transgression]
    change ((cohPullback (V ≫ forget P) q).hom τ + (cohPullback (R ≫ forget P) q).hom τ) +
      (cohPullback (W ≫ forget P) q).hom τ =
        ((cohPullback (V ≫ forget P) q).hom τ + (cohPullback (W ≫ forget P) q).hom τ) +
          (cohPullback (R ≫ forget P) q).hom τ
    abel
  · change (cohPullback (underlying P v₀ 2) q).hom τ = _
    have he : underlying P v₀ 2 = concat (concat R V) W ≫ forget P := by ext z : 1; rfl
    rw [he, concat_transgression, concat_transgression]
    change ((cohPullback (R ≫ forget P) q).hom τ + (cohPullback (V ≫ forget P) q).hom τ) +
      (cohPullback (W ≫ forget P) q).hom τ =
        ((cohPullback (V ≫ forget P) q).hom τ + (cohPullback (W ≫ forget P) q).hom τ) +
          (cohPullback (R ≫ forget P) q).hom τ
    abel

theorem underlying_reduced {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    {X : TopCat.{0}} (f : X ⟶ parameters P)
    (h₁ : ∀ x, firstDirection P (f x) ≠ v₀) (h₂ : ∀ x, secondDirection P (f x) ≠ v₀)
    (q : ℕ) (hq : q ≠ 0) (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (f ≫ underlying P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (f ≫ (remainingDirection P ≫ ordinary P v₀)) q).hom (ContinuousLoopSweep.transgression n q a) := by
  let τ := ContinuousLoopSweep.transgression n q a
  have h₁z := PuncturedEquatorCohomology.primitive_pullback_zero P v₀ (f ≫ firstDirection P) h₁ q hq a
  have h₂z := PuncturedEquatorCohomology.primitive_pullback_zero P v₀ (f ≫ secondDirection P) h₂ q hq a
  have he := congrArg ((cohPullback f q).hom) (underlying_transgression P v₀ b q a)
  rw [map_add, map_add, ← pullback_comp, ← pullback_comp, ← pullback_comp, ← pullback_comp] at he
  simp only [Category.assoc] at h₁z h₂z
  rw [h₁z, h₂z, zero_add, zero_add] at he
  exact he

theorem shifted_reduced {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    {X : TopCat.{0}} (f : X ⟶ parameters P)
    (h₁ : ∀ x, firstDirection P (f x) ≠ v₀) (h₂ : ∀ x, secondDirection P (f x) ≠ v₀)
    (q : ℕ) (hq : q ≠ 0) (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (f ≫ shifted P v₀ b) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (f ≫ (remainingDirection P ≫ ordinary P v₀)) q).hom (ContinuousLoopSweep.transgression n q a) := by
  have hh := congrArg ((cohPullback f q).hom)
    (LoopSweepTwoPiece.cohomology_homotopy (rotationHomotopy P v₀ b) q (ContinuousLoopSweep.transgression n q a))
  rw [← pullback_comp, ← pullback_comp] at hh
  exact hh.symm.trans (underlying_reduced P v₀ b f h₁ h₂ q hq a)

end
end Finsler.NativePairPrimitiveLocalization
