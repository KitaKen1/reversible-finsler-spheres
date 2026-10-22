module

public import Finsler.Loop.NativeMeridianMatchingLoci

/-! On the TWO ADJACENT matching-meridian families, the ORIGINAL
tested loop is independent of the remaining meridian parameter.
This is a pointwise factorization of the genuine cut map, not a
claim that its eventual relative Thom contribution is zero. -/
@[expose] public section
namespace Finsler.NativeMatchingAdjacentFactors
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevCircleRepresentative
open Finsler.MeridianLoopFamily Finsler.NativeTripleSelfEvaluation Finsler.NativeMeridianMatchingLoci
open Finsler.ClosedLoopReparametrization
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

local notation "I" => ClosedInterval

def testedMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ ContinuousLoopModel.space n :=
  intoDiagonal P v₀ b ≫ DiagonalSelfCutRepresentatives.tested n

def phase (b : Fin 3) (s t : I) : ℝ :=
  (rotationTime b s : ℝ) + (cutTime b s : ℝ) * (early.val t : ℝ)

theorem phase_mem (b : Fin 3) (s t : I) : phase b s t ∈ Set.Icc (0 : ℝ) 1 := by
  have hr := (rotationTime b s).property
  have hc := (cutTime b s).property
  have he := (early.val t).property
  have hb := legClock_mem (pairRight b) s
  have hsum : (rotationTime b s : ℝ) + (cutTime b s : ℝ) = legClock (pairRight b) s := by
    change legClock (pairLeft b) s + (legClock (pairRight b) s - legClock (pairLeft b) s) = _
    ring
  constructor
  · exact add_nonneg hr.1 (mul_nonneg hc.1 he.1)
  · have hm := mul_le_of_le_one_right hc.1 he.2
    dsimp [phase]
    linarith [hb.2]

theorem tested_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (z : parameters P) (a : SobolevCircleRepresentative.Circle) :
    testedMap P v₀ b z a =
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2))
        ((phase b z.1 (circlePoint a) : ℝ) : SobolevCircleRepresentative.Circle) := by
  have hf := congrArg
    (fun k : DiagonalSelfCutRepresentatives.domain n ⟶ ContinuousLoopModel.space n =>
      k (intoDiagonal P v₀ b z) a) (DiagonalSelfCutRepresentatives.tested_factor n)
  calc
    _ = ClosedPathCircle.circle
        (warp early (DiagonalSelfCutRepresentatives.prefixClosed (intoDiagonal P v₀ b z))) a := hf
    _ = sphereRepresentative
        (SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2)) (rotationTime b z.1 : ℝ))
        (DiagonalSelfCutRepresentatives.prefixTime (cutTime b z.1) (early.val (circlePoint a))) := by
      rw [ClosedPathCircle.circle_apply]
      rfl
    _ = _ := by
      rw [endpoint_shift, ← AddCircle.coe_add]
      rfl

theorem native_circle_extend {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : NativeH1TripleMeridian.parameters P) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ z) (p : SobolevCircleRepresentative.Circle) =
      (NativeH1TripleMeridian.triplePath P v₀ z).extend p := by
  rw [NativeH1TripleMeridian.circle_value]
  exact (ClosedPathCircle.circle_coe _ ⟨p, hp⟩).trans (Path.extend_apply _ hp).symm

theorem before_half {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hh : p ≤ 1 / 2) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 0 v w)) (p : SobolevCircleRepresentative.Circle) =
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 0 v w')) (p : SobolevCircleRepresentative.Circle) := by
  rw [native_circle_extend P v₀ _ p hp, native_circle_extend P v₀ _ p hp]
  change (((loop P v₀ v).trans (loop P v₀ v)).trans (loop P v₀ w)).extend p =
    (((loop P v₀ v).trans (loop P v₀ v)).trans (loop P v₀ w')).extend p
  exact (Path.extend_trans_of_le_half _ _ hh).trans (Path.extend_trans_of_le_half _ _ hh).symm

theorem after_quarter {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : 1 / 4 ≤ p) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 2 v w)) (p : SobolevCircleRepresentative.Circle) =
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 2 v w')) (p : SobolevCircleRepresentative.Circle) := by
  rw [native_circle_extend P v₀ _ p hp, native_circle_extend P v₀ _ p hp]
  change (((loop P v₀ w).trans (loop P v₀ v)).trans (loop P v₀ v)).extend p =
    (((loop P v₀ w').trans (loop P v₀ v)).trans (loop P v₀ v)).extend p
  by_cases hh : p ≤ 1 / 2
  · rw [Path.extend_trans_of_le_half _ _ hh, Path.extend_trans_of_le_half _ _ hh,
      Path.extend_trans_of_half_le _ _ (by linarith : 1 / 2 ≤ 2 * p),
      Path.extend_trans_of_half_le _ _ (by linarith : 1 / 2 ≤ 2 * p)]
  · exact (Path.extend_trans_of_half_le _ _ (le_of_not_ge hh)).trans
      (Path.extend_trans_of_half_le _ _ (le_of_not_ge hh)).symm

theorem phase_before_half (s t : I) : phase 0 s t ≤ 1 / 2 := by
  have ht := (early.val t).property
  have he : phase 0 s t = (s : ℝ) / 8 + (1 / 4 : ℝ) * (early.val t : ℝ) := by
    dsimp [phase, rotationTime, cutTime, pairLeft, pairRight, legClock]
    ring
  rw [he]
  linarith [s.property.2, ht.2]

theorem phase_after_quarter (s t : I) : 1 / 4 ≤ phase 2 s t := by
  have ht := (early.val t).property
  have hc := (cutTime 2 s).property.1
  have hm := mul_nonneg hc ht.1
  dsimp [phase, rotationTime, cutTime, pairLeft, pairRight, legClock] at *
  linarith [s.property.1]

theorem adjacent01_independent {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P) (s : I) :
    testedMap P v₀ 0 (s, (v, w)) = testedMap P v₀ 0 (s, (v, w')) := by
  apply ContinuousMap.ext
  intro a
  rw [tested_value, tested_value]
  exact before_half P v₀ v w w' _ (phase_mem 0 s (circlePoint a)) (phase_before_half s (circlePoint a))

theorem adjacent12_independent {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P) (s : I) :
    testedMap P v₀ 2 (s, (v, w)) = testedMap P v₀ 2 (s, (v, w')) := by
  apply ContinuousMap.ext
  intro a
  rw [tested_value, tested_value]
  exact after_quarter P v₀ v w w' _ (phase_mem 2 s (circlePoint a)) (phase_after_quarter s (circlePoint a))

def reducedProjection {n : ℕ} (P : Sphere n) : parameters P ⟶ TopCat.of (I × equator P) :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.1), continuous_fst.prodMk continuous_snd.fst⟩

def adjacent01 {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (I × equator P) ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => testedMap P v₀ 0 (z.1, (z.2, v₀)),
    (testedMap P v₀ 0).hom.continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))⟩

def adjacent12 {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (I × equator P) ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => testedMap P v₀ 2 (z.1, (z.2, v₀)),
    (testedMap P v₀ 2).hom.continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))⟩

theorem adjacent01_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    testedMap P v₀ 0 = reducedProjection P ≫ adjacent01 P v₀ := by
  ext z : 1
  exact adjacent01_independent P v₀ z.2.1 z.2.2 v₀ z.1

theorem adjacent12_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    testedMap P v₀ 2 = reducedProjection P ≫ adjacent12 P v₀ := by
  ext z : 1
  exact adjacent12_independent P v₀ z.2.1 z.2.2 v₀ z.1

end
end Finsler.NativeMatchingAdjacentFactors
