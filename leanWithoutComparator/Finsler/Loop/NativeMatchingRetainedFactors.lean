module

public import Finsler.Loop.NativeMatchingAdjacentFactors

/-! In the NONADJACENT matching pair02, the ORIGINAL retained loop
is independent of the middle meridian. All three matching families
retain exactly the original moving meridian evaluation point. -/
@[expose] public section
namespace Finsler.NativeMatchingRetainedFactors
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevCircleRepresentative
open Finsler.MeridianLoopFamily Finsler.NativeTripleSelfEvaluation Finsler.NativeMeridianMatchingLoci
open Finsler.ClosedLoopReparametrization Finsler.NativeMatchingAdjacentFactors
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

local notation "I" => ClosedInterval

def retainedMap {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    parameters P ⟶ ContinuousLoopModel.space n :=
  intoDiagonal P v₀ b ≫ DiagonalSelfCutRepresentatives.retained n

def phase (b : Fin 3) (s t : I) : ℝ :=
  (rotationTime b s : ℝ) + (cutTime b s : ℝ) + (1 - (cutTime b s : ℝ)) * (late.val t : ℝ)

theorem retained_value {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3)
    (z : parameters P) (a : SobolevCircleRepresentative.Circle) :
    retainedMap P v₀ b z a =
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2))
        ((phase b z.1 (circlePoint a) : ℝ) : SobolevCircleRepresentative.Circle) := by
  have hf := congrArg
    (fun k : DiagonalSelfCutRepresentatives.domain n ⟶ ContinuousLoopModel.space n =>
      k (intoDiagonal P v₀ b z) a) (DiagonalSelfCutRepresentatives.retained_factor n)
  calc
    _ = ClosedPathCircle.circle
        (warp late (DiagonalSelfCutRepresentatives.suffixClosed (intoDiagonal P v₀ b z))) a := hf
    _ = sphereRepresentative
        (SobolevShift.shiftSphere (NativeH1TripleMeridian.native P v₀ (repeated b z.2.1 z.2.2)) (rotationTime b z.1 : ℝ))
        (DiagonalSelfCutRepresentatives.suffixTime (cutTime b z.1) (late.val (circlePoint a))) := by
      rw [ClosedPathCircle.circle_apply]
      rfl
    _ = _ := by
      rw [endpoint_shift, ← AddCircle.coe_add]
      congr 1
      congr 1
      change (rotationTime b z.1 : ℝ) +
        ((cutTime b z.1 : ℝ) + (1 - (cutTime b z.1 : ℝ)) * (late.val (circlePoint a) : ℝ)) = _
      unfold phase
      ring

theorem before_quarter {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : p ≤ 1 / 4) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 1 v w)) (p : SobolevCircleRepresentative.Circle) =
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 1 v w')) (p : SobolevCircleRepresentative.Circle) := by
  rw [native_circle_extend P v₀ _ p hp, native_circle_extend P v₀ _ p hp]
  change (((loop P v₀ v).trans (loop P v₀ w)).trans (loop P v₀ v)).extend p =
    (((loop P v₀ v).trans (loop P v₀ w')).trans (loop P v₀ v)).extend p
  rw [Path.extend_trans_of_le_half _ _ (by linarith : p ≤ 1 / 2),
    Path.extend_trans_of_le_half _ _ (by linarith : p ≤ 1 / 2),
    Path.extend_trans_of_le_half _ _ (by linarith : 2 * p ≤ 1 / 2),
    Path.extend_trans_of_le_half _ _ (by linarith : 2 * p ≤ 1 / 2)]

theorem after_half {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (hh : 1 / 2 ≤ p) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 1 v w)) (p : SobolevCircleRepresentative.Circle) =
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 1 v w')) (p : SobolevCircleRepresentative.Circle) := by
  rw [native_circle_extend P v₀ _ p hp, native_circle_extend P v₀ _ p hp]
  change (((loop P v₀ v).trans (loop P v₀ w)).trans (loop P v₀ v)).extend p =
    (((loop P v₀ v).trans (loop P v₀ w')).trans (loop P v₀ v)).extend p
  exact (Path.extend_trans_of_half_le _ _ hh).trans (Path.extend_trans_of_half_le _ _ hh).symm

theorem exterior_phases {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P)
    (p : ℝ) (hp : 1 / 2 ≤ p) (hq : p ≤ 1 + 1 / 4) :
    sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 1 v w)) (p : SobolevCircleRepresentative.Circle) =
      sphereCircleMap (NativeH1TripleMeridian.native P v₀ (repeated 1 v w')) (p : SobolevCircleRepresentative.Circle) := by
  by_cases h1 : p ≤ 1
  · exact after_half P v₀ v w w' p ⟨by linarith, h1⟩ hp
  · have he : ((p : ℝ) : SobolevCircleRepresentative.Circle) =
        ((p - 1 : ℝ) : SobolevCircleRepresentative.Circle) := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    rw [he]
    exact before_quarter P v₀ v w w' (p - 1) ⟨by linarith, by linarith⟩ (by linarith)

theorem phase_bounds (s t : I) : 1 / 2 ≤ phase 1 s t ∧ phase 1 s t ≤ 1 + 1 / 4 := by
  have hc := (cutTime 1 s).property
  have ht := (late.val t).property
  have hm := mul_nonneg (sub_nonneg.mpr hc.2) ht.1
  have hM := mul_le_of_le_one_right (sub_nonneg.mpr hc.2) ht.2
  have hs := s.property
  have he : (rotationTime 1 s : ℝ) + (cutTime 1 s : ℝ) = (2 + (s : ℝ)) / 4 := by
    dsimp [rotationTime, cutTime, pairLeft, pairRight, legClock]
    ring
  constructor
  · unfold phase
    rw [he]
    linarith [s.property.1]
  · dsimp [phase, rotationTime, cutTime, pairLeft, pairRight, legClock] at *
    linarith [s.property.2]

theorem nonadjacent_independent {n : ℕ} (P : Sphere n) (v₀ v w w' : equator P) (s : I) :
    retainedMap P v₀ 1 (s, (v, w)) = retainedMap P v₀ 1 (s, (v, w')) := by
  apply ContinuousMap.ext
  intro a
  rw [retained_value, retained_value]
  exact exterior_phases P v₀ v w w' _ (phase_bounds s (circlePoint a)).1 (phase_bounds s (circlePoint a)).2

def nonadjacent {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (I × equator P) ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => retainedMap P v₀ 1 (z.1, (z.2, v₀)),
    (retainedMap P v₀ 1).hom.continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))⟩

theorem nonadjacent_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    retainedMap P v₀ 1 = reducedProjection P ≫ nonadjacent P v₀ := by
  ext z : 1
  exact nonadjacent_independent P v₀ z.2.1 z.2.2 v₀ z.1

theorem retained_evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) (z : parameters P) :
    retainedMap P v₀ b z 0 = meridian P z.2.1 z.1 := by
  have h0 := sphereCircleMap_coe (right (DiagonalSelfCutRepresentatives.intoTube (intoDiagonal P v₀ b z))) 0
  change retainedMap P v₀ b z 0 = _ at h0
  have hb := basepoint_right (DiagonalSelfCutRepresentatives.intoTube (intoDiagonal P v₀ b z))
  have hp := congrArg Prod.fst (NativeMeridianMatchingLoci.selfEvaluation n P v₀ b z)
  change point (NativeMeridianMatchingLoci.intoCut P v₀ b z).2 = meridian P z.2.1 z.1 at hp
  have hs : sphereRepresentative
      (right (DiagonalSelfCutRepresentatives.intoTube (intoDiagonal P v₀ b z))) 0 =
        point (NativeMeridianMatchingLoci.intoCut P v₀ b z).2 := by
    apply Subtype.ext
    exact hb
  exact h0.trans (hs.trans hp)

end
end Finsler.NativeMatchingRetainedFactors
