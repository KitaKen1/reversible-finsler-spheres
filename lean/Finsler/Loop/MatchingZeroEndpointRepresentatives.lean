module

public import Finsler.Loop.NativeMatchingPairEmbedding
public import Finsler.Loop.NativeMatchingTransgression
public import Finsler.Loop.MatchingRelativeOutputEndpointTrace

/-! Identify the actual nonadjacent matching time-ZERO endpoints,
with the real native clocks and pauses. The retained loop is a single
meridian with front pause; the tested loop is the original two-meridian
concatenation with back pause. Actual pause homotopies remove these.
No time-one alignment or endpoint-trace cancellation is claimed. -/
@[expose] public section
namespace Finsler.MatchingZeroEndpointRepresentatives
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.ClosedLoopReparametrization Finsler.NativeMeridianMatchingLoci
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def singleClosed {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.of (equator P) ⟶ TopCat.of (ClosedPathCircle.closedMaps (Sphere n)) :=
  TopCat.ofHom ⟨fun v => ClosedPathCircle.ofPath (loop P v₀ v),
    (ClosedPathCircle.ofPath_continuous P).comp (loop_continuous P v₀)⟩

def doubleClosed {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    MatchingRelativeOutputEndpointTrace.source P ⟶ TopCat.of (ClosedPathCircle.closedMaps (Sphere n)) :=
  BasedMeridianProducts.doubleFamily P v₀ ≫ TopCat.ofHom ⟨ClosedPathCircle.ofPath, ClosedPathCircle.ofPath_continuous P⟩

def retained {n : ℕ} (P : Sphere n) (v₀ : equator P) : TopCat.of (equator P) ⟶ ContinuousLoopModel.space n :=
  DoubleRelativeTimeCylinder.atTime (TopCat.of (equator P)) 0 ≫ NativeMatchingRetainedFactors.nonadjacent P v₀

def tested {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    MatchingRelativeOutputEndpointTrace.source P ⟶ ContinuousLoopModel.space n :=
  DoubleRelativeTimeCylinder.atTime (MatchingRelativeOutputEndpointTrace.source P) 0 ≫ NativeMatchingAdjacentFactors.testedMap P v₀ 1

theorem retained_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    retained P v₀ = singleClosed P v₀ ≫ circleMap n late := by
  ext v : 1
  apply ContinuousMap.ext
  intro a
  change NativeMatchingRetainedFactors.retainedMap P v₀ 1 (0, (v, v₀)) a =
    ClosedPathCircle.circle (warp late (ClosedPathCircle.ofPath (loop P v₀ v))) a
  rw [NativeMatchingRetainedFactors.retained_value]
  let u := late.val (SobolevCircleRepresentative.circlePoint a)
  have hp : NativeMatchingRetainedFactors.phase 1 0 (SobolevCircleRepresentative.circlePoint a) = (1 + (u : ℝ)) / 2 := by
    dsimp [NativeMatchingRetainedFactors.phase, rotationTime, cutTime, pairLeft, pairRight, legClock, u]
    ring
  rw [hp, NativeMatchingAdjacentFactors.native_circle_extend P v₀ _ _
    (by constructor <;> linarith [u.property.1, u.property.2])]
  change (((loop P v₀ v).trans (loop P v₀ v₀)).trans (loop P v₀ v)).extend ((1 + (u : ℝ)) / 2) = _
  rw [Path.extend_trans_of_half_le _ _ (by linarith [u.property.1]),
    show 2 * ((1 + (u : ℝ)) / 2) - 1 = (u : ℝ) by ring, ClosedPathCircle.circle_apply]
  exact Path.extend_apply _ u.property

theorem tested_factor {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    tested P v₀ = doubleClosed P v₀ ≫ circleMap n early := by
  ext z : 1
  apply ContinuousMap.ext
  intro a
  change NativeMatchingAdjacentFactors.testedMap P v₀ 1 (0, z) a =
    ClosedPathCircle.circle (warp early (ClosedPathCircle.ofPath ((loop P v₀ z.1).trans (loop P v₀ z.2)))) a
  rw [NativeMatchingAdjacentFactors.tested_value]
  let u := early.val (SobolevCircleRepresentative.circlePoint a)
  have hp : NativeMatchingAdjacentFactors.phase 1 0 (SobolevCircleRepresentative.circlePoint a) = (u : ℝ) / 2 := by
    dsimp [NativeMatchingAdjacentFactors.phase, rotationTime, cutTime, pairLeft, pairRight, legClock, u]
    ring
  rw [hp, NativeMatchingAdjacentFactors.native_circle_extend P v₀ _ _
    (by constructor <;> linarith [u.property.1, u.property.2])]
  change (((loop P v₀ z.1).trans (loop P v₀ z.2)).trans (loop P v₀ z.1)).extend ((u : ℝ) / 2) = _
  rw [Path.extend_trans_of_le_half _ _ (by linarith [u.property.2]),
    show 2 * ((u : ℝ) / 2) = (u : ℝ) by ring, ClosedPathCircle.circle_apply]
  exact Path.extend_apply _ u.property

theorem single_identity {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    singleClosed P v₀ ≫ circleMap n identity = ordinary P v₀ := by
  ext v : 1
  change ClosedPathCircle.circle (warp identity (ClosedPathCircle.ofPath (loop P v₀ v))) = _
  rw [warp_identity]
  rfl

theorem double_identity {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    doubleClosed P v₀ ≫ circleMap n identity = BasedMeridianProducts.doubleFamily P v₀ ≫ BasedMeridianProducts.forget P := by
  ext z : 1
  change ClosedPathCircle.circle (warp identity (ClosedPathCircle.ofPath ((loop P v₀ z.1).trans (loop P v₀ z.2)))) = _
  rw [warp_identity]
  rfl

def retainedHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (retained P v₀) (ordinary P v₀) := by
  rw [retained_factor, ← single_identity P v₀]
  exact (homotopy n late identity).comp (TopCat.Homotopy.refl (singleClosed P v₀))

def testedHomotopy {n : ℕ} (P : Sphere n) (v₀ : equator P) :
    TopCat.Homotopy (tested P v₀) (BasedMeridianProducts.doubleFamily P v₀ ≫ BasedMeridianProducts.forget P) := by
  rw [tested_factor, ← double_identity P v₀]
  exact (homotopy n early identity).comp (TopCat.Homotopy.refl (doubleClosed P v₀))

theorem retained_cohomology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (retained P v₀) q).hom a = (cohPullback (ordinary P v₀) q).hom a :=
  LoopSweepTwoPiece.cohomology_homotopy (retainedHomotopy P v₀) q a

theorem tested_cohomology {n : ℕ} (P : Sphere n) (v₀ : equator P) (q : ℕ)
    (a : cohomologyZMod2 (ContinuousLoopModel.space n) q) :
    (cohPullback (tested P v₀) q).hom a =
      (cohPullback (BasedMeridianProducts.doubleFamily P v₀ ≫ BasedMeridianProducts.forget P) q).hom a :=
  LoopSweepTwoPiece.cohomology_homotopy (testedHomotopy P v₀) q a

end
end Finsler.MatchingZeroEndpointRepresentatives
