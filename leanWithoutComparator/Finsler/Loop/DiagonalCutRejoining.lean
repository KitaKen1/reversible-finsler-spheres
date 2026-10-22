module

public import Finsler.Loop.DiagonalSelfCutRepresentatives
public import Finsler.Loop.ClosedLoopVariableClocks
public import Finsler.Loop.LoopSweepTwoPiece

/-! Rejoin the ACTUAL prefix/suffix of a self-coincident H1 loop.
The joint clock homotopy gives the original loop back, even at cut
times0/1. The original evaluation transgression splits into the
ORIGINAL tested and retained pullbacks on the real coincidence locus. -/
@[expose] public section
namespace Finsler.DiagonalCutRejoining
open CategoryTheory MonoidalCategory SphereOddDegree Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.H1SelfCutNeighborhood Finsler.H1FiberBase Finsler.SobolevCircleRepresentative
open Finsler.CochainComparison Finsler.ClosedLoopReparametrization Finsler.DiagonalSelfCutRepresentatives
open Finsler.BasedLoopTransgressionPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

local notation "I" => ClosedInterval

def splice (c t : I) : I := mix (unitInterval.symm c) (early.val t) (late.val t)

def clock (c : I) : clocks :=
  ⟨⟨splice c, by unfold splice mix early late; fun_prop⟩, by
    constructor
    · apply Subtype.ext
      change (1 - (1 - (c : ℝ))) * min (2 * 0) 1 + (1 - (c : ℝ)) * max (2 * 0 - 1) 0 = 0
      norm_num
    · apply Subtype.ext
      change (1 - (1 - (c : ℝ))) * min (2 * 1) 1 + (1 - (c : ℝ)) * max (2 * 1 - 1) 0 = 1
      norm_num⟩

theorem continuous_clock : Continuous clock := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : I × I => splice z.1 z.2)
  unfold splice mix early late
  fun_prop

theorem splice_first (c t : I) :
    splice c (IntervalTriangle.firstMap (ULift.up t)).down = prefixTime c t := by
  apply Subtype.ext
  change (1 - (1 - (c : ℝ))) * min (2 * ((t : ℝ) / 2)) 1 +
    (1 - (c : ℝ)) * max (2 * ((t : ℝ) / 2) - 1) 0 = (c : ℝ) * t
  rw [show 2 * ((t : ℝ) / 2) = (t : ℝ) by ring,
    min_eq_left t.property.2, max_eq_right (sub_nonpos.mpr t.property.2)]
  ring

theorem splice_second (c t : I) :
    splice c (IntervalTriangle.secondMap (ULift.up t)).down = suffixTime c t := by
  apply Subtype.ext
  change (1 - (1 - (c : ℝ))) * min (2 * ((1 + (t : ℝ)) / 2)) 1 +
    (1 - (c : ℝ)) * max (2 * ((1 + (t : ℝ)) / 2) - 1) 0 =
      (c : ℝ) + (1 - (c : ℝ)) * t
  rw [show 2 * ((1 + (t : ℝ)) / 2) = 1 + (t : ℝ) by ring,
    show 1 + (t : ℝ) - 1 = (t : ℝ) by ring,
    min_eq_right (by linarith [t.property.1]), max_eq_left t.property.1]
  ring

def fullClosed {n : ℕ} (z : domain n) : ClosedPathCircle.closedMaps (Sphere n) :=
  ⟨⟨sphereRepresentative z.val.2, sphereRepresentative_continuous z.val.2⟩,
    (sphereRepresentative_endpoints z.val.2).symm⟩

theorem continuous_fullClosed (n : ℕ) : Continuous (fullClosed (n := n)) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hu : Continuous (fun z : domain n × I => z.1.val.2) := by fun_prop
  exact continuous_endpoint.comp (continuous_snd.prodMk hu)

def source (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap z.val.2,
    (sphereCircleMap_continuous n).comp (by fun_prop)⟩

def rejoined (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  ClosedLoopVariableClocks.family n (fun z => clock z.val.1)
    (continuous_clock.comp (by fun_prop)) fullClosed (continuous_fullClosed n)

def unpausedLeft (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  prefixFamily n ≫ circleMap n identity
def unpausedRight (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  suffixFamily n ≫ circleMap n identity

theorem source_factor (n : ℕ) :
    ClosedLoopVariableClocks.family n (fun _ : domain n => identity) continuous_const
      fullClosed (continuous_fullClosed n) = source n := by
  ext z : 1
  change ClosedPathCircle.circle (warp identity (fullClosed z)) = sphereCircleMap z.val.2
  rw [warp_identity]
  apply ContinuousMap.ext
  intro a
  rw [ClosedPathCircle.circle_apply, sphereCircleMap_point]
  rfl

def rejoiningHomotopy (n : ℕ) : TopCat.Homotopy (rejoined n) (source n) := by
  rw [← source_factor]
  exact ClosedLoopVariableClocks.homotopy n (X := domain n) (fun z => clock z.val.1) (fun _ => identity)
    (continuous_clock.comp (by fun_prop)) continuous_const fullClosed (continuous_fullClosed n)

theorem rejoined_coe {n : ℕ} (z : domain n) (t : I) :
    rejoined n z ((t : ℝ) : SobolevCircleRepresentative.Circle) =
      sphereRepresentative z.val.2 (splice z.val.1 t) := by
  change ClosedPathCircle.circle (warp (clock z.val.1) (fullClosed z)) ((t : ℝ) : SobolevCircleRepresentative.Circle) = _
  rw [ClosedPathCircle.circle_coe]
  rfl

theorem prefix_coe {n : ℕ} (z : domain n) (t : I) :
    unpausedLeft n z ((t : ℝ) : SobolevCircleRepresentative.Circle) =
      sphereRepresentative z.val.2 (prefixTime z.val.1 t) := by
  change ClosedPathCircle.circle (warp identity (prefixClosed z)) ((t : ℝ) : SobolevCircleRepresentative.Circle) = _
  rw [warp_identity, ClosedPathCircle.circle_coe]
  rfl

theorem suffix_coe {n : ℕ} (z : domain n) (t : I) :
    unpausedRight n z ((t : ℝ) : SobolevCircleRepresentative.Circle) =
      sphereRepresentative z.val.2 (suffixTime z.val.1 t) := by
  change ClosedPathCircle.circle (warp identity (suffixClosed z)) ((t : ℝ) : SobolevCircleRepresentative.Circle) = _
  rw [warp_identity, ClosedPathCircle.circle_coe]
  rfl

theorem first_timeMap (n : ℕ) :
    UncappedTimeSplit.first (timeMap (rejoined n)) = timeMap (unpausedLeft n) := by
  ext z : 1
  change rejoined n z.1 ((((IntervalTriangle.firstMap z.2).down : ℝ)) : SobolevCircleRepresentative.Circle) =
    unpausedLeft n z.1 (((z.2.down : ℝ)) : SobolevCircleRepresentative.Circle)
  rw [rejoined_coe, prefix_coe]
  exact congrArg (sphereRepresentative z.1.val.2) (splice_first z.1.val.1 z.2.down)

theorem second_timeMap (n : ℕ) :
    UncappedTimeSplit.second (timeMap (rejoined n)) = timeMap (unpausedRight n) := by
  ext z : 1
  change rejoined n z.1 ((((IntervalTriangle.secondMap z.2).down : ℝ)) : SobolevCircleRepresentative.Circle) =
    unpausedRight n z.1 (((z.2.down : ℝ)) : SobolevCircleRepresentative.Circle)
  rw [rejoined_coe, suffix_coe]
  exact congrArg (sphereRepresentative z.1.val.2) (splice_second z.1.val.1 z.2.down)

theorem original_transgression_split (n q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (source n) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (tested n) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (retained n) q).hom (ContinuousLoopSweep.transgression n q a) := by
  have hj := LoopSweepTwoPiece.cohomology_homotopy (rejoiningHomotopy n) q
    (ContinuousLoopSweep.transgression n q a)
  have hp := LoopSweepTwoPiece.cohomology_homotopy (testedHomotopy n) q
    (ContinuousLoopSweep.transgression n q a)
  have hs := LoopSweepTwoPiece.cohomology_homotopy (retainedHomotopy n) q
    (ContinuousLoopSweep.transgression n q a)
  have he := LoopSweepTwoPiece.transgression_split (rejoined n) (unpausedLeft n) (unpausedRight n)
    (first_timeMap n) (second_timeMap n) q a
  exact hj.symm.trans (he.trans (congrArg₂ (· + ·) hp.symm hs.symm))

end
end Finsler.DiagonalCutRejoining
