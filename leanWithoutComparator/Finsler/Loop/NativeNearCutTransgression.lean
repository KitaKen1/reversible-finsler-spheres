module

public import Finsler.Loop.NativeNearCutRejoining
public import Finsler.Loop.CloseContinuousLoopHomotopy
public import Finsler.Loop.LoopSweepTwoPiece

/-! Genuine rejoining of the ORIGINAL near self-cut outputs, through
actual ordinary loop families. Evaluation transgression splits on the
whole fixed near tube, not merely on the exact coincidence locus. -/
@[expose] public section
namespace Finsler.NativeNearCutTransgression
open CategoryTheory MonoidalCategory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevCircleRepresentative
open Finsler.H1SelfCutNeighborhood Finsler.CochainComparison
open Finsler.ClosedLoopReparametrization Finsler.NativeNearCutRejoining
open Finsler.BasedLoopTransgressionPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
local notation "I" => ClosedInterval
local notation "Circ" => SobolevCircleRepresentative.Circle

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
  TopCat.ofHom ⟨fun z => sphereCircleMap (joined z),
    (sphereCircleMap_continuous n).comp (continuous_joined n)⟩

def tested (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap (left (input z)),
    (sphereCircleMap_continuous n).comp (continuous_left.comp (continuous_input n))⟩

def retained (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  TopCat.ofHom ⟨fun z => sphereCircleMap (right (input z)),
    (sphereCircleMap_continuous n).comp (continuous_right.comp (continuous_input n))⟩

def paused (n : ℕ) : domain n ⟶ ContinuousLoopModel.space n :=
  ClosedLoopVariableClocks.family n (fun z => NativeNearCutClocks.clock z.val.1)
    (NativeNearCutClocks.continuous_clock.comp (by fun_prop)) fullClosed (continuous_fullClosed n)

theorem rejoined_coe {n : ℕ} (z : domain n) (t : I) :
    rejoined n z ((t : ℝ) : Circ) = sphereRepresentative (joined z) t :=
  sphereCircleMap_coe (joined z) t

theorem paused_coe {n : ℕ} (z : domain n) (t : I) :
    paused n z ((t : ℝ) : Circ) =
      sphereRepresentative z.val.2 (NativeNearCutClocks.splice z.val.1 t) := by
  change ClosedPathCircle.circle (warp (NativeNearCutClocks.clock z.val.1) (fullClosed z))
    ((t : ℝ) : Circ) = _
  rw [ClosedPathCircle.circle_coe]
  rfl

theorem close (n : ℕ) (z : domain n) : dist (rejoined n z) (paused n z) < 1 := by
  apply (ContinuousMap.dist_lt_iff zero_lt_one).mpr
  intro a
  change dist (sphereCircleMap (joined z) a)
    (ClosedPathCircle.circle (warp (NativeNearCutClocks.clock z.val.1) (fullClosed z)) a) < 1
  rw [sphereCircleMap_point, ClosedPathCircle.circle_apply]
  exact uniformly_close z (circlePoint a)

def closingArcHomotopy (n : ℕ) : TopCat.Homotopy (rejoined n) (paused n) :=
  CloseContinuousLoopHomotopy.homotopy (rejoined n) (paused n) (close n)

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

def unpausingHomotopy (n : ℕ) : TopCat.Homotopy (paused n) (source n) := by
  rw [← source_factor]
  exact ClosedLoopVariableClocks.homotopy n (X := domain n)
    (fun z => NativeNearCutClocks.clock z.val.1) (fun _ => identity)
    (NativeNearCutClocks.continuous_clock.comp (by fun_prop)) continuous_const
    fullClosed (continuous_fullClosed n)

def rejoiningHomotopy (n : ℕ) : TopCat.Homotopy (rejoined n) (source n) :=
  (closingArcHomotopy n).trans (unpausingHomotopy n)

theorem first_timeMap (n : ℕ) :
    UncappedTimeSplit.first (timeMap (rejoined n)) = timeMap (tested n) := by
  ext z : 1
  change rejoined n z.1 (((IntervalTriangle.firstMap z.2).down : ℝ) : Circ) =
    sphereCircleMap (left (input z.1)) ((z.2.down : ℝ) : Circ)
  rw [rejoined_coe, sphereCircleMap_coe]
  exact joined_first z.1 z.2.down

theorem second_timeMap (n : ℕ) :
    UncappedTimeSplit.second (timeMap (rejoined n)) = timeMap (retained n) := by
  ext z : 1
  change rejoined n z.1 (((IntervalTriangle.secondMap z.2).down : ℝ) : Circ) =
    sphereCircleMap (right (input z.1)) ((z.2.down : ℝ) : Circ)
  rw [rejoined_coe, sphereCircleMap_coe]
  exact joined_second z.1 z.2.down

theorem original_transgression_split (n q : ℕ)
    (a : cohomologyZMod2 (BorelEvaluation.sphere n) (q + 1)) :
    (cohPullback (source n) q).hom (ContinuousLoopSweep.transgression n q a) =
      (cohPullback (tested n) q).hom (ContinuousLoopSweep.transgression n q a) +
      (cohPullback (retained n) q).hom (ContinuousLoopSweep.transgression n q a) := by
  have hj := LoopSweepTwoPiece.cohomology_homotopy (rejoiningHomotopy n) q
    (ContinuousLoopSweep.transgression n q a)
  exact hj.symm.trans (LoopSweepTwoPiece.transgression_split (rejoined n) (tested n) (retained n)
    (first_timeMap n) (second_timeMap n) q a)

end
end Finsler.NativeNearCutTransgression
