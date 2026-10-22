module

public import Finsler.Loop.ClosedPathCircle
public import Finsler.Loop.H1BasedFiberTransport
public import Finsler.Loop.NativeSphereSimplyConnected

/-! The genuine based fiber of ordinary circle loops, the actual H1
inclusion, and actual paths of based ordinary loops obtained from
endpoint-fixed path homotopies. -/
@[expose] public section
namespace Finsler.BasedContinuousLoopModel
open CategoryTheory Topology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.SobolevCircleRepresentative Finsler.CompactH1Alignment Finsler.H1FiberBase
open Finsler.H1LocalFiber (based)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
local notation "Circ" => SobolevCircleRepresentative.Circle

abbrev space {n : ℕ} (y : Sphere n) : TopCat.{0} :=
  TopCat.of {u : ContinuousLoopModel.space n // u 0 = y}

theorem evaluation_H1 {n : ℕ} (u : SphereLoop n) : ContinuousLoopModel.inclusion n u 0 = point u := by
  change sphereCircleMap u 0 = sphereRepresentative u 0
  simpa using sphereCircleMap_coe u (0 : ClosedInterval)

def inclusion {n : ℕ} (y : Sphere n) : TopCat.of (based y) ⟶ space y :=
  TopCat.ofHom ⟨fun u => ⟨ContinuousLoopModel.inclusion n u.val,
    (evaluation_H1 u.val).trans (Subtype.ext u.property)⟩,
    ((ContinuousLoopModel.inclusion n).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def constant {n : ℕ} (y : Sphere n) : space y := ⟨ContinuousLoopModel.constantMap n y, rfl⟩

def intervalPath {n : ℕ} (y : Sphere n) (u : space y) : Path y y where
  toFun t := u.val ((t : ℝ) : Circ)
  continuous_toFun := u.val.continuous.comp ((AddCircle.continuous_mk' 1).comp continuous_subtype_val)
  source' := by simpa using u.property
  target' := by change u.val ((1 : ℝ) : Circ) = y; rw [AddCircle.coe_period]; exact u.property

def ofPath {n : ℕ} (y : Sphere n) (γ : Path y y) : space y :=
  ⟨ClosedPathCircle.circle (ClosedPathCircle.ofPath γ), by
    have h := ClosedPathCircle.circle_coe (ClosedPathCircle.ofPath γ) (0 : _root_.unitInterval)
    simpa using h.trans γ.source⟩

theorem ofPath_continuous {n : ℕ} (y : Sphere n) : Continuous (ofPath y) :=
  (ClosedPathCircle.path_circle_continuous y).subtype_mk _

theorem ofPath_intervalPath {n : ℕ} (y : Sphere n) (u : space y) : ofPath y (intervalPath y u) = u := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro c
  rw [show (ofPath y (intervalPath y u)).val c =
    (intervalPath y u) (circlePoint c) from ClosedPathCircle.circle_apply _ c]
  exact congrArg u.val (circlePoint_coe c)

theorem ofPath_refl {n : ℕ} (y : Sphere n) : ofPath y (Path.refl y) = constant y := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro c
  exact ClosedPathCircle.circle_apply _ c

def pathOfHomotopy {n : ℕ} (y : Sphere n) {γ δ : Path y y} (H : Path.Homotopy γ δ) :
    Path (ofPath y γ) (ofPath y δ) where
  toFun t := ofPath y (H.eval t)
  continuous_toFun := (ofPath_continuous y).comp (continuous_induced_rng.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ H.toHomotopy.continuous))
  source' := by rw [H.eval_zero]
  target' := by rw [H.eval_one]

theorem joined_constant {n : ℕ} (hn : 2 ≤ n) (y : Sphere n) (u : space y) :
    Joined u (constant y) := by
  have hs : SimplyConnectedSpace (Sphere n) := TauCeti.simplyConnectedSpace_sphere_euclideanSpace hn
  obtain ⟨H⟩ := (simply_connected_iff_loops_nullhomotopic.mp hs).2 y (intervalPath y u)
  have h : Joined (ofPath y (intervalPath y u)) (ofPath y (Path.refl y)) := ⟨pathOfHomotopy y H⟩
  simpa only [ofPath_intervalPath, ofPath_refl] using h

theorem pathConnected {n : ℕ} (hn : 2 ≤ n) (y : Sphere n) : PathConnectedSpace (space y) :=
  ⟨⟨constant y⟩, fun u v => (joined_constant hn y u).trans (joined_constant hn y v).symm⟩

end
end Finsler.BasedContinuousLoopModel
