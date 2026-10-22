module

public import Finsler.Loop.H1PolygonReplacementHomotopy
public import Finsler.Loop.H1BasedFiberTransport

/-! The existing actual Milnor deformation preserves the exact H1
basepoint. Its polygon endpoint is a path endpoint in the original
based strong-H1 space. Actual ordinary polygon approximations also
preserve their exact sampled basepoint. -/
@[expose] public section
namespace Finsler.H1BasedPolygonHomotopy
open CategoryTheory Topology TopologicalSpace
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.CompactH1Alignment
open Finsler.H1LocalFiber (based)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem sample_zero {n N : ℕ} (u : SphereLoop n) :
    (samplePoly N u 0 : Ambient n) = basepoint u := by
  change continuousRepresentative (u.data : Space n) (sampleTime N 0) =
    continuousRepresentative (u.data : Space n) 0
  congr 1
  simp [sampleTime]

theorem broken_basepoint {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (M : PolygonModelData F a N) (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q}) :
    basepoint (PolygonModel.broken M q) = (q.val 0 : Ambient n) := by
  rw [← sample_zero (N := N)]
  exact congrArg (fun v : ZMod N → Sphere n => (v 0 : Ambient n)) (PolygonModel.sample_broken M q)

theorem deform_basepoint {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (M : PolygonModelData F a N) (u : SphereLoop n) (hu : SobolevEnergy.energy F u < a ^ 2)
    (t : _root_.unitInterval) : basepoint (PolygonModel.deform M ((t : ℝ), u)) = basepoint u :=
  MilnorContinuity.trace_milnorH F M.seg M.space ⟨t.property, hu⟩

def replacement {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (y : Sphere n) (M : PolygonModelData F a N) (u : based y)
    (hu : SobolevEnergy.energy F u.val < a ^ 2) : based y :=
  ⟨PolygonModel.broken M ⟨samplePoly N u.val, PolygonModel.sample_short M hu⟩, by
    change basepoint (PolygonModel.broken M _) = (y : Ambient n)
    rw [broken_basepoint]
    exact (sample_zero u.val).trans u.property⟩

def path {n : ℕ} {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N]
    (y : Sphere n) (M : PolygonModelData F a N) (u : based y)
    (hu : SobolevEnergy.energy F u.val < a ^ 2) : Path u (replacement y M u hu) where
  toFun t := ⟨PolygonModel.deform M ((t : ℝ), u.val), (deform_basepoint M u.val hu t).trans u.property⟩
  continuous_toFun := by
    have hc : Continuous (fun t : _root_.unitInterval => PolygonModel.deform M ((t : ℝ), u.val)) :=
      (PolygonModel.deform_continuousOn M).comp_continuous
        (continuous_subtype_val.prodMk continuous_const) (fun t => ⟨t.property, hu⟩)
    exact hc.subtype_mk _
  source' := Subtype.ext (PolygonModel.deform_zero M hu)
  target' := Subtype.ext (PolygonModel.deform_one M hu)

theorem approximation_basepoint {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (K : Compacts (ContinuousLoopModel.space n)) (N : ℕ) [NeZero N]
    (hshort : ∀ v : K, ShortPolygon S.δ (CompactContinuousLoopSampling.sample N v.val)) (u : K) :
    basepoint (CompactContinuousLoopPolygon.approximation S K N hshort u) = (u.val 0 : Ambient n) := by
  have hs := congrArg (fun v : ZMod N → Sphere n => (v 0 : Ambient n))
    (CompactContinuousLoopPolygon.sample_approximation S K N hshort u)
  rw [sample_zero] at hs
  simpa only [CompactContinuousLoopSampling.sample, sampleTime, ZMod.val_zero, Nat.cast_zero,
    zero_div, AddCircle.coe_zero] using hs

end
end Finsler.H1BasedPolygonHomotopy
