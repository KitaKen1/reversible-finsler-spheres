module

public import Finsler.Analysis.IntervalH1CircleRepresentative
public import Mathlib.Topology.Path
public import Mathlib.Topology.ContinuousMap.Compact

/-! Actual endpoint-matched interval maps descend continuously to
the project's AddCircle(1) loop model. The descent is Lipschitz in
the genuine compact-source uniform metrics and preserves every point,
including the endpoint seam. -/

@[expose] public section
namespace Finsler.ClosedPathCircle
open Topology Finsler.IntervalSobolev Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

local notation "Circ" => SobolevCircleRepresentative.Circle

abbrev closedMaps (X : Type*) [TopologicalSpace X] :=
  {f : C(_root_.unitInterval, X) // f 0 = f 1}

def path {X : Type*} [TopologicalSpace X] (f : closedMaps X) : Path (f.val 0) (f.val 0) where
  toFun := f.val
  continuous_toFun := f.val.continuous
  source' := rfl
  target' := f.property.symm

def circle {X : Type*} [TopologicalSpace X] (f : closedMaps X) : C(Circ, X) :=
  ⟨AddCircle.liftIco (1 : ℝ) 0 (path f).extend,
    AddCircle.liftIco_zero_continuous (by simp) (path f).continuous_extend.continuousOn⟩

theorem circle_apply {X : Type*} [TopologicalSpace X] (f : closedMaps X) (t : Circ) :
    circle f t = f.val (circlePoint t) := by
  change (path f).extend (circlePoint t : ℝ) = f.val (circlePoint t)
  rw [Path.extend_apply _ (circlePoint t).property]
  rfl

theorem circle_coe {X : Type*} [TopologicalSpace X] (f : closedMaps X) (t : _root_.unitInterval) :
    circle f ((t : ℝ) : Circ) = f.val t := by
  by_cases ht : (t : ℝ) = 1
  · have he : t = 1 := Subtype.ext ht
    subst t
    have hc : ((1 : ℝ) : Circ) = 0 := by exact_mod_cast AddCircle.coe_period (1 : ℝ)
    change circle f ((1 : ℝ) : Circ) = f.val 1
    rw [hc]
    have h0 := AddCircle.liftIco_zero_coe_apply (p := (1 : ℝ))
      (f := (path f).extend) (show (0 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    change AddCircle.liftIco (1 : ℝ) 0 (path f).extend 0 = f.val 1
    change AddCircle.liftIco (1 : ℝ) 0 (path f).extend (0 : Circ) = (path f).extend 0 at h0
    exact h0.trans ((path f).extend_zero.trans f.property)
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
    change AddCircle.liftIco (1 : ℝ) 0 (path f).extend ((t : ℝ) : Circ) = f.val t
    rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1, hlt⟩, Path.extend_apply _ t.property]
    rfl

theorem circle_lipschitz {X : Type*} [PseudoMetricSpace X] :
    LipschitzWith 1 (circle : closedMaps X → C(Circ, X)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  rw [circle_apply, circle_apply]
  exact ContinuousMap.dist_apply_le_dist (circlePoint t)

theorem circle_continuous {X : Type*} [PseudoMetricSpace X] :
    Continuous (circle : closedMaps X → C(Circ, X)) := circle_lipschitz.continuous

def ofPath {X : Type*} [TopologicalSpace X] {x : X} (γ : Path x x) : closedMaps X :=
  ⟨γ.toContinuousMap, γ.source.trans γ.target.symm⟩

theorem ofPath_continuous {X : Type*} [TopologicalSpace X] (x : X) :
    Continuous (ofPath : Path x x → closedMaps X) :=
  continuous_induced_dom.subtype_mk _

theorem path_circle_continuous {X : Type*} [PseudoMetricSpace X] (x : X) :
    Continuous (fun γ : Path x x => circle (ofPath γ)) :=
  circle_continuous.comp (ofPath_continuous x)

end
end Finsler.ClosedPathCircle
