module

public import Finsler.Topology.SupportedSelfCut
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Every actual compact continuous H1 loop family has one positive time
collar at both endpoints on which the self-evaluation distance is below
any fixed positive inner radius. The collar may depend on the finite
parameter family; no uniform collar on the entire loop space is asserted. -/

@[expose] public section
namespace Finsler.UniformSelfCutCollar

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SelfCutThomCocycle
open Finsler.SupportedSelfCut Finsler.H1FiberBase
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X : Type*} [PseudoMetricSpace X] {n : ℕ}

def jointDistance (u : C(X, SphereLoop n)) (z : ClosedInterval × X) : ℝ := distance n (z.1, u z.2)

theorem continuous_jointDistance (u : C(X, SphereLoop n)) : Continuous (jointDistance u) :=
  (continuous_distance n).comp (continuous_fst.prodMk (u.continuous.comp continuous_snd))

theorem distance_zero (u : C(X, SphereLoop n)) (x : X) : jointDistance u (0, x) = 0 := by
  change ‖(point (u x) : Ambient n) - point (u x)‖ = 0
  rw [sub_self, norm_zero]

theorem distance_one (u : C(X, SphereLoop n)) (x : X) : jointDistance u (1, x) = 0 := by
  change ‖(sphereRepresentative (u x) 1 : Ambient n) - sphereRepresentative (u x) 0‖ = 0
  exact (congrArg (fun y : Sphere n => ‖(y : Ambient n) - sphereRepresentative (u x) 0‖)
    (sphereRepresentative_endpoints (u x))).trans
      ((congrArg (fun v : Ambient n => ‖v‖) (sub_self (sphereRepresentative (u x) 0 : Ambient n))).trans norm_zero)

theorem exists_collar [CompactSpace X] (u : C(X, SphereLoop n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a > 0, a < 1 / 2 ∧ ∀ (t : ClosedInterval) (x : X),
      ((t : ℝ) < a ∨ 1 - a < (t : ℝ)) → jointDistance u (t, x) ≤ δ := by
  have hu := CompactSpace.uniformContinuous_of_continuous (continuous_jointDistance u)
  obtain ⟨b, hb, hbound⟩ := Metric.uniformContinuous_iff.mp hu δ hδ
  let a := min (b / 2) (1 / 4 : ℝ)
  have ha : 0 < a := lt_min (half_pos hb) (by norm_num)
  have hab : a ≤ b / 2 := min_le_left _ _
  have haq : a ≤ (1 / 4 : ℝ) := min_le_right _ _
  refine ⟨a, ha, by linarith, ?_⟩
  intro t x ht
  rcases ht with ht | ht
  · have hin : dist (t, x) ((0 : ClosedInterval), x) < b := by
      rw [dist_prod_same_right]
      change |(t : ℝ) - 0| < b
      rw [sub_zero, abs_of_nonneg t.property.1]
      linarith
    have hout := hbound hin
    rw [Real.dist_eq, distance_zero, sub_zero] at hout
    exact (le_abs_self _).trans hout.le
  · have hin : dist (t, x) ((1 : ClosedInterval), x) < b := by
      rw [dist_prod_same_right]
      change |(t : ℝ) - 1| < b
      rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
      linarith
    have hout := hbound hin
    rw [Real.dist_eq, distance_one, sub_zero] at hout
    exact (le_abs_self _).trans hout.le

end
end Finsler.UniformSelfCutCollar
