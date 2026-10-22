module

public import Finsler.Topology.JoinedTimeSplit
public import Finsler.Topology.DegreeLoweringAdd
public import Finsler.Topology.AnnularTrimHomology

/-! The two genuine joined-half operations descend and their sum is the
existing annular operation on the actual joined loop family. No filtered
comparison bounds or full cut-join interchange are asserted. -/

@[expose] public section
namespace Finsler.JoinedHalfOperations

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X : Type} [TopologicalSpace X] {n : ℕ}

private theorem distance_end (v : SphereLoop n) (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    distance n (t, v) = 0 := by
  rcases ht with rfl | rfl
  · change ‖(H1FiberBase.point v : Ambient n) - H1FiberBase.point v‖ = 0
    rw [sub_self, norm_zero]
  · change ‖(sphereRepresentative v 1 : Ambient n) - sphereRepresentative v 0‖ = 0
    exact (congrArg (fun y : Sphere n => ‖(y : Ambient n) - sphereRepresentative v 0‖)
      (sphereRepresentative_endpoints v)).trans
        ((congrArg (fun w : Ambient n => ‖w‖)
          (sub_self (sphereRepresentative v 0 : Ambient n))).trans norm_zero)

theorem first_endpoint (u : C(X, H1JoinContinuity.composable n))
    (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (x : X) :
    distance n (JoinedHalfCollars.firstFamily u (t, x)) = 0 := by
  change distance n (JoinedHalfCollars.first (t, u x)) = 0
  rw [JoinedHalfCollars.first_distance]
  exact distance_end _ t ht

theorem second_endpoint (u : C(X, H1JoinContinuity.composable n))
    (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (x : X) :
    distance n (JoinedHalfCollars.secondFamily u (t, x)) = 0 := by
  change distance n (JoinedHalfCollars.second (t, u x)) = 0
  rw [JoinedHalfCollars.second_distance]
  exact distance_end _ t ht

section
variable (m p : ℕ) {δ ρ r : ℝ}
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (u : C(X, H1JoinContinuity.composable (m + 1)))

def firstOperation : DegreeLoweringHomology.Map (chains (TopCat.of X))
    (chains (TopCat.of (SphereLoop (m + 1)))) (m + p) :=
  AnnularTrimHomology.operation m p h hρr hr T hT (JoinedHalfCollars.firstFamily u)
    (fun x => (first_endpoint u 0 (Or.inl rfl) x).trans_le h.1.le)
    (fun x => (first_endpoint u 1 (Or.inr rfl) x).trans_le h.1.le)

def secondOperation : DegreeLoweringHomology.Map (chains (TopCat.of X))
    (chains (TopCat.of (SphereLoop (m + 1)))) (m + p) :=
  AnnularTrimHomology.operation m p h hρr hr T hT (JoinedHalfCollars.secondFamily u)
    (fun x => (second_endpoint u 0 (Or.inl rfl) x).trans_le h.1.le)
    (fun x => (second_endpoint u 1 (Or.inr rfl) x).trans_le h.1.le)

theorem first_component (q : ℕ) :
    (firstOperation m p h hρr hr T hT u).component q =
      AnnularTimeTrim.component m p h hρr hr T hT (JoinedHalfCollars.firstFamily u) q := rfl

theorem second_component (q : ℕ) :
    (secondOperation m p h hρr hr T hT u).component q =
      AnnularTimeTrim.component m p h hρr hr T hT (JoinedHalfCollars.secondFamily u) q := rfl

theorem homology_split (q : ℕ) :
    ((AnnularCutComparison.operation m p h hρr hr T hT).pre
      (push (TopCat.ofHom (JoinedTimeSplit.loopFamily u)))).homology q =
      (firstOperation m p h hρr hr T hT u).homology q +
      (secondOperation m p h hρr hr T hT u).homology q := by
  apply DegreeLoweringAdd.homology_eq_sum_of_cycle_boundary _ _ _ q
    (AnnularTimeSplit.comparison m p h hρr hr T hT (JoinedTimeSplit.fullCylinder u) q)
  change (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
    ((push (TopCat.ofHom (JoinedTimeSplit.loopFamily u))).f ((m + p) + q) ≫
      (AnnularCutComparison.operation m p h hρr hr T hT).component q -
      ((firstOperation m p h hρr hr T hT u).component q +
        (secondOperation m p h hρr hr T hT u).component q)) = _
  rw [first_component, second_component, Preadditive.comp_sub, Preadditive.comp_add,
    JoinedTimeSplit.full_split]
  abel

end
end
end Finsler.JoinedHalfOperations
