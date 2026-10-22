module

public import Finsler.Topology.SelfCutShuffle
public import Finsler.Topology.DegreeLoweringSuccAlignment

/-! Genuine global first-Thom time operation before either tested
cochain is introduced. Both actual endpoint restrictions vanish. -/

@[expose] public section
namespace Finsler.GlobalThomTime
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)

def aligned := DegreeLoweringSuccAlignment.align m
  (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr) rfl

theorem comm (q : ℕ) : aligned m hρ hρr (q + 1) ≫
    (chains (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r))).d (q + 1) q =
    (chains (parameters (m + 1))).d (m + q + 2) (m + q + 1) ≫ aligned m hρ hρr q :=
  DegreeLoweringSuccAlignment.comm m _ rfl q

theorem endpoint (t : ClosedInterval)
    (ht : cochainPullback (atTime (m + 1) t) (m + 1)
      (NormalizedSelfCut.cocycle (m + 1) (by omega) hρ) = 0) (q : ℕ) :
    (push (atTime (m + 1) t)).f (m + q + 1) ≫ aligned m hρ hρr q = 0 :=
  DegreeLoweringSuccAlignment.pre_zero m _ rfl (push (atTime (m + 1) t)) q
    (SelfCutEndpoints.thom_atTime_zero (m + 1) q (by omega) hρ hρr t ht)

def operation := TimePrismDescent.operation (SelfCutTimePrism.chainHomotopy (m + 1)) m
  (aligned m hρ hρr) (comm m hρ hρr)
  (endpoint m hρ hρr 0 (NormalizedSelfCut.time_zero (m + 1) (by omega) hρ))
  (endpoint m hρ hρr 1 (NormalizedSelfCut.time_one (m + 1) (by omega) hρ))

theorem component (q : ℕ) : (operation m hρ hρr).component q =
    TimeShuffleComparison.rectangle (SelfCutTimePrism.cylinder (m + 1)) (m + q) ≫
      eqToHom (congrArg (chains (parameters (m + 1))).X
        (show m + q + 1 = (m + 1) + q by omega)) ≫
      (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component q := by
  rw [TimeShuffleComparison.rectangle_eq_prism]
  rfl

end
end Finsler.GlobalThomTime
