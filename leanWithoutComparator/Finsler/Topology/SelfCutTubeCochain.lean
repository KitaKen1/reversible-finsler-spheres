module

public import Finsler.Topology.AdequateTubeCochain
public import Finsler.Topology.NormalizedSelfCut

/-! Instantiate the zero-extension calculus with the actual H1 self-cut,
normalized diagonal Thom cochain, and actual tested-loop map. Both time
endpoints vanish literally. Supported cup-boundary and cup-one error caps
vanish on the actual exterior/tube carrier, without global closure of the
extended tested cochain. -/

@[expose] public section
namespace Finsler.SelfCutTubeCochain

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (n p : ℕ) (hn : 1 ≤ n) {ρ r : ℝ} (hρ : 0 < ρ) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)

def gamma : singularCochainGroup (ZMod 2) (parameters n) (n + p) :=
  AdequateTubeCochain.gamma (parameters n) (neighborhood n r) n p
    (NormalizedSelfCut.cocycle n hn hρ) (NormalizedSelfCut.testedCocycle n p hr T)

theorem time_zero : cochainPullback (atTime n 0) (n + p) (gamma n p hn hρ hr T) = 0 := by
  change cochainPullback (atTime n 0) (n + p)
    (cochainCup n p (NormalizedSelfCut.cocycle n hn hρ) _) = 0
  rw [cochainCup_naturality, NormalizedSelfCut.time_zero, cochainCup_zero_left]

theorem time_one : cochainPullback (atTime n 1) (n + p) (gamma n p hn hρ hr T) = 0 := by
  change cochainPullback (atTime n 1) (n + p)
    (cochainCup n p (NormalizedSelfCut.cocycle n hn hρ) _) = 0
  rw [cochainCup_naturality, NormalizedSelfCut.time_one, cochainCup_zero_left]

theorem boundary_cap_zero
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (t m : ℕ) (h : (n + p + 1) + t = m)
    {c : coeff ⟶ (chains (parameters n)).X m}
    (hc : c ∈ supported (parameters n)
      (SupportedCap.cover (parameters n) (exterior n ρ) (neighborhood n r)) m) :
    c ≫ absoluteChain (parameters n) (n + p + 1) t m h
      (cochainCoboundary (ZMod 2) (parameters n) (n + p) (gamma n p hn hρ hr T)) = 0 :=
  AdequateTubeCochain.boundary_cap_zero (parameters n) (exterior n ρ) (neighborhood n r) n p
    (NormalizedSelfCut.cocycle n hn hρ) (NormalizedSelfCut.cocycle_closed n hn hρ)
    (NormalizedSelfCut.cocycle_supported n hn hρ) (NormalizedSelfCut.testedCocycle n p hr T)
    (NormalizedSelfCut.testedCocycle_closed n p hr T hT) t m h hc

theorem cupOne_error_cap_zero
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
    (a m t k : ℕ) (h : a + (n + p + 1) = m + 1) (hk : m + t = k)
    (σ : singularCochainGroup (ZMod 2) (parameters n) a)
    {c : coeff ⟶ (chains (parameters n)).X k}
    (hc : c ∈ supported (parameters n)
      (SupportedCap.cover (parameters n) (exterior n ρ) (neighborhood n r)) k) :
    c ≫ absoluteChain (parameters n) m t k hk
      (CupOne.cupOne (parameters n) a (n + p + 1) m h σ
        (cochainCoboundary (ZMod 2) (parameters n) (n + p) (gamma n p hn hρ hr T))) = 0 :=
  AdequateTubeCochain.cupOne_error_cap_zero (parameters n) (exterior n ρ) (neighborhood n r) n p
    (NormalizedSelfCut.cocycle n hn hρ) (NormalizedSelfCut.cocycle_closed n hn hρ)
    (NormalizedSelfCut.cocycle_supported n hn hρ) (NormalizedSelfCut.testedCocycle n p hr T)
    (NormalizedSelfCut.testedCocycle_closed n p hr T hT) a m t k h hk σ hc

end
end Finsler.SelfCutTubeCochain
