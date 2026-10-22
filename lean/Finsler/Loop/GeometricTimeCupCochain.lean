module

public import Finsler.Topology.SelfCutShuffle
public import Finsler.Topology.RelativeCapDual
public import Finsler.Loop.DegreeLoweringCochainPullback

/-! A geometric time-cut cochain defined by the actual split pullbacks,
ordinary cup, supported Thom cut and genuine time rectangle. Its pairing
with the actual prism self-cut is a theorem, not its definition. -/

@[expose] public section
namespace Finsler.GeometricTimeCupCochain
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.SupportedSelfCut
open Finsler.RelativeCapAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable (m p : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (q : ℕ) (B : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q)

def splitCup : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) (p + q) :=
  cochainCup p q (NormalizedSelfCut.testedCocycle (m + 1) p hr T)
    (cochainPullback (TopCat.ofHom (retained (m + 1) hr)) q B)

def cochain : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) ((m + p) + q) :=
  TimeShuffleComparison.rectangle (SelfCutTimePrism.cylinder (m + 1)) ((m + p) + q) ≫
    eqToHom (congrArg (chains (SelfCutThomCocycle.parameters (m + 1))).X
      (show (m + p) + q + 1 = (m + 1) + (p + q) by omega)) ≫
    (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (p + q) ≫
    splitCup m p hr T q B

theorem tested_cap_dual
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q ≫ B = splitCup m p hr T q B := by
  change absoluteChain (TopCat.of (neighborhood (m + 1) r)) p q (p + q) rfl
    (NormalizedSelfCut.testedCocycle (m + 1) p hr T) ≫
    ((push (TopCat.ofHom (retained (m + 1) hr))).f q ≫ B) = _
  exact RelativeCapDual.absolute_chain_dual (TopCat.of (neighborhood (m + 1) r)) p q
    (NormalizedSelfCut.testedCocycle (m + 1) p hr T)
    (cochainPullback (TopCat.ofHom (retained (m + 1) hr)) q B)

theorem operation_dual
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) :
    (PrismSelfCut.operation m p hρ hρr hr T hT).component q ≫ B = cochain m p hρ hρr hr T q B := by
  rw [SelfCutShuffle.operation_eq_shuffle, PrismSelfCut.cut, NormalizedSelfCut.chainCut, cochain]
  simp only [Category.assoc]
  rw [tested_cap_dual]

theorem closed
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) ((m + p) + q)
      (cochain m p hρ hρr hr T q B) = 0 := by
  have h := DegreeLoweringCochainPullback.closed (PrismSelfCut.operation m p hρ hρr hr T hT) q B hB
  simpa only [DegreeLoweringCochainPullback.cochain, operation_dual] using h

theorem pairing
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hB : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) q B = 0)
    (z : PoolCap.homology (TopCat.of (SphereLoop (m + 1))) ((m + p) + q)) :
    (kroneckerMap (TopCat.of (SphereLoop (m + 1))) ((m + p) + q)).hom
      (cocycleClass _ _ (cochain m p hρ hρr hr T q B) (closed m p hρ hρr hr T q B hT hB)) z =
    (kroneckerMap (TopCat.of (SphereLoop (m + 1))) q).hom (cocycleClass _ q B hB)
      (((PrismSelfCut.operation m p hρ hρr hr T hT).homology q).hom z) := by
  have h := DegreeLoweringCochainPullback.pairing (PrismSelfCut.operation m p hρ hρr hr T hT) q B hB z
  have hc : DegreeLoweringCochainPullback.cochain (PrismSelfCut.operation m p hρ hρr hr T hT) q B =
      cochain m p hρ hρr hr T q B := operation_dual m p hρ hρr hr T q B hT
  have he := cocycleClass_congr (TopCat.of (SphereLoop (m + 1))) ((m + p) + q) hc
    (DegreeLoweringCochainPullback.closed (PrismSelfCut.operation m p hρ hρr hr T hT) q B hB)
    (closed m p hρ hρr hr T q B hT hB)
  exact (congrArg
    (fun c : cohomologyZMod2 (TopCat.of (SphereLoop (m + 1))) ((m + p) + q) =>
      (kroneckerMap _ ((m + p) + q)).hom c z) he).symm.trans h

end
end Finsler.GeometricTimeCupCochain
