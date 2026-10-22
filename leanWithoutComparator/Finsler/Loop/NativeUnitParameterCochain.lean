module

public import Finsler.Loop.NativeUnitOriginalCochain
public import Finsler.Loop.GlobalCutTimePrismAlignment

/-! The ORIGINAL pre-time first-Thom cut followed by the actual
tested factor and an arbitrary genuine constant-relative output.
Its original time prism is exactly the current UNIT test cochain. -/
@[expose] public section
namespace Finsler.NativeUnitParameterCochain
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

def output : singularCochainGroup (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) (m + (m + 1)) :=
  GeometricTimeCupCochain.splitCup m m hr (classRepr _ m (MeridianLoopClass.H1TransgressionClass m)) (m + 1)
    (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)

theorem output_closed : cochainCoboundary (ZMod 2) (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r))
    (m + (m + 1)) (output m hr a) = 0 :=
  cochainCupZMod2_respects_cocycles m (m + 1) _ _
    (NormalizedSelfCut.testedCocycle_closed (m + 1) m hr _ (classRepr_isCocycle _ m _))
    (pullback_closed _ _ _ (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a))

def cochain : singularCochainGroup (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) ((m + 1) + (m + (m + 1))) :=
  (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr).component (m + (m + 1)) ≫ output m hr a

theorem closed : cochainCoboundary (ZMod 2) (SelfCutThomCocycle.parameters (m + 1)) ((m + 1) + (m + (m + 1)))
    (cochain m hρ hρr hr a) = 0 :=
  DegreeLoweringCochainPullback.closed (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr) (m + (m + 1)) _ (output_closed m hr a)

theorem original_time_prism : NativeUnitOriginalCochain.cochain m hρ hρr hr a =
    SelfCutTimePrism.prism (m + 1) ((m + m) + (m + 1)) ≫
      CochainDegreeTransport.pre (SelfCutThomCocycle.parameters (m + 1))
        (by omega : ((m + m) + (m + 1)) + 1 = (m + 1) + (m + (m + 1))) (cochain m hρ hρr hr a) := by
  unfold NativeUnitOriginalCochain.cochain GeometricTimeCupCochain.cochain
  rw [TimeShuffleComparison.rectangle_eq_prism]
  rfl

end
end Finsler.NativeUnitParameterCochain
