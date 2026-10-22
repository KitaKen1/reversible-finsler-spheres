module

public import Finsler.Loop.NativeInnerHalfIntervalComparison
public import Finsler.Loop.IntervalCupLeftProjection
public import Finsler.Loop.GeometricTimeCupInterval

/-! The suffix FULL inner interval is exactly the original nested inner
geometric time cup, retaining the normalized first GH factor. This is
an equality of actual near-tube cochains with the existing degree casts. -/
@[expose] public section
namespace Finsler.NativeSuffixFullTimeCup
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeIntervalGHTests Finsler.NativeInnerCutPullback
open Finsler.NativeInnerFullClock (tube space)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def leftBase : tube m hm F ⟶ Loops (m + 1) := TopCat.ofHom (SupportedSelfCut.tested (m + 1) (radiusLe m hm F))
def rightBase : tube m hm F ⟶ Loops (m + 1) := TopCat.ofHom (SupportedSelfCut.retained (m + 1) (radiusLe m hm F))

theorem second_parameter : (rightBase m hm F ▷ TopCat.I) ≫ (SelfCutTimePrism.cylinder (m + 1)).h =
    NativeInnerFullClock.second m hm F := rfl

theorem outside_parameter : CartesianMonoidalCategory.fst (tube m hm F) TopCat.I ≫ leftBase m hm F =
    NativeInnerFullClock.leftOutside m hm F := rfl

abbrev innerDegree := (m + NativeGHPowers.degree m b) + k

def innerTest : singularCochainGroup (ZMod 2) (space m hm F) (innerDegree m b k + 1) :=
  CochainDegreeTransport.pre (space m hm F)
    (show innerDegree m b k + 1 = (m + 1) + NativeSuffixTestOrder.restDegree m b k by dsimp [innerDegree, NativeSuffixTestOrder.restDegree]; omega)
    (NativeInnerFullClock.suffix m hm F b k E)

def outerTest := cochainPullback (leftBase m hm F) (NativeGHPowers.degree m a)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F a)

theorem outer_normalized : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (tube m hm F)) (outerTest m hm F a) :=
  SupportedCapIntervalLocal.normalized_pullback _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_normalized m hm F a)

theorem full_test : NativeInnerFullClock.test m hm F a b k E true =
    CupOne.cup (space m hm F) (NativeGHPowers.degree m a) (innerDegree m b k + 1) (index m a b k true + 1)
      (by dsimp [innerDegree, index, NativeSuffixTestOrder.index, NativeSuffixTestOrder.restDegree]; omega)
      (cochainPullback (CartesianMonoidalCategory.fst (tube m hm F) TopCat.I) _ (outerTest m hm F a))
      (innerTest m hm F b k E) := by
  unfold innerTest outerTest
  rw [NativeInnerRetainedComparison.cup_right_pre, ← pullback_comp, outside_parameter]
  rfl

theorem inner_integral : TimeTriangleSplit.interval (tube m hm F) (innerDegree m b k) ≫ innerTest m hm F b k E =
    cochainPullback (rightBase m hm F) (innerDegree m b k)
      (GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m b) (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F b) k E) := by
  rw [GeometricTimeCupInterval.pullback_interval, second_parameter]
  rfl

def nested : singularCochainGroup (ZMod 2) (tube m hm F) (index m a b k true) :=
  CupOne.cup (tube m hm F) (NativeGHPowers.degree m a) (innerDegree m b k) (index m a b k true)
    (by dsimp [innerDegree, index, NativeSuffixTestOrder.index, NativeSuffixTestOrder.restDegree]; omega)
    (outerTest m hm F a)
    (cochainPullback (rightBase m hm F) (innerDegree m b k)
      (GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m b) (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F b) k E))

theorem integral_nested : TimeTriangleSplit.interval (tube m hm F) (index m a b k true) ≫
    NativeInnerFullClock.test m hm F a b k E true = nested m hm F a b k E := by
  rw [full_test, IntervalCupLeftProjection.at_degree _ _ _ _ _ _ (outer_normalized m hm F a), inner_integral]
  rfl

theorem full_value_nested : NativeInnerHalfIntervalComparison.fullValue m hm F a b k E true =
    CochainDegreeTransport.pre (tube m hm F) (NativeInnerIntervalComparison.low_degree m hm a b k true)
      (nested m hm F a b k E) := by
  unfold NativeInnerHalfIntervalComparison.fullValue IntervalHalfScalarComparison.value NativeInnerHalfIntervalComparison.fullTest
  rw [← NativeGHRawTwoTimeComparison.interval_pre, integral_nested]

end
end Finsler.NativeSuffixFullTimeCup
