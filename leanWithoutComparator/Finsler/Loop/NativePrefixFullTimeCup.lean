module

public import Finsler.Loop.NativeSuffixFullTimeCup
public import Finsler.Loop.IntervalCupRightProjection

/-! The prefix FULL inner interval is exactly the original nested
inner geometric time cup when the retained output is normalized.
Every original outside map and source-degree cast is retained. -/
@[expose] public section
namespace Finsler.NativePrefixFullTimeCup
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeIntervalGHTests Finsler.NativeInnerCutPullback
open Finsler.NativeInnerFullClock (tube space)
open Finsler.NativeSuffixFullTimeCup (leftBase rightBase)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem first_parameter : (leftBase m hm F ▷ TopCat.I) ≫ (SelfCutTimePrism.cylinder (m + 1)).h =
    NativeInnerFullClock.first m hm F := rfl

theorem outside_parameter : CartesianMonoidalCategory.fst (tube m hm F) TopCat.I ≫ rightBase m hm F =
    NativeInnerFullClock.rightOutside m hm F := rfl

abbrev innerDegree := (m + NativeGHPowers.degree m a) + NativeGHPowers.degree m b

def innerTest : singularCochainGroup (ZMod 2) (space m hm F) (innerDegree m a b + 1) :=
  CochainDegreeTransport.pre (space m hm F)
    (show innerDegree m a b + 1 = (m + 1) + NativePrefixTestOrder.pairDegree m a b by
      dsimp [innerDegree, NativePrefixTestOrder.pairDegree]; omega)
    (NativeInnerFullClock.prefixValue m hm F a b)

def outerTest := cochainPullback (rightBase m hm F) k E

theorem outer_normalized (hE : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) E) :
    DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (tube m hm F)) (outerTest m hm F k E) :=
  SupportedCapIntervalLocal.normalized_pullback _ _ _ hE

theorem full_test : NativeInnerFullClock.test m hm F a b k E false =
    CupOne.cup (space m hm F) (innerDegree m a b + 1) k (index m a b k false + 1)
      (by dsimp [innerDegree, index, NativePrefixTestOrder.index, NativePrefixTestOrder.pairDegree]; omega)
      (innerTest m hm F a b)
      (cochainPullback (CartesianMonoidalCategory.fst (tube m hm F) TopCat.I) k (outerTest m hm F k E)) := by
  unfold innerTest outerTest
  rw [NativeInnerRetainedComparison.cup_left_pre, ← pullback_comp, outside_parameter]
  rfl

theorem inner_integral : TimeTriangleSplit.interval (tube m hm F) (innerDegree m a b) ≫ innerTest m hm F a b =
    cochainPullback (leftBase m hm F) (innerDegree m a b)
      (GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m a) (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeGHPowers.degree m b)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F b)) := by
  rw [GeometricTimeCupInterval.pullback_interval, first_parameter]
  rfl

def nested : singularCochainGroup (ZMod 2) (tube m hm F) (index m a b k false) :=
  CupOne.cup (tube m hm F) (innerDegree m a b) k (index m a b k false)
    (by dsimp [innerDegree, index, NativePrefixTestOrder.index, NativePrefixTestOrder.pairDegree]; omega)
    (cochainPullback (leftBase m hm F) (innerDegree m a b)
      (GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m a) (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeGHPowers.degree m b)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F b))) (outerTest m hm F k E)

theorem integral_nested (hE : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) E) :
    TimeTriangleSplit.interval (tube m hm F) (index m a b k false) ≫
      NativeInnerFullClock.test m hm F a b k E false = nested m hm F a b k E := by
  rw [full_test, IntervalCupRightProjection.at_degree _ _ _ _ _ _ _ (outer_normalized m hm F k E hE), inner_integral]
  rfl

theorem full_value_nested (hE : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) E) :
    NativeInnerHalfIntervalComparison.fullValue m hm F a b k E false =
      CochainDegreeTransport.pre (tube m hm F) (NativeInnerIntervalComparison.low_degree m hm a b k false)
        (nested m hm F a b k E) := by
  unfold NativeInnerHalfIntervalComparison.fullValue IntervalHalfScalarComparison.value NativeInnerHalfIntervalComparison.fullTest
  rw [← NativeGHRawTwoTimeComparison.interval_pre, integral_nested m hm F a b k E hE]

end
end Finsler.NativePrefixFullTimeCup
