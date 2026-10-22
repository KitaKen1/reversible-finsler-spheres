module

public import Finsler.Loop.NativePrefixFullTimeCup
public import Finsler.Loop.GeometricTimeCupSource
public import Finsler.Loop.NativeOriginalInnerFullTime

/-! Identify BOTH complete original full-inner-interval expressions
with the actual nested geometric time cups on the original loop source.
The same Stage115 source primitive proves the comparison for normalized
closed retained output, with all source degrees and radii unchanged. -/
@[expose] public section
namespace Finsler.NativeNestedTimeCupAlignment
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests Finsler.NativeInnerCutPullback
open Finsler.NativeInnerFullClock (tube)
open Finsler.NativeGHProductRawAlignment (squareDegree)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

abbrev innerLeft := GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m a)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeGHPowers.degree m b)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F b)
abbrev innerRight := GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m b)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F b) k E

abbrev leftDegree := (m + NativePrefixFullTimeCup.innerDegree m a b) + k
abbrev rightDegree := (m + NativeGHPowers.degree m a) + NativeSuffixFullTimeCup.innerDegree m b k

theorem prefix_index : index m a b k false = NativePrefixFullTimeCup.innerDegree m a b + k := by
  dsimp [index, NativePrefixTestOrder.index, NativePrefixTestOrder.pairDegree, NativePrefixFullTimeCup.innerDegree]
  omega

theorem suffix_index : index m a b k true = NativeGHPowers.degree m a + NativeSuffixFullTimeCup.innerDegree m b k := by
  dsimp [index, NativeSuffixTestOrder.index, NativeSuffixTestOrder.restDegree, NativeSuffixFullTimeCup.innerDegree]
  omega

include hm in
theorem left_degree : squareDegree m a b k + 1 = leftDegree m a b k := by
  have h := NativeGHOuterTimeComparison.primitive_degree m hm a b k false
  change squareDegree m a b k + 1 = m + index m a b k false at h
  rw [prefix_index] at h
  dsimp [leftDegree]
  omega

include hm in
theorem right_degree : squareDegree m a b k + 1 = rightDegree m a b k := by
  have h := NativeGHOuterTimeComparison.primitive_degree m hm a b k true
  change squareDegree m a b k + 1 = m + index m a b k true at h
  rw [suffix_index] at h
  dsimp [rightDegree]
  omega

def leftValue : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  CochainDegreeTransport.pre (Loops (m + 1)) (left_degree m hm a b k)
    (GeometricTimeCupCochain.cochain m (NativePrefixFullTimeCup.innerDegree m a b)
      (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (innerLeft m hm F a b) k E)

def rightValue : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  CochainDegreeTransport.pre (Loops (m + 1)) (right_degree m hm a b k)
    (GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m a)
      (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeSuffixFullTimeCup.innerDegree m b k)
      (innerRight m hm F b k E))

theorem prefix_split : NativePrefixFullTimeCup.nested m hm F a b k E =
    CochainDegreeTransport.pre (tube m hm F) (prefix_index m a b k)
      (GeometricTimeCupCochain.splitCup m (NativePrefixFullTimeCup.innerDegree m a b)
        (radiusLe m hm F) (innerLeft m hm F a b) k E) := by
  unfold NativePrefixFullTimeCup.nested
  rw [GeometricTimeCupSource.cup_at_degree]
  rfl

theorem suffix_split : NativeSuffixFullTimeCup.nested m hm F a b k E =
    CochainDegreeTransport.pre (tube m hm F) (suffix_index m a b k)
      (GeometricTimeCupCochain.splitCup m (NativeGHPowers.degree m a)
        (radiusLe m hm F) (NativeClosingArcPowerVanishing.powerCocycle m hm F a)
        (NativeSuffixFullTimeCup.innerDegree m b k) (innerRight m hm F b k E)) := by
  unfold NativeSuffixFullTimeCup.nested
  rw [GeometricTimeCupSource.cup_at_degree]
  rfl

theorem prefix_source (hE : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) E) :
    NativeOriginalInnerFullTime.value m hm F a b k E false = leftValue m hm F a b k E := by
  unfold NativeOriginalInnerFullTime.value NativeOriginalInnerFullTime.parameterValue
  rw [NativePrefixFullTimeCup.full_value_nested m hm F a b k E hE, prefix_split,
    NativeRawClockSupportedAlignment.pre_trans]
  exact GeometricTimeCupSource.source_at_degree m (NativePrefixFullTimeCup.innerDegree m a b) k
    (squareDegree m a b k + 1) _ (left_degree m hm a b k) _ _
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (innerLeft m hm F a b) E

theorem suffix_source : NativeOriginalInnerFullTime.value m hm F a b k E true = rightValue m hm F a b k E := by
  unfold NativeOriginalInnerFullTime.value NativeOriginalInnerFullTime.parameterValue
  rw [NativeSuffixFullTimeCup.full_value_nested, suffix_split, NativeRawClockSupportedAlignment.pre_trans]
  exact GeometricTimeCupSource.source_at_degree m (NativeGHPowers.degree m a) (NativeSuffixFullTimeCup.innerDegree m b k)
    (squareDegree m a b k + 1) _ (right_degree m hm a b k) _ _
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (NativeClosingArcPowerVanishing.powerCocycle m hm F a)
    (innerRight m hm F b k E)

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (hn : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (Loops (m + 1))) E) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k)
      (NativeOriginalInnerFullTime.bothPrimitive m hm F a b k E) = leftValue m hm F a b k E - rightValue m hm F a b k E := by
  rw [NativeOriginalInnerFullTime.both_boundary m hm F a b k E hE, prefix_source m hm F a b k E hn, suffix_source]

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (hn : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (Loops (m + 1))) E)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ leftValue m hm F a b k E = c ≫ rightValue m hm F a b k E := by
  rw [← prefix_source m hm F a b k E hn, ← suffix_source]
  exact NativeOriginalInnerFullTime.cycle_values_eq m hm F a b k E hE c hc

theorem left_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) (leftValue m hm F a b k E) = 0 :=
  CochainDegreeTransport.closed _ _ _ (GeometricTimeCupCochain.closed _ _ _ _ _ _ _ _
    (GeometricTimeCupCochain.closed _ _ _ _ _ _ _ _
      (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a)
      (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b)) hE)

theorem right_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) (rightValue m hm F a b k E) = 0 :=
  CochainDegreeTransport.closed _ _ _ (GeometricTimeCupCochain.closed _ _ _ _ _ _ _ _
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a)
    (GeometricTimeCupCochain.closed _ _ _ _ _ _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b) hE))

theorem class_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (hn : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization (Loops (m + 1))) E) :
    cocycleClass _ (squareDegree m a b k + 1) (leftValue m hm F a b k E) (left_closed m hm F a b k E hE) =
      cocycleClass _ (squareDegree m a b k + 1) (rightValue m hm F a b k E) (right_closed m hm F a b k E hE) :=
  RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 (Loops (m + 1)))
    (squareDegree m a b k) (squareDegree m a b k + 1) (NativeOriginalInnerFullTime.bothPrimitive m hm F a b k E)
    _ _ _ _ (boundary m hm F a b k E hE hn).symm

end
end Finsler.NativeNestedTimeCupAlignment
