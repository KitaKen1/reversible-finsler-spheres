module

public import Finsler.Loop.NormalizedCutScalarPullback
public import Finsler.Loop.NativePrefixTestOrder
public import Finsler.Loop.NativeSuffixTestOrder

/-! BOTH original raw-half inner tests compared with the ORIGINAL
normalized self-cut on its own parameter space. Exact tested/retained
factor squares identify the same original loops and GH cocycles. -/
@[expose] public section
namespace Finsler.NativeInnerCutPullback
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

abbrev rhoPos := NativeOrderedDoubleCutSupported.thomRadius_pos m hm F
abbrev rhoLt := NativeOrderedDoubleCutSupported.thomRadius_lt m hm F
abbrev radiusLe := NativeOrderedDoubleCutDiagonal.radius_le_one m hm F

def prefixNear := NormalizedCutScalarPullback.nearMap m (prefixParameter m hm F)
  (r := NativeClosingArcPowerVanishing.radius m hm F)
def suffixNear := NormalizedCutScalarPullback.nearMap m (suffixParameter m hm F)
  (r := NativeClosingArcPowerVanishing.radius m hm F)

theorem prefix_tested : prefixNear m hm F ≫ TopCat.ofHom (SupportedSelfCut.tested (m + 1) (radiusLe m hm F)) =
    NativePrefixTestOrder.nearTriple m hm F ≫ NativeTripleGHTest.first (m + 1) := rfl

theorem prefix_retained : prefixNear m hm F ≫ TopCat.ofHom (SupportedSelfCut.retained (m + 1) (radiusLe m hm F)) =
    NativePrefixTestOrder.nearTriple m hm F ≫ NativeTripleGHTest.middle (m + 1) := rfl

theorem suffix_tested : suffixNear m hm F ≫ TopCat.ofHom (SupportedSelfCut.tested (m + 1) (radiusLe m hm F)) =
    NativeSuffixTestOrder.nearTriple m hm F ≫ NativeTripleGHTest.middle (m + 1) := rfl

theorem suffix_retained : suffixNear m hm F ≫ TopCat.ofHom (SupportedSelfCut.retained (m + 1) (radiusLe m hm F)) =
    NativeSuffixTestOrder.nearTriple m hm F ≫ NativeTripleGHTest.last (m + 1) := rfl

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_split : cochainPullback (prefixNear m hm F) _
    (GeometricTimeCupCochain.splitCup m (NativeGHPowers.degree m a) (radiusLe m hm F)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeGHPowers.degree m b)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F b)) = NativePrefixTestOrder.psi m hm F a b := by
  unfold GeometricTimeCupCochain.splitCup NormalizedSelfCut.testedCocycle
  rw [cochainCup_naturality]
  simp only [← pullback_comp, prefix_tested, prefix_retained]
  rfl

theorem suffix_split : cochainPullback (suffixNear m hm F) _
    (GeometricTimeCupCochain.splitCup m (NativeGHPowers.degree m b) (radiusLe m hm F)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F b) k E) = NativeSuffixTestOrder.psi m hm F b k E := by
  unfold GeometricTimeCupCochain.splitCup NormalizedSelfCut.testedCocycle
  rw [cochainCup_naturality]
  simp only [← pullback_comp, suffix_tested, suffix_retained]
  rfl

def prefixPrimitive := NormalizedCutScalarPullback.primitive m (prefixParameter m hm F)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeClosingArcPowerVanishing.powerCocycle m hm F b)

def prefixOriginal := NormalizedCutScalarPullback.originalValue m (prefixParameter m hm F)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeClosingArcPowerVanishing.powerCocycle m hm F b)

def prefixLocal := NormalizedCutScalarPullback.localValue m (prefixParameter m hm F)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeClosingArcPowerVanishing.powerCocycle m hm F b)

def suffixPrimitive := NormalizedCutScalarPullback.primitive m (suffixParameter m hm F)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (NativeGHPowers.degree m b) k
  (NativeClosingArcPowerVanishing.powerCocycle m hm F b) E

def suffixOriginal := NormalizedCutScalarPullback.originalValue m (suffixParameter m hm F)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (NativeGHPowers.degree m b) k
  (NativeClosingArcPowerVanishing.powerCocycle m hm F b) E

def suffixLocal := NormalizedCutScalarPullback.localValue m (suffixParameter m hm F)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F) (NativeGHPowers.degree m b) k
  (NativeClosingArcPowerVanishing.powerCocycle m hm F b) E

theorem prefix_local : prefixLocal m hm F a b =
    (prefixOperation m hm F).component (NativePrefixTestOrder.pairDegree m a b) ≫ NativePrefixTestOrder.psi m hm F a b := by
  unfold prefixLocal NormalizedCutScalarPullback.localValue
  rw [show NormalizedCutScalarPullback.nearMap m (prefixParameter m hm F) = prefixNear m hm F from rfl, prefix_split]
  rfl

theorem suffix_local : suffixLocal m hm F b k E =
    (suffixOperation m hm F).component (NativeSuffixTestOrder.restDegree m b k) ≫ NativeSuffixTestOrder.psi m hm F b k E := by
  unfold suffixLocal NormalizedCutScalarPullback.localValue
  rw [show NormalizedCutScalarPullback.nearMap m (suffixParameter m hm F) = suffixNear m hm F from rfl, suffix_split]
  rfl

theorem prefix_boundary : cochainCoboundary (ZMod 2) (outerSpace m hm F)
    (m + NativePrefixTestOrder.pairDegree m a b) (prefixPrimitive m hm F a b) =
      CochainDegreeTransport.pre (outerSpace m hm F)
        (show m + NativePrefixTestOrder.pairDegree m a b + 1 = (m + 1) + NativePrefixTestOrder.pairDegree m a b by omega)
        (prefixLocal m hm F a b - prefixOriginal m hm F a b) :=
  NormalizedCutScalarPullback.boundary _ _ _ _ _ _ _ _ _
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a)
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b)

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (outerSpace m hm F)
      (m + NativeSuffixTestOrder.restDegree m b k) (suffixPrimitive m hm F b k E) =
      CochainDegreeTransport.pre (outerSpace m hm F)
        (show m + NativeSuffixTestOrder.restDegree m b k + 1 = (m + 1) + NativeSuffixTestOrder.restDegree m b k by omega)
        (suffixLocal m hm F b k E - suffixOriginal m hm F b k E) :=
  NormalizedCutScalarPullback.boundary _ _ _ _ _ _ _ _ _
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b) hE

end
end Finsler.NativeInnerCutPullback
