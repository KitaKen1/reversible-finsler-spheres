module

public import Finsler.Loop.NativeInnerIntervalEndpoints
public import Finsler.Topology.UnivCochainExtension

/-! The actual ORIGINAL inner normalized cuts on the FULL time interval,
with the SAME outside factors. Their raw-half restrictions are literally
Stage113's tests. The discarded arc halves vanish by actual short output
carriers in the original ambient space, not by retraction naturality. -/
@[expose] public section
namespace Finsler.NativeInnerFullClock
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeIntervalGHTests Finsler.NativeInnerCutPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem original_closed (m : ℕ) {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (p q : ℕ)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)
    (B : singularCochainGroup (ZMod 2) (Loops (m + 1)) q)
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) p T = 0)
    (hB : cochainCoboundary (ZMod 2) (Loops (m + 1)) q B = 0) :
    cochainCoboundary (ZMod 2) X ((m + 1) + (p + q))
      (NormalizedCutScalarPullback.originalValue m f hρ hρr hr p q T B) = 0 :=
  pullback_closed _ _ _ (DegreeLoweringCochainPullback.closed
    (NormalizedSelfCut.operation (m + 1) (by omega) hρ hρr) (p + q) _
    (NormalizedCutScalarPullback.split_closed m hr p q T B hT hB))

theorem univ_zero (X : TopCat.{0}) (p : ℕ) (T : singularCochainGroup (ZMod 2) X p)
    (hT : cochainPullback (SupportedCap.subspaceMap X Set.univ) p T = 0) : T = 0 := by
  apply UnivCochainExtension.pullback_injective X p
  rw [hT]
  simp only [cochainPullback, map_zero]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev tube := TopCat.of (near m hm F)
abbrev space := RightIntervalCochain.space (tube m hm F)

def first : space m hm F ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  (TopCat.ofHom (SupportedSelfCut.tested (m + 1) (radiusLe m hm F)) ▷ TopCat.I) ≫
    (SelfCutTimePrism.cylinder (m + 1)).h

def second : space m hm F ⟶ SelfCutThomCocycle.parameters (m + 1) :=
  (TopCat.ofHom (SupportedSelfCut.retained (m + 1) (radiusLe m hm F)) ▷ TopCat.I) ≫
    (SelfCutTimePrism.cylinder (m + 1)).h

def leftOutside := rawNear m hm F ≫ NativeSuffixTestOrder.firstTestMap m hm F
def rightOutside := rawNear m hm F ≫ NativePrefixTestOrder.lastTestMap m hm F

theorem first_half : (tube m hm F ◁ IntervalTriangle.firstMap) ≫ first m hm F =
    rawNear m hm F ≫ NativeSequentialSupportedStages.prefixParameter m hm F := rfl

theorem second_half : (tube m hm F ◁ IntervalTriangle.secondMap) ≫ second m hm F =
    rawNear m hm F ≫ NativeSequentialSupportedStages.suffixParameter m hm F := rfl

theorem outside_half (g : TopCat.I.{0} ⟶ TopCat.I.{0}) :
    (tube m hm F ◁ g) ≫ leftOutside m hm F = leftOutside m hm F ∧
    (tube m hm F ◁ g) ≫ rightOutside m hm F = rightOutside m hm F := ⟨rfl, rfl⟩

def arcDomain (z : space m hm F) : NativeClosingArcPowerVanishing.domain m hm F :=
  (⟨(NativeSequentialSupportedStages.outer m hm F (rawNear m hm F z)).1, z.1.property⟩, z.2.down)

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixValue : singularCochainGroup (ZMod 2) (space m hm F) ((m + 1) + NativePrefixTestOrder.pairDegree m a b) :=
  NormalizedCutScalarPullback.originalValue m (first m hm F) (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F a) (NativeClosingArcPowerVanishing.powerCocycle m hm F b)

def suffix : singularCochainGroup (ZMod 2) (space m hm F) ((m + 1) + NativeSuffixTestOrder.restDegree m b k) :=
  NormalizedCutScalarPullback.originalValue m (second m hm F) (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeGHPowers.degree m b) k (NativeClosingArcPowerVanishing.powerCocycle m hm F b) E

theorem prefix_half : cochainPullback (tube m hm F ◁ IntervalTriangle.firstMap) _ (prefixValue m hm F a b) =
    cochainPullback (rawNear m hm F) _ (NativeInnerCutPullback.prefixOriginal m hm F a b) := by
  unfold prefixValue NativeInnerCutPullback.prefixOriginal NormalizedCutScalarPullback.originalValue
  rw [← pullback_comp, first_half, pullback_comp]

theorem suffix_half : cochainPullback (tube m hm F ◁ IntervalTriangle.secondMap) _ (suffix m hm F b k E) =
    cochainPullback (rawNear m hm F) _ (NativeInnerCutPullback.suffixOriginal m hm F b k E) := by
  unfold suffix NativeInnerCutPullback.suffixOriginal NormalizedCutScalarPullback.originalValue
  rw [← pullback_comp, second_half, pullback_comp]

theorem prefix_arc_zero : cochainPullback (tube m hm F ◁ IntervalTriangle.secondMap) _ (prefixValue m hm F a b) = 0 := by
  have h := NormalizedCutScalarCarrier.original_retained_zero m
    ((tube m hm F ◁ IntervalTriangle.secondMap) ≫ first m hm F)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F a)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F b) Set.univ
    (SelfCutOscillation.short F (NativeClosingArcPowerVanishing.supportScale m hm F))
    (NativeClosingArcPowerVanishing.powerCocycle_supported m hm F b)
    (fun z _ _ => NativeClosingArcPowerVanishing.left_short m hm F (arcDomain m hm F z))
  have hz := univ_zero (space m hm F) _ _ h
  simp only [NormalizedCutScalarPullback.originalValue, pullback_comp] at hz
  exact hz

theorem suffix_arc_zero : cochainPullback (tube m hm F ◁ IntervalTriangle.firstMap) _ (suffix m hm F b k E) = 0 := by
  have h := NormalizedCutScalarCarrier.original_tested_zero m
    ((tube m hm F ◁ IntervalTriangle.firstMap) ≫ second m hm F)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeGHPowers.degree m b) k (NativeClosingArcPowerVanishing.powerCocycle m hm F b) E Set.univ
    (SelfCutOscillation.short F (NativeClosingArcPowerVanishing.supportScale m hm F))
    (NativeClosingArcPowerVanishing.powerCocycle_supported m hm F b)
    (fun z _ _ => NativeClosingArcPowerVanishing.right_short m hm F (arcDomain m hm F z))
  have hz := univ_zero (space m hm F) _ _ h
  simp only [NormalizedCutScalarPullback.originalValue, pullback_comp] at hz
  exact hz

def prefixTest : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k false + 1) :=
  CupOne.cup (space m hm F) ((m + 1) + NativePrefixTestOrder.pairDegree m a b) k
    (index m a b k false + 1) (by dsimp [index, NativePrefixTestOrder.index]; omega)
    (prefixValue m hm F a b) (cochainPullback (rightOutside m hm F) k E)

def suffixTest : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k true + 1) :=
  CupOne.cup (space m hm F) (NativeGHPowers.degree m a) ((m + 1) + NativeSuffixTestOrder.restDegree m b k)
    (index m a b k true + 1) (by dsimp [index, NativeSuffixTestOrder.index]; omega)
    (cochainPullback (leftOutside m hm F) _ (NativeClosingArcPowerVanishing.powerCocycle m hm F a)) (suffix m hm F b k E)

def test (side : Bool) : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k side + 1) :=
  match side with
  | false => prefixTest m hm F a b k E
  | true => suffixTest m hm F a b k E

theorem test_closed (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (space m hm F) (index m a b k side + 1) (test m hm F a b k E side) = 0 := by
  cases side
  · apply CupCapOrder.closed
    · exact original_closed _ _ _ _ _ _ _ _ _
        (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a) (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b)
    · exact pullback_closed _ _ _ hE
  · apply CupCapOrder.closed
    · exact pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a)
    · exact original_closed _ _ _ _ _ _ _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b) hE

theorem prefix_test_half : cochainPullback (tube m hm F ◁ IntervalTriangle.firstMap) _ (test m hm F a b k E false) =
    cochainPullback (rawNear m hm F) _ (NativeInnerIntervalComparison.rawOriginal m hm F a b k E false) := by
  change cochainPullback (tube m hm F ◁ IntervalTriangle.firstMap) _ (prefixTest m hm F a b k E) =
    cochainPullback (rawNear m hm F) _ (NativeInnerRetainedComparison.prefixOriginal m hm F a b k E)
  unfold prefixTest NativeInnerRetainedComparison.prefixOriginal
  rw [CupCapOrder.naturality, CupCapOrder.naturality, prefix_half, ← pullback_comp, (outside_half m hm F IntervalTriangle.firstMap).2]
  rw [rightOutside, pullback_comp]
  rfl

theorem suffix_test_half : cochainPullback (tube m hm F ◁ IntervalTriangle.secondMap) _ (test m hm F a b k E true) =
    cochainPullback (rawNear m hm F) _ (NativeInnerIntervalComparison.rawOriginal m hm F a b k E true) := by
  change cochainPullback (tube m hm F ◁ IntervalTriangle.secondMap) _ (suffixTest m hm F a b k E) =
    cochainPullback (rawNear m hm F) _ (NativeInnerRetainedComparison.suffixOriginal m hm F a b k E)
  unfold suffixTest NativeInnerRetainedComparison.suffixOriginal
  rw [CupCapOrder.naturality, CupCapOrder.naturality, suffix_half, ← pullback_comp, (outside_half m hm F IntervalTriangle.secondMap).1]
  rw [leftOutside, pullback_comp]
  rfl

theorem prefix_test_arc_zero : cochainPullback (tube m hm F ◁ IntervalTriangle.secondMap) _ (test m hm F a b k E false) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ _ _ _ (Or.inl (prefix_arc_zero m hm F a b))

theorem suffix_test_arc_zero : cochainPullback (tube m hm F ◁ IntervalTriangle.firstMap) _ (test m hm F a b k E true) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ _ _ _ (Or.inr (suffix_arc_zero m hm F b k E))

end
end Finsler.NativeInnerFullClock
