module

public import Finsler.Loop.SupportedRightTestOrder
public import Finsler.Loop.NativeSequentialSupportedStages
public import Finsler.Loop.NativeTripleGHTest
public import Finsler.Loop.NativeSequentialDoubleCapOutputComparison

/-! The original prefix inner cut followed by its two GH tests,
with the original outer retained-loop evaluation on the RIGHT.
One actual small-subdivision primitive compares it with postponement. -/
@[expose] public section
namespace Finsler.NativePrefixTestOrder
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.H1SelfCutNeighborhood Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev space := NativeSequentialSupportedStages.outerSpace m hm F
abbrev far := NativeOrderedDoubleCutSupported.far (NativeSequentialSupportedStages.prefixParameter m hm F)
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev near := NativeOrderedDoubleCutSupported.near (NativeSequentialSupportedStages.prefixParameter m hm F)
  (NativeClosingArcPowerVanishing.radius m hm F)
abbrev far_open := NativeOrderedDoubleCutSupported.far_open (NativeSequentialSupportedStages.prefixParameter m hm F)
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev near_open := NativeOrderedDoubleCutSupported.near_open (NativeSequentialSupportedStages.prefixParameter m hm F)
  (NativeClosingArcPowerVanishing.radius m hm F)
abbrev cover := NativeOrderedDoubleCutSupported.cover (NativeSequentialSupportedStages.prefixParameter m hm F)
  (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)

def theta := NativeOrderedDoubleCutSupported.thom (NativeSequentialSupportedStages.prefixParameter m hm F)
  (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)

theorem theta_supported : cochainPullback (SupportedCap.subspaceMap (space m hm F) (far m hm F)) (m + 1)
    (theta m hm F) = 0 := NativeOrderedDoubleCutSupported.thom_supported _ _ _

theorem theta_closed : cochainCoboundary (ZMod 2) (space m hm F) (m + 1) (theta m hm F) = 0 :=
  NativeOrderedDoubleCutSupported.thom_closed _ _ _

def lastTestMap : space m hm F ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => right (NativeSequentialSupportedStages.outer m hm F z).1,
    (continuous_right (n := m + 1)).comp (continuous_fst.comp (NativeSequentialSupportedStages.outer m hm F).hom.continuous)⟩

def nearTriple : TopCat.of (near m hm F) ⟶ NativeSequentialTripleComparison.triple (m + 1) :=
  NativeSequentialSupportedStages.prefixFinal m hm F ≫ NativeSequentialCollarGeometry.prefixOriginal m hm F

theorem last_factor : SupportedCap.subspaceMap (space m hm F) (near m hm F) ≫ lastTestMap m hm F =
    nearTriple m hm F ≫ NativeTripleGHTest.last (m + 1) := rfl

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)
abbrev pairDegree := NativeGHPowers.degree m a + NativeGHPowers.degree m b
abbrev index := (m + pairDegree m a b) + k

def alpha := cochainPullback (lastTestMap m hm F) k E

theorem alpha_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (space m hm F) k (alpha m hm F k E) = 0 :=
  pullback_closed _ k E hE

def psi : singularCochainGroup (ZMod 2) (TopCat.of (near m hm F)) (pairDegree m a b) :=
  cochainCup _ _
    (cochainPullback (nearTriple m hm F ≫ NativeTripleGHTest.first (m + 1)) _
      (NativeClosingArcPowerVanishing.powerCocycle m hm F a))
    (cochainPullback (nearTriple m hm F ≫ NativeTripleGHTest.middle (m + 1)) _
      (NativeClosingArcPowerVanishing.powerCocycle m hm F b))

theorem psi_closed : cochainCoboundary (ZMod 2) _ _ (psi m hm F a b) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _
    (pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a))
    (pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b))

theorem near_output : CupOne.cup (TopCat.of (near m hm F)) (pairDegree m a b) k
    (NativeTripleGHTest.degree m a b k) (by dsimp [pairDegree, NativeTripleGHTest.degree]; omega)
    (psi m hm F a b) (cochainPullback (SupportedCap.subspaceMap (space m hm F) (near m hm F)) k (alpha m hm F k E)) =
    cochainPullback (nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E) := by
  have hα : cochainPullback (SupportedCap.subspaceMap (space m hm F) (near m hm F)) k (alpha m hm F k E) =
      cochainPullback (nearTriple m hm F ≫ NativeTripleGHTest.last (m + 1)) k E := by
    rw [alpha, ← pullback_comp, last_factor]
  rw [hα, psi, ← CupOne.cup_comparison]
  rw [SupportedRightTestLocal.cup_assoc (TopCat.of (near m hm F))
    (NativeGHPowers.degree m a) (NativeGHPowers.degree m b) k (pairDegree m a b)
    (NativeGHPowers.degree m b + k) (NativeTripleGHTest.degree m a b k) rfl rfl (by
      dsimp [pairDegree, NativeTripleGHTest.degree]; omega) rfl]
  rw [CupOne.cup_comparison, CupOne.cup_comparison, NativeTripleGHTest.test,
    cochainCup_naturality, cochainCup_naturality]
  simp only [← pullback_comp]

def primitive : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k) :=
  SupportedRightTestOrder.primitive (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) k m (pairDegree m a b)
    (alpha m hm F k E) (theta m hm F) (theta_supported m hm F) (psi m hm F a b)

def interleaved : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k + 1) :=
  SupportedRightTestLocal.before (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) k m (pairDegree m a b)
    (alpha m hm F k E) (theta m hm F) (theta_supported m hm F) (psi m hm F a b)

def postponed : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k + 1) :=
  SupportedRightTestLocal.after (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) k m (pairDegree m a b)
    (alpha m hm F k E) (theta m hm F) (theta_supported m hm F) (psi m hm F a b)

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (space m hm F) _ (primitive m hm F a b k E) =
      interleaved m hm F a b k E - postponed m hm F a b k E :=
  SupportedRightTestOrder.boundary _ _ _ _ _ _ _ _ _ _ _ _ _
    (alpha_closed m hm F k E hE) (theta_closed m hm F) (psi_closed m hm F a b)

def globalPrimitive : singularCochainGroup (ZMod 2) (NativeSequentialSupportedStages.source (m + 1))
    ((m + 1) + index m a b k) :=
  (NativeSequentialSupportedStages.firstOperation m hm F).component (index m a b k) ≫ primitive m hm F a b k E

def globalInterleaved : singularCochainGroup (ZMod 2) (NativeSequentialSupportedStages.source (m + 1))
    ((m + 1) + (index m a b k + 1)) :=
  (NativeSequentialSupportedStages.firstOperation m hm F).component (index m a b k + 1) ≫ interleaved m hm F a b k E

def globalPostponed : singularCochainGroup (ZMod 2) (NativeSequentialSupportedStages.source (m + 1))
    ((m + 1) + (index m a b k + 1)) :=
  (NativeSequentialSupportedStages.firstOperation m hm F).component (index m a b k + 1) ≫ postponed m hm F a b k E

theorem global_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (globalPrimitive m hm F a b k E) =
      globalInterleaved m hm F a b k E - globalPostponed m hm F a b k E := by
  unfold globalPrimitive
  rw [NativeSequentialDoubleCapOutputComparison.lowering_boundary, boundary m hm F a b k E hE, Preadditive.comp_sub]
  rfl

end
end Finsler.NativePrefixTestOrder
