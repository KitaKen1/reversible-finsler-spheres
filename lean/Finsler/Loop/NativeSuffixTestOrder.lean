module

public import Finsler.Loop.SupportedCapTestOrder
public import Finsler.Loop.NativeSequentialSupportedStages
public import Finsler.Loop.NativeTripleGHTest
public import Finsler.Loop.NativeSequentialDoubleCapOutputComparison

/-! Instantiate the supported test/Thom commutation with the SAME
original GH powers, ORIGINAL suffix-half inner cut and actual original
outer Thom cap. On the real raw-half parameter source the first GH
test can move past the actual inner supported Thom cap by an EXPLICIT
global boundary. The postponed near output is the genuine original
triple test, with all source degrees retained. Sequential time-cross
alignment and the other cap-order comparison remain separate. -/
@[expose] public section
namespace Finsler.NativeSuffixTestOrder
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
abbrev far := NativeOrderedDoubleCutSupported.far (NativeSequentialSupportedStages.suffixParameter m hm F)
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev near := NativeOrderedDoubleCutSupported.near (NativeSequentialSupportedStages.suffixParameter m hm F)
  (NativeClosingArcPowerVanishing.radius m hm F)
abbrev far_open := NativeOrderedDoubleCutSupported.far_open (NativeSequentialSupportedStages.suffixParameter m hm F)
  (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev near_open := NativeOrderedDoubleCutSupported.near_open (NativeSequentialSupportedStages.suffixParameter m hm F)
  (NativeClosingArcPowerVanishing.radius m hm F)
abbrev cover := NativeOrderedDoubleCutSupported.cover (NativeSequentialSupportedStages.suffixParameter m hm F)
  (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)

def theta := NativeOrderedDoubleCutSupported.thom (NativeSequentialSupportedStages.suffixParameter m hm F)
  (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)

theorem theta_supported : cochainPullback (SupportedCap.subspaceMap (space m hm F) (far m hm F)) (m + 1)
    (theta m hm F) = 0 := NativeOrderedDoubleCutSupported.thom_supported _ _ _

theorem theta_closed : cochainCoboundary (ZMod 2) (space m hm F) (m + 1) (theta m hm F) = 0 :=
  NativeOrderedDoubleCutSupported.thom_closed _ _ _

def firstTestMap : space m hm F ⟶ Loops (m + 1) := TopCat.ofHom
  ⟨fun z => left (NativeSequentialSupportedStages.outer m hm F z).1,
    (continuous_left (n := m + 1)).comp (continuous_fst.comp (NativeSequentialSupportedStages.outer m hm F).hom.continuous)⟩

def nearTriple : TopCat.of (near m hm F) ⟶ NativeSequentialTripleComparison.triple (m + 1) :=
  NativeSequentialSupportedStages.suffixFinal m hm F ≫ NativeSequentialCollarGeometry.suffixOriginal m hm F

theorem first_factor : SupportedCap.subspaceMap (space m hm F) (near m hm F) ≫ firstTestMap m hm F =
    nearTriple m hm F ≫ NativeTripleGHTest.first (m + 1) := rfl

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)
abbrev restDegree := NativeGHPowers.degree m b + k
abbrev index := (NativeGHPowers.degree m a + m) + restDegree m b k

def alpha := cochainPullback (firstTestMap m hm F) _ (NativeClosingArcPowerVanishing.powerCocycle m hm F a)

theorem alpha_closed : cochainCoboundary (ZMod 2) (space m hm F) _ (alpha m hm F a) = 0 :=
  pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F a)

def psi : singularCochainGroup (ZMod 2) (TopCat.of (near m hm F)) (restDegree m b k) :=
  cochainCup _ _
    (cochainPullback (nearTriple m hm F ≫ NativeTripleGHTest.middle (m + 1)) _
      (NativeClosingArcPowerVanishing.powerCocycle m hm F b))
    (cochainPullback (nearTriple m hm F ≫ NativeTripleGHTest.last (m + 1)) k E)

theorem psi_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (psi m hm F b k E) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _
    (pullback_closed _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F b))
    (pullback_closed _ _ E hE)

theorem near_output : cochainCup _ _
    (cochainPullback (SupportedCap.subspaceMap (space m hm F) (near m hm F)) _ (alpha m hm F a))
    (psi m hm F b k E) =
    cochainPullback (nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E) := by
  have hα : cochainPullback (SupportedCap.subspaceMap (space m hm F) (near m hm F)) _ (alpha m hm F a) =
      cochainPullback (nearTriple m hm F ≫ NativeTripleGHTest.first (m + 1)) _
        (NativeClosingArcPowerVanishing.powerCocycle m hm F a) := by
    rw [alpha, ← pullback_comp, first_factor]
  rw [hα, NativeTripleGHTest.test, cochainCup_naturality, cochainCup_naturality]
  simp only [← pullback_comp, psi]

def primitive : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k) :=
  SupportedCapTestOrder.primitive (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) (NativeGHPowers.degree m a) m (restDegree m b k)
    (alpha m hm F a) (theta m hm F) (theta_supported m hm F) (psi m hm F b k E)

def interleaved : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k + 1) :=
  SupportedCapTestOrderCoupling.before (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) (NativeGHPowers.degree m a) m (restDegree m b k)
    (alpha m hm F a) (theta m hm F) (theta_supported m hm F) (psi m hm F b k E)

def postponed : singularCochainGroup (ZMod 2) (space m hm F) (index m a b k + 1) :=
  SupportedCapTestOrderCoupling.after (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) (NativeGHPowers.degree m a) m (restDegree m b k)
    (alpha m hm F a) (theta m hm F) (theta_supported m hm F) (psi m hm F b k E)

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (space m hm F) _ (primitive m hm F a b k E) =
      interleaved m hm F a b k E - postponed m hm F a b k E :=
  SupportedCapTestOrder.boundary _ _ _ _ _ _ _ _ _ _ _ _ _
    (alpha_closed m hm F a) (theta_closed m hm F) (psi_closed m hm F b k E hE)

theorem postponed_output : postponed m hm F a b k E =
    SupportedCap.cut (space m hm F) (far m hm F) (near m hm F)
      (far_open m hm F) (near_open m hm F) (cover m hm F) (m + 1)
      (NativeTripleGHTest.degree m a b k) (index m a b k + 1) (by dsimp [NativeTripleGHTest.degree, index, restDegree]; omega)
      (theta m hm F) (theta_supported m hm F) ≫
        cochainPullback (nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E) := by
  have he := RelativeCapDual.absolute_chain_dual (TopCat.of (near m hm F))
    (NativeGHPowers.degree m a) (restDegree m b k)
    (cochainPullback (SupportedCap.subspaceMap (space m hm F) (near m hm F)) _ (alpha m hm F a))
    (psi m hm F b k E)
  exact congrArg (fun φ : singularCochainGroup (ZMod 2) (TopCat.of (near m hm F)) (NativeTripleGHTest.degree m a b k) =>
    SupportedCap.cut (space m hm F) (far m hm F) (near m hm F)
      (far_open m hm F) (near_open m hm F) (cover m hm F) (m + 1)
      (NativeTripleGHTest.degree m a b k) (index m a b k + 1) (by dsimp [NativeTripleGHTest.degree, index, restDegree]; omega)
      (theta m hm F) (theta_supported m hm F) ≫ φ) (he.trans (near_output m hm F a b k E))

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

theorem primitive_carrier_zero (C : Set (space m hm F))
    (hC : cochainPullback (restriction (SupportedCap.subspaceMap (space m hm F) C)
      ((SupportedCap.subspaceMap (space m hm F) C) ⁻¹' near m hm F) (near m hm F) (fun _ h => h)) _
      (psi m hm F b k E) = 0) :
    cochainPullback (SupportedCap.subspaceMap (space m hm F) C) _ (primitive m hm F a b k E) = 0 :=
  SupportedCapTestOrder.primitive_carrier_zero _ _ _ _ _ _ _ _ _ _ _ _ _ C hC

end
end Finsler.NativeSuffixTestOrder
