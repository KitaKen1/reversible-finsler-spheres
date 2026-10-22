module

public import Finsler.Loop.MatchingRetainedOutputPrimitive
public import Finsler.Loop.NativeUnitParameterCochain

/-! The ORIGINAL nonadjacent tested/retained split on the ENTIRE
matching locus, for every genuine constant-relative output. An actual
global output primitive bounds this SAME split cochain. No assertion
about the first Thom cap, global time faces, or UNIT follows alone. -/
@[expose] public section
namespace Finsler.MatchingOriginalRelativeOutputSplit
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def testedH1 {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    NativeMeridianMatchingLoci.parameters P ⟶ Loops n :=
  TopCat.ofHom ⟨fun z => H1SelfCutNeighborhood.left
    (DiagonalSelfCutRepresentatives.intoTube (NativeMeridianMatchingLoci.intoDiagonal P v₀ b z)),
    H1SelfCutNeighborhood.continuous_left.comp
      ((DiagonalSelfCutRepresentatives.continuous_intoTube n).comp
        (NativeMeridianMatchingLoci.intoDiagonal P v₀ b).hom.continuous)⟩

variable (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

def tested : singularCochainGroup (ZMod 2) (NativeMeridianMatchingLoci.parameters P) m :=
  cochainPullback (testedH1 P v₀ 1) m (classRepr _ m (MeridianLoopClass.H1TransgressionClass m))

theorem tested_closed : cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) m (tested m P v₀) = 0 :=
  pullback_closed _ _ _ (classRepr_isCocycle _ m _)

def output : singularCochainGroup (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + 1) :=
  MatchingRetainedOutputPrimitive.cochain m P v₀ (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)

theorem output_closed : cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + 1) (output m P v₀ a) = 0 :=
  MatchingRetainedOutputPrimitive.closed m P v₀ _ (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a)

def split : singularCochainGroup (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + (m + 1)) :=
  cochainCup m (m + 1) (tested m P v₀) (output m P v₀ a)

theorem closed : cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + (m + 1)) (split m P v₀ a) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _ (tested_closed m P v₀) (output_closed m P v₀ a)

def primitive : singularCochainGroup (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + m) :=
  cochainCup m m (tested m P v₀)
    (MatchingRetainedOutputPrimitive.primitive m P v₀ (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)
      (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a))

theorem primitive_d : cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + m)
    (primitive m P v₀ a) = split m P v₀ a := by
  have he := cochainCupZMod2_coboundary_right m m (tested m P v₀)
    (MatchingRetainedOutputPrimitive.primitive m P v₀ (ConstantRelativeOutputCochain.cochain (m + 1) (m + 1) a)
      (ConstantRelativeOutputCochain.closed (m + 1) (m + 1) a)) (tested_closed m P v₀)
  rw [MatchingRetainedOutputPrimitive.primitive_d] at he
  exact he

theorem distance_zero (b : Fin 3) (z : NativeMeridianMatchingLoci.parameters P) :
    SupportedSelfCut.distance (m + 1) (NativeMeridianMatchingLoci.intoCut P v₀ b z) = 0 := by
  rw [← SelfCutDistanceCoordinates.selfEvaluation_distance, NativeMeridianMatchingLoci.selfEvaluation]
  exact (congrArg norm (sub_self _)).trans norm_zero

def nearMap (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) {r : ℝ} (hr : 0 < r) : NativeMeridianMatchingLoci.parameters P ⟶
    TopCat.of (SupportedSelfCut.neighborhood (m + 1) r) :=
  TopCat.ofHom ⟨fun z => ⟨NativeMeridianMatchingLoci.intoCut P v₀ 1 z, by
    change SupportedSelfCut.distance (m + 1) (NativeMeridianMatchingLoci.intoCut P v₀ 1 z) < r
    rw [distance_zero]
    exact hr⟩, (NativeMeridianMatchingLoci.intoCut P v₀ 1).hom.continuous.subtype_mk _⟩

theorem original_output {r : ℝ} (hr₀ : 0 < r) (hr : r ≤ 1) :
    cochainPullback (nearMap m P v₀ hr₀) (m + (m + 1)) (NativeUnitParameterCochain.output m hr a) = split m P v₀ a := by
  unfold NativeUnitParameterCochain.output GeometricTimeCupCochain.splitCup NormalizedSelfCut.testedCocycle split tested output
  rw [cochainCup_naturality, ← pullback_comp, ← pullback_comp]
  rfl

end
end Finsler.MatchingOriginalRelativeOutputSplit
