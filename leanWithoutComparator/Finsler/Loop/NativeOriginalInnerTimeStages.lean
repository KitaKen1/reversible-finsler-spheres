module

public import Finsler.Loop.NativeInnerIntervalComparison
public import Finsler.Loop.NativeOriginalCapTimeSquare

/-! Carry the SAME actual inner-cut pullback correction through the
original outer normalized cap and original first time prism. The two
INNER endpoint corrections remain explicit in correctedOriginal.
Both OUTER endpoints are discharged by the original normalized Thom.
This does not assert that the inner endpoint corrections vanish or that
the remaining raw-half clocks equal the complete nested time cups. -/
@[expose] public section
namespace Finsler.NativeOriginalInnerTimeStages
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
open Finsler.NativeGHProductRawAlignment (squareDegree)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)
abbrev q (side : Bool) := NativeInnerIntervalComparison.lowDegree m a b k side

include hm in
theorem parameter_degree (side : Bool) : squareDegree m a b k + 1 = (m + 1) + q m a b k side := by
  have h := NativeGHOuterTimeComparison.primitive_degree m hm a b k side
  change squareDegree m a b k + 1 = m + index m a b k side at h
  have hi := NativeInnerIntervalComparison.low_degree m hm a b k side
  change q m a b k side + 1 = index m a b k side at hi
  omega

def outerCap : DegreeLoweringHomology.Map (chains (base m)) (chains (TopCat.of (near m hm F))) (m + 1) :=
  NormalizedSelfCut.operation (m + 1) (by omega)
  (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)

def parameterPrimitive (side : Bool) := CochainDegreeTransport.pre (base m) (parameter_degree m hm a b k side)
  ((outerCap m hm F).component (q m a b k side) ≫ NativeInnerIntervalComparison.primitive m hm F a b k E side)

def parameterBefore (side : Bool) := CochainDegreeTransport.pre (base m)
  (show squareDegree m a b k + 2 = (m + 1) + (q m a b k side + 1) by have h := parameter_degree m hm a b k side; omega)
  ((outerCap m hm F).component (q m a b k side + 1) ≫ NativeInnerIntervalComparison.before m hm F a b k E side)

def parameterOriginal (side : Bool) := CochainDegreeTransport.pre (base m)
  (show squareDegree m a b k + 2 = (m + 1) + (q m a b k side + 1) by have h := parameter_degree m hm a b k side; omega)
  ((outerCap m hm F).component (q m a b k side + 1) ≫ NativeInnerIntervalComparison.correctedOriginal m hm F a b k E side)

theorem parameter_boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (base m) (squareDegree m a b k + 1) (parameterPrimitive m hm F a b k E side) =
      parameterBefore m hm F a b k E side - parameterOriginal m hm F a b k E side := by
  unfold parameterPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary, NativeSequentialDoubleCapOutputComparison.lowering_boundary,
    NativeInnerIntervalComparison.boundary m hm F a b k E side hE, Preadditive.comp_sub,
    NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem parameter_endpoint (side : Bool) (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (squareDegree m a b k + 1)
      (parameterPrimitive m hm F a b k E side) = 0 := by
  apply NativeSequentialGHGlobalComparison.pullback_pre_zero
  have hz : (push (SelfCutThomCocycle.atTime (m + 1) t)).f ((m + 1) + q m a b k side) ≫
      (outerCap m hm F).component (q m a b k side) = 0 :=
    SelfCutEndpoints.thom_atTime_zero (m + 1) (q m a b k side) (by omega)
      (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) t
      (by rcases ht with rfl | rfl
          · exact NormalizedSelfCut.time_zero _ _ _
          · exact NormalizedSelfCut.time_one _ _ _)
  change (push (SelfCutThomCocycle.atTime (m + 1) t)).f ((m + 1) + q m a b k side) ≫
    ((outerCap m hm F).component (q m a b k side) ≫ NativeInnerIntervalComparison.primitive m hm F a b k E side) = 0
  rw [← Category.assoc, hz, zero_comp]

def primitive (side : Bool) := SelfCutPrismCoboundary.primitive (m + 1) (squareDegree m a b k)
  (parameterPrimitive m hm F a b k E side)

def correctedOriginal (side : Bool) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫ parameterOriginal m hm F a b k E side

theorem before_original (side : Bool) :
    SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫ parameterBefore m hm F a b k E side =
      NativeGHOriginalTimeStages.originalSequential m hm F a b k E side := by
  unfold parameterBefore
  rw [NativeInnerIntervalComparison.before_original, ← NativeSuffixPostponedAlignment.pre_lowering,
    NativeRawClockSupportedAlignment.pre_trans]
  rfl

theorem boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E side) =
      NativeGHOriginalTimeStages.originalSequential m hm F a b k E side - correctedOriginal m hm F a b k E side := by
  have h := SelfCutPrismCoboundary.comparison (m + 1) (squareDegree m a b k)
    (parameterPrimitive m hm F a b k E side) (parameterBefore m hm F a b k E side) (parameterOriginal m hm F a b k E side)
    (parameter_boundary m hm F a b k E side hE)
    (parameter_endpoint m hm F a b k E side 0 (Or.inl rfl)) (parameter_endpoint m hm F a b k E side 1 (Or.inr rfl))
  rw [before_original] at h
  exact h

def bothPrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) :=
  NativeOriginalCapTimeSquare.bothPrimitive m hm F a b k E - primitive m hm F a b k E false + primitive m hm F a b k E true

theorem both_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (bothPrimitive m hm F a b k E) =
      correctedOriginal m hm F a b k E false - correctedOriginal m hm F a b k E true := by
  change ((cochainCxZMod2 (Loops (m + 1))).d _ _).hom ((_ - _) + _) = _
  rw [map_add, map_sub]
  change (cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (NativeOriginalCapTimeSquare.bothPrimitive m hm F a b k E) -
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E false)) +
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E true) = _
  rw [NativeOriginalCapTimeSquare.both_boundary m hm F a b k E hE,
    boundary m hm F a b k E false hE, boundary m hm F a b k E true hE]
  abel

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ correctedOriginal m hm F a b k E false = c ≫ correctedOriginal m hm F a b k E true := by
  have h := congrArg (fun f => c ≫ f) (both_boundary m hm F a b k E hE)
  change c ≫ ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫ bothPrimitive m hm F a b k E) = _ at h
  rw [← Category.assoc c, hc, zero_comp, Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.NativeOriginalInnerTimeStages
