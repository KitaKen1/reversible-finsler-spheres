module

public import Finsler.Loop.NativeInnerHalfIntervalComparison
public import Finsler.Loop.NativeOriginalInnerEndpointFree

/-! Remove BOTH raw-half clock restrictions using the actual original
triangle, short arc vanishing, original outer cap and first prism.
The full-inner-interval expressions agree on every source cycle.
Moving the retained cup factors through time integration is separate. -/
@[expose] public section
namespace Finsler.NativeOriginalInnerFullTime
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
open Finsler.NativeGHProductRawAlignment (squareDegree)
open Finsler.NativeOriginalInnerTimeStages (q outerCap parameter_degree)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def parameterPrimitive (side : Bool) := CochainDegreeTransport.pre (base m) (parameter_degree m hm a b k side)
  ((outerCap m hm F).component (q m a b k side) ≫ NativeInnerHalfIntervalComparison.primitive m hm F a b k E side)

def parameterValue (side : Bool) := CochainDegreeTransport.pre (base m)
  (show squareDegree m a b k + 2 = (m + 1) + (q m a b k side + 1) by have h := parameter_degree m hm a b k side; omega)
  ((outerCap m hm F).component (q m a b k side + 1) ≫ NativeInnerHalfIntervalComparison.fullValue m hm F a b k E side)

theorem parameter_boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (base m) (squareDegree m a b k + 1) (parameterPrimitive m hm F a b k E side) =
      parameterValue m hm F a b k E side - NativeOriginalInnerEndpointFree.parameterValue m hm F a b k E side := by
  unfold parameterPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary, NativeSequentialDoubleCapOutputComparison.lowering_boundary,
    NativeInnerHalfIntervalComparison.boundary m hm F a b k E side hE, Preadditive.comp_sub,
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
    ((outerCap m hm F).component (q m a b k side) ≫ NativeInnerHalfIntervalComparison.primitive m hm F a b k E side) = 0
  rw [← Category.assoc, hz, zero_comp]

def primitive (side : Bool) := SelfCutPrismCoboundary.primitive (m + 1) (squareDegree m a b k)
  (parameterPrimitive m hm F a b k E side)

def value (side : Bool) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫ parameterValue m hm F a b k E side

theorem boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E side) =
      value m hm F a b k E side - NativeOriginalInnerEndpointFree.value m hm F a b k E side :=
  SelfCutPrismCoboundary.comparison (m + 1) (squareDegree m a b k)
    (parameterPrimitive m hm F a b k E side) (parameterValue m hm F a b k E side)
    (NativeOriginalInnerEndpointFree.parameterValue m hm F a b k E side)
    (parameter_boundary m hm F a b k E side hE)
    (parameter_endpoint m hm F a b k E side 0 (Or.inl rfl)) (parameter_endpoint m hm F a b k E side 1 (Or.inr rfl))

def bothPrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) :=
  primitive m hm F a b k E false + NativeOriginalInnerTimeStages.bothPrimitive m hm F a b k E - primitive m hm F a b k E true

theorem both_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (bothPrimitive m hm F a b k E) =
      value m hm F a b k E false - value m hm F a b k E true := by
  change ((cochainCxZMod2 (Loops (m + 1))).d _ _).hom ((_ + _) - _) = _
  rw [map_sub, map_add]
  change (cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E false) +
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (NativeOriginalInnerTimeStages.bothPrimitive m hm F a b k E)) -
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E true) = _
  rw [boundary m hm F a b k E false hE, NativeOriginalInnerEndpointFree.boundary m hm F a b k E hE,
    boundary m hm F a b k E true hE]
  abel

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ value m hm F a b k E false = c ≫ value m hm F a b k E true := by
  have h := congrArg (fun f => c ≫ f) (both_boundary m hm F a b k E hE)
  change c ≫ ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫ bothPrimitive m hm F a b k E) = _ at h
  rw [← Category.assoc c, hc, zero_comp, Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.NativeOriginalInnerFullTime
