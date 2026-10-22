module

public import Finsler.Loop.MatchingOriginalRelativeOutputSplit
public import Finsler.Loop.PrismCochainEndpointTrace

/-! Keep the actual time-end obstruction for the SAME original split
on the full nonadjacent matching locus. Its ordinary time-prism value
is exactly the difference of the two primitive traces on genuine
source cycles. Absolute exactness is not mistaken for relative zero. -/
@[expose] public section
namespace Finsler.MatchingRelativeOutputEndpointTrace
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev source {n : ℕ} (P : Sphere n) : TopCat.{0} := TopCat.of (equator P × equator P)

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
  (a : RelativeCup.cohomology (fullPair (m + 1)) (m + 1))

def trace (t : ClosedInterval) : (chains (source P)).cycles (m + m) ⟶ coeff :=
  (chains (source P)).iCycles (m + m) ≫
    cochainPullback (DoubleRelativeTimeCylinder.atTime (source P) t) (m + m)
      (MatchingOriginalRelativeOutputSplit.primitive m P v₀ a)

def value : (chains (source P)).cycles (m + m) ⟶ coeff :=
  (chains (source P)).iCycles (m + m) ≫
    ((DoubleRelativeTimeCylinder.homotopy (source P)).toSSet.chainComplexMap coeff).hom (m + m) ((m + m) + 1) ≫
      MatchingOriginalRelativeOutputSplit.split m P v₀ a

include hm in
theorem value_eq_trace_sub : value m P v₀ a = trace m P v₀ a 0 - trace m P v₀ a 1 := by
  have he := PrismCochainEndpointTrace.boundary (DoubleRelativeTimeCylinder.homotopy (source P)) (m + m) (by omega)
    (MatchingOriginalRelativeOutputSplit.primitive m P v₀ a)
  rw [MatchingOriginalRelativeOutputSplit.primitive_d] at he
  exact he

include hm in
theorem value_zero_iff : value m P v₀ a = 0 ↔ trace m P v₀ a 0 = trace m P v₀ a 1 := by
  rw [value_eq_trace_sub m hm P v₀ a, sub_eq_zero]

include hm in
theorem scalar_eq_trace_sub (c : (chains (source P)).cycles (m + m)) :
    (value m P v₀ a).hom c = (trace m P v₀ a 0).hom c - (trace m P v₀ a 1).hom c :=
  ConcreteCategory.congr_hom (value_eq_trace_sub m hm P v₀ a) c

include hm in
theorem scalar_zero_iff (c : (chains (source P)).cycles (m + m)) :
    (value m P v₀ a).hom c = 0 ↔ (trace m P v₀ a 0).hom c = (trace m P v₀ a 1).hom c := by
  rw [scalar_eq_trace_sub m hm P v₀ a c, sub_eq_zero]

include hm in
theorem trace_sub_independent
    (χ : singularCochainGroup (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + m))
    (hχ : cochainCoboundary (ZMod 2) (NativeMeridianMatchingLoci.parameters P) (m + m) χ =
      MatchingOriginalRelativeOutputSplit.split m P v₀ a) :
    trace m P v₀ a 0 - trace m P v₀ a 1 =
      (chains (source P)).iCycles (m + m) ≫ cochainPullback (DoubleRelativeTimeCylinder.atTime (source P) 0) (m + m) χ -
      (chains (source P)).iCycles (m + m) ≫ cochainPullback (DoubleRelativeTimeCylinder.atTime (source P) 1) (m + m) χ :=
  PrismCochainEndpointTrace.endpoint_sub_eq_of_same_boundary (DoubleRelativeTimeCylinder.homotopy (source P))
    (m + m) (by omega) (MatchingOriginalRelativeOutputSplit.primitive m P v₀ a) χ
    ((MatchingOriginalRelativeOutputSplit.primitive_d m P v₀ a).trans hχ.symm)

end
end Finsler.MatchingRelativeOutputEndpointTrace
