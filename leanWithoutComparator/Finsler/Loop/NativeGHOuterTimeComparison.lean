module

public import Finsler.Loop.NativeGHIntervalOrder
public import Finsler.Loop.SelfCutPrismCoboundary
public import Finsler.Loop.NativeBothInterleavedSquare

/-! Insert the actual GH cap/interval correction through the ORIGINAL
first self-cut time prism. Both parameter endpoints of the correction
vanish. The explicit source coboundary compares the two orders at the
SAME Stage108 square degree, for BOTH prefix and suffix GH tests.
The two time insertions have not yet been identified with square shuffle. -/
@[expose] public section
namespace Finsler.NativeGHOuterTimeComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

abbrev squareDegree := NativeOriginalClockSquare.squareDegree

theorem primitive_degree (m : ℕ) (hm : 2 ≤ m) (a b k : ℕ) (side : Bool) :
    squareDegree m a b k + 1 = m + index m a b k side := by
  cases side with
  | false =>
    have h := NativePrefixInterleavedSquare.primitive_degree m hm a b k
    change squareDegree m a b k + 2 = (m + 1) + NativePrefixTestOrder.index m a b k at h
    change squareDegree m a b k + 1 = m + NativePrefixTestOrder.index m a b k
    omega
  | true =>
    have h := NativeSuffixInterleavedSquare.primitive_degree m hm a b k
    change squareDegree m a b k + 2 = (m + 1) + NativeSuffixTestOrder.index m a b k at h
    change squareDegree m a b k + 1 = m + NativeSuffixTestOrder.index m a b k
    omega

theorem input_degree (m : ℕ) (hm : 2 ≤ m) (a b k : ℕ) (side : Bool) :
    squareDegree m a b k + 2 = m + index m a b k side + 1 := by
  have h := primitive_degree m hm a b k side
  omega

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

def parameterPrimitive := CochainDegreeTransport.pre (base m) (primitive_degree m hm a b k side)
  (NativeGHIntervalOrder.primitive m hm F a b k E side)
def parameterBefore := CochainDegreeTransport.pre (base m) (input_degree m hm a b k side)
  (NativeGHIntervalOrder.before m hm F a b k E side)
def parameterAfter := CochainDegreeTransport.pre (base m) (input_degree m hm a b k side)
  (NativeGHIntervalOrder.after m hm F a b k E side)

theorem parameter_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (base m) (squareDegree m a b k + 1)
      (parameterPrimitive m hm F a b k E side) =
      parameterBefore m hm F a b k E side - parameterAfter m hm F a b k E side := by
  unfold parameterPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary, NativeGHIntervalOrder.boundary m hm F a b k E side hE,
    NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem parameter_endpoint (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (squareDegree m a b k + 1)
      (parameterPrimitive m hm F a b k E side) = 0 :=
  NativeSequentialGHGlobalComparison.pullback_pre_zero _ _ _
    (NativeGHIntervalOrder.primitive_endpoint m hm F a b k E side t ht)

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) :=
  SelfCutPrismCoboundary.primitive (m + 1) (squareDegree m a b k) (parameterPrimitive m hm F a b k E side)

def sequential : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫ parameterBefore m hm F a b k E side

def moved : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫ parameterAfter m hm F a b k E side

theorem full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E side) =
      sequential m hm F a b k E side - moved m hm F a b k E side :=
  SelfCutPrismCoboundary.comparison (m + 1) (squareDegree m a b k)
    (parameterPrimitive m hm F a b k E side) (parameterBefore m hm F a b k E side)
    (parameterAfter m hm F a b k E side) (parameter_boundary m hm F a b k E side hE)
    (parameter_endpoint m hm F a b k E side 0 (Or.inl rfl))
    (parameter_endpoint m hm F a b k E side 1 (Or.inr rfl))

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ sequential m hm F a b k E side = c ≫ moved m hm F a b k E side :=
  SelfCutPrismCoboundary.cycle_values_eq (m + 1) (squareDegree m a b k)
    (parameterPrimitive m hm F a b k E side) (parameterBefore m hm F a b k E side)
    (parameterAfter m hm F a b k E side) (parameter_boundary m hm F a b k E side hE)
    (parameter_endpoint m hm F a b k E side 0 (Or.inl rfl))
    (parameter_endpoint m hm F a b k E side 1 (Or.inr rfl)) c hc

end
end Finsler.NativeGHOuterTimeComparison
