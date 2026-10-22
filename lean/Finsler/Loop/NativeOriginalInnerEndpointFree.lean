module

public import Finsler.Loop.NativeInnerIntervalEndpoints
public import Finsler.Loop.NativeOriginalInnerTimeStages

/-! BOTH original normalized inner cuts, actual retained factors and
raw-half intervals, followed by the ORIGINAL outer cap and first prism.
No inner endpoint correction remains. Their difference is the SAME
explicit source coboundary, hence they agree on every source cycle.
Identification with complete nested GH time cups is still separate. -/
@[expose] public section
namespace Finsler.NativeOriginalInnerEndpointFree
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

def parameterValue (side : Bool) := CochainDegreeTransport.pre (base m)
  (show squareDegree m a b k + 2 = (m + 1) + (q m a b k side + 1) by have h := parameter_degree m hm a b k side; omega)
  ((outerCap m hm F).component (q m a b k side + 1) ≫
    RightIntervalFullCoboundary.integrate (TopCat.of (near m hm F)) (q m a b k side + 1)
      (NativeInnerIntervalComparison.tubeOriginal m hm F a b k E side))

def value (side : Bool) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  SelfCutTimePrism.prism (m + 1) (squareDegree m a b k + 1) ≫ parameterValue m hm F a b k E side

theorem parameter_corrected_eq (side : Bool) :
    NativeOriginalInnerTimeStages.parameterOriginal m hm F a b k E side = parameterValue m hm F a b k E side := by
  unfold NativeOriginalInnerTimeStages.parameterOriginal
  rw [NativeInnerIntervalEndpoints.corrected_original]
  rfl

theorem corrected_eq (side : Bool) :
    NativeOriginalInnerTimeStages.correctedOriginal m hm F a b k E side = value m hm F a b k E side := by
  unfold NativeOriginalInnerTimeStages.correctedOriginal
  rw [parameter_corrected_eq]
  rfl

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k)
      (NativeOriginalInnerTimeStages.bothPrimitive m hm F a b k E) =
        value m hm F a b k E false - value m hm F a b k E true := by
  rw [NativeOriginalInnerTimeStages.both_boundary m hm F a b k E hE, corrected_eq, corrected_eq]

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ value m hm F a b k E false = c ≫ value m hm F a b k E true := by
  have h := NativeOriginalInnerTimeStages.cycle_values_eq m hm F a b k E hE c hc
  rw [corrected_eq, corrected_eq] at h
  exact h

end
end Finsler.NativeOriginalInnerEndpointFree
