module

public import Finsler.Loop.NativeTwoTimeSquareComparison

/-! Compose the actual cap/time, product/raw and two-time/square
primitives. BOTH original normalized cap/near-interval expressions
compare to the SAME Stage108 square. Their prefix/suffix difference
is one explicit source coboundary. Complete nested PrismSelfCut and
SAME-Theta high-power UNIT identification remain separate. -/
@[expose] public section
namespace Finsler.NativeOriginalCapTimeSquare
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier
open Finsler.NativeGHProductRawAlignment (squareDegree)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def primitive (side : Bool) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) :=
  NativeGHRawTwoTimeComparison.primitive m hm F a b k E side +
    NativeTwoTimeSquareComparison.primitive m hm F a b k E side

theorem boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E side) =
      NativeGHOriginalTimeStages.originalSequential m hm F a b k E side -
        NativeTwoTimeSquareComparison.squareValue m hm F a b k E side := by
  change ((cochainCxZMod2 (Loops (m + 1))).d _ _).hom (_ + _) = _
  rw [map_add]
  change cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (NativeGHRawTwoTimeComparison.primitive m hm F a b k E side) +
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (NativeTwoTimeSquareComparison.primitive m hm F a b k E side) = _
  rw [NativeGHRawTwoTimeComparison.full_comparison m hm F a b k E side hE,
    NativeTwoTimeSquareComparison.boundary m hm F a b k E side hE]
  abel

def bothPrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) :=
  primitive m hm F a b k E false + NativeBothInterleavedSquare.primitive m hm F a b k E -
    primitive m hm F a b k E true

theorem square_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k)
      (NativeBothInterleavedSquare.primitive m hm F a b k E) =
      NativeTwoTimeSquareComparison.squareValue m hm F a b k E false -
        NativeTwoTimeSquareComparison.squareValue m hm F a b k E true := by
  have h := NativeBothInterleavedSquare.full_comparison m hm F a b k E hE
  simp only [Preadditive.comp_sub] at h
  exact h

theorem both_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (bothPrimitive m hm F a b k E) =
      NativeGHOriginalTimeStages.originalSequential m hm F a b k E false -
        NativeGHOriginalTimeStages.originalSequential m hm F a b k E true := by
  change ((cochainCxZMod2 (Loops (m + 1))).d _ _).hom ((_ + _) - _) = _
  rw [map_sub, map_add]
  change (cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E false) +
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (NativeBothInterleavedSquare.primitive m hm F a b k E)) -
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E true) = _
  rw [boundary m hm F a b k E false hE, boundary m hm F a b k E true hE, square_boundary m hm F a b k E hE]
  abel

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ NativeGHOriginalTimeStages.originalSequential m hm F a b k E false =
      c ≫ NativeGHOriginalTimeStages.originalSequential m hm F a b k E true := by
  have h := congrArg (fun f => c ≫ f) (both_boundary m hm F a b k E hE)
  change c ≫ ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    bothPrimitive m hm F a b k E) = _ at h
  rw [← Category.assoc c, hc, zero_comp, Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.NativeOriginalCapTimeSquare
