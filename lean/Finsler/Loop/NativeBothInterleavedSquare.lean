module

public import Finsler.Loop.NativePrefixInterleavedSquare
public import Finsler.Loop.NativePrefixSuffixTestedSquare

/-! The actual prefix and suffix INTERLEAVED GH/evaluation placements
have equal values on the same genuine square over every source cycle.
The complete source primitive is explicit. Original repeated time
insertions and the original SINGLE high-power UNIT remain separate. -/
@[expose] public section
namespace Finsler.NativeBothInterleavedSquare
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeOriginalClockSquare
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) :=
  (show singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) from
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 2) ≫
        NativePrefixInterleavedSquare.primitive m hm F a b k E) +
    NativePrefixSuffixTestedSquare.primitive m hm F a b k E

theorem full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E) =
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        (NativePrefixInterleavedSquare.interleaved m hm F a b k E - NativeSuffixInterleavedSquare.interleaved m hm F a b k E) := by
  have hp := NativePrefixInterleavedSquare.full_comparison m hm F a b k E hE
  have hs := NativePrefixSuffixTestedSquare.full_comparison m hm F a b k E hE
  rw [NativePrefixInterleavedSquare.postponed_stage106] at hp
  change (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    NativePrefixSuffixTestedSquare.primitive m hm F a b k E = _ at hs
  change (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    primitive m hm F a b k E = _
  unfold primitive
  rw [Preadditive.comp_add, ← hp, hs]
  simp only [Preadditive.comp_sub]
  abel

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        NativePrefixInterleavedSquare.interleaved m hm F a b k E =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        NativeSuffixInterleavedSquare.interleaved m hm F a b k E := by
  have h := congrArg (fun T => c ≫ T) (full_comparison m hm F a b k E hE)
  change c ≫ ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    primitive m hm F a b k E) = _ at h
  rw [← Category.assoc c, hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.NativeBothInterleavedSquare
