module

public import Finsler.Loop.NativeSquareClockAlignment

/-! BOTH ORIGINAL postponed two-stage Thom/GH cochains have equal
values on the actual canonical square insertion of every source cycle.
Their difference is an explicit SOURCE coboundary, retaining both
normalization corrections. Complete interleaved time/test alignment
and the original SINGLE high-power UNIT remain separate obligations. -/
@[expose] public section
namespace Finsler.NativePostponedSquareEquality
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeOriginalClockSquare
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) :=
  (show singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) from
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k) ≫
    (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 2) ≫
      (prefixPrimitive m hm F a b k E -
        SingularNormalization.primitive _ (squareDegree m a b k + 2) (prefixOrdered m hm F a b k E) -
        suffixPrimitive m hm F a b k E +
        SingularNormalization.primitive _ (squareDegree m a b k + 2) (suffixOrdered m hm F a b k E))) +
  OrderedClockCycleComparison.primitive (Loops (m + 1)) (squareDegree m a b k)
    (NativeOrderedSquareInput.input m hm F a b k E)

theorem full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E) =
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        (prefixOriginal m hm F a b k E - suffixOriginal m hm F a b k E) := by
  have hp := prefix_full_comparison m hm F a b k E hE
  have hs := suffix_full_comparison m hm F a b k E hE
  have hnp := NativeSquareNormalization.full_comparison (m + 1) (squareDegree m a b k)
    (prefixOrdered m hm F a b k E) (NativeOrderedSquareInput.prefix_closed m hm F a b k E hE)
    (NativeOrderedSquareInput.prefix_face_zero m hm F a b k E)
  have hns := NativeSquareNormalization.full_comparison (m + 1) (squareDegree m a b k)
    (suffixOrdered m hm F a b k E) (NativeOrderedSquareInput.suffix_closed m hm F a b k E hE)
    (NativeOrderedSquareInput.suffix_face_zero m hm F a b k E)
  have hh := OrderedClockCycleComparison.comparison_boundary (Loops (m + 1)) (squareDegree m a b k)
    (NativeOrderedSquareInput.input m hm F a b k E)
    (NativeOrderedSquareInput.input_closed m hm F a b k E hE)
    (NativeOrderedSquareInput.input_diagonal_map_zero m hm F a b k E)
  rw [← NativeSquareClockAlignment.prefix_normalized_square,
    ← NativeSquareClockAlignment.suffix_normalized_square] at hh
  change (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    OrderedClockCycleComparison.primitive _ _ _ =
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        SingularNormalization.normalize _ _ (prefixOrdered m hm F a b k E) -
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        SingularNormalization.normalize _ _ (suffixOrdered m hm F a b k E) at hh
  change (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    primitive m hm F a b k E = _
  unfold primitive
  simp only [Preadditive.comp_add, Preadditive.comp_sub]
  rw [← hp, ← hnp, ← hs, ← hns, hh]
  simp only [Preadditive.comp_sub]
  abel

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        prefixOriginal m hm F a b k E =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        suffixOriginal m hm F a b k E := by
  have h := congrArg (fun T => c ≫ T) (full_comparison m hm F a b k E hE)
  change c ≫ ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    primitive m hm F a b k E) = _ at h
  rw [← Category.assoc c, hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

theorem stage97_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        NativeSequentialOutputSquare.prefixOriginal m hm F a b k E =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        NativeSequentialOutputSquare.suffixOriginal m hm F a b k E := by
  rw [← prefix_original_stage97, ← suffix_original_stage97]
  exact cycle_values_eq m hm F a b k E hE c hc

end
end Finsler.NativePostponedSquareEquality
