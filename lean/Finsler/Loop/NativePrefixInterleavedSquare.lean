module

public import Finsler.Loop.NativePrefixTestFaces
public import Finsler.Loop.NativePrefixPostponedAlignment
public import Finsler.Loop.NativePostponedSquareEquality

/-! Insert the actual prefix RIGHT-test comparison into the same
canonical shuffle square. The genuine source boundary and all degree
transports are retained; postponement is the same Stage97 original. -/
@[expose] public section
namespace Finsler.NativePrefixInterleavedSquare
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages
open Finsler.NativeRawClockSupportedAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

abbrev squareDegree := NativeOriginalClockSquare.squareDegree

theorem primitive_degree (m : ℕ) (hm : 2 ≤ m) (a b k : ℕ) : squareDegree m a b k + 2 =
    (m + 1) + NativePrefixTestOrder.index m a b k := by
  have hd := NativeSequentialGHGlobalComparison.degree_match m hm a b k
  dsimp [squareDegree, NativeOriginalClockSquare.squareDegree, NativeSequentialOutputSquare.squareDegree,
    NativePrefixTestOrder.index, NativePrefixTestOrder.pairDegree, NativeTripleGHTest.degree] at *
  omega

theorem input_degree (m : ℕ) (hm : 2 ≤ m) (a b k : ℕ) : squareDegree m a b k + 3 =
    (m + 1) + (NativePrefixTestOrder.index m a b k + 1) := by
  have h := primitive_degree m hm a b k
  omega

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def primitive := CochainDegreeTransport.pre (source (m + 1)) (primitive_degree m hm a b k)
  (NativePrefixTestOrder.globalPrimitive m hm F a b k E)
def interleaved := CochainDegreeTransport.pre (source (m + 1)) (input_degree m hm a b k)
  (NativePrefixTestOrder.globalInterleaved m hm F a b k E)
def postponed := CochainDegreeTransport.pre (source (m + 1)) (input_degree m hm a b k)
  (NativePrefixTestOrder.globalPostponed m hm F a b k E)

theorem postponed_stage97 : postponed m hm F a b k E =
    NativeSequentialOutputSquare.prefixOriginal m hm F a b k E := by
  unfold postponed NativeSequentialOutputSquare.prefixOriginal
  rw [← NativePrefixPostponedAlignment.global_postponed_compare,
    ← NativePrefixPostponedAlignment.stage97_compare, pre_trans, pre_trans]

theorem postponed_stage106 : postponed m hm F a b k E =
    NativeOriginalClockSquare.prefixOriginal m hm F a b k E :=
  (postponed_stage97 m hm F a b k E).trans
    (NativeOriginalClockSquare.prefix_original_stage97 m hm F a b k E).symm

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (squareDegree m a b k + 2) (primitive m hm F a b k E) =
      interleaved m hm F a b k E - postponed m hm F a b k E := by
  unfold primitive
  rw [NativeRawOriginalScalarReduction.pre_boundary,
    NativePrefixTestOrder.global_boundary m hm F a b k E hE, NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem face_zero (i : Fin 4) : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (squareDegree m a b k + 2) (primitive m hm F a b k E) = 0 :=
  NativeSequentialGHGlobalComparison.pullback_pre_zero _ _ _
    (NativePrefixTestFaces.global_face_zero m hm F a b k E i)

theorem full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        (interleaved m hm F a b k E - postponed m hm F a b k E) =
    (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k) ≫
        (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 2) ≫
          primitive m hm F a b k E := by
  rw [← boundary m hm F a b k E hE]
  exact NativeRawTimeSquareBoundary.full_boundary_evaluation (m + 1) (squareDegree m a b k)
    (primitive m hm F a b k E) (face_zero m hm F a b k E)

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        interleaved m hm F a b k E =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
        postponed m hm F a b k E := by
  have h := congrArg (fun T => c ≫ T) (full_comparison m hm F a b k E hE)
  rw [← Category.assoc c ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k)), hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h

end
end Finsler.NativePrefixInterleavedSquare
