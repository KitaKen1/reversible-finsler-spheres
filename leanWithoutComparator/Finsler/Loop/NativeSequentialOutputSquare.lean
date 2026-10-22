module

public import Finsler.Loop.NativeSequentialOutputFaces
public import Finsler.Loop.NativeRawOriginalScalarReduction

/-! The original GH output substitution is now valid on the ACTUAL
shuffle-square insertion of every source cycle, despite its nonzero time
boundary. Every degree cast and the source-boundary correction are retained.
This does not yet identify the complete original interleaved operation. -/
@[expose] public section
namespace Finsler.NativeSequentialOutputSquare
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

abbrev squareDegree (m a b k : ℕ) := m + m + NativeSequentialGHGlobalComparison.testDegree m a b k

theorem primitive_degree (m a b k : ℕ) : squareDegree m a b k + 2 =
    (m + 1) + ((m + 1) + NativeSequentialGHGlobalComparison.testDegree m a b k) := by
  unfold squareDegree
  omega

theorem input_degree (m a b k : ℕ) : squareDegree m a b k + 3 =
    (m + 1) + ((m + 1) + (NativeSequentialGHGlobalComparison.testDegree m a b k + 1)) := by
  unfold squareDegree
  omega

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixPrimitive := CochainDegreeTransport.pre (source (m + 1)) (primitive_degree m a b k)
  (NativeSequentialDoubleCapOutputComparison.prefixPrimitive m hm F a b k E)
def prefixOriginal := CochainDegreeTransport.pre (source (m + 1)) (input_degree m a b k)
  (NativeSequentialDoubleCapOutputComparison.prefixOriginal m hm F a b k E)
def prefixCommon := CochainDegreeTransport.pre (source (m + 1)) (input_degree m a b k)
  (NativeSequentialDoubleCapOutputComparison.prefixCommon m hm F a b k E)

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (squareDegree m a b k + 2) (prefixPrimitive m hm F a b k E) =
      prefixOriginal m hm F a b k E - prefixCommon m hm F a b k E := by
  unfold prefixPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary,
    NativeSequentialDoubleCapOutputComparison.prefix_boundary m hm F a b k E hE,
    NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem prefix_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (squareDegree m a b k + 2) (prefixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialGHGlobalComparison.pullback_pre_zero _ _ _
    (NativeSequentialOutputFaces.prefix_face_zero m hm F a b k E i)

theorem prefix_full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      (prefixOriginal m hm F a b k E - prefixCommon m hm F a b k E) =
    (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 2) ≫
      prefixPrimitive m hm F a b k E := by
  rw [← prefix_boundary m hm F a b k E hE]
  exact NativeRawTimeSquareBoundary.full_boundary_evaluation (m + 1) (squareDegree m a b k)
    (prefixPrimitive m hm F a b k E) (prefix_face_zero m hm F a b k E)

theorem prefix_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      prefixOriginal m hm F a b k E =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      prefixCommon m hm F a b k E := by
  have h := congrArg (fun T => c ≫ T) (prefix_full_comparison m hm F a b k E hE)
  rw [← Category.assoc c ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k)), hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h

def suffixPrimitive := CochainDegreeTransport.pre (source (m + 1)) (primitive_degree m a b k)
  (NativeSequentialDoubleCapOutputComparison.suffixPrimitive m hm F a b k E)
def suffixOriginal := CochainDegreeTransport.pre (source (m + 1)) (input_degree m a b k)
  (NativeSequentialDoubleCapOutputComparison.suffixOriginal m hm F a b k E)
def suffixCommon := CochainDegreeTransport.pre (source (m + 1)) (input_degree m a b k)
  (NativeSequentialDoubleCapOutputComparison.suffixCommon m hm F a b k E)

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (squareDegree m a b k + 2) (suffixPrimitive m hm F a b k E) =
      suffixOriginal m hm F a b k E - suffixCommon m hm F a b k E := by
  unfold suffixPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary,
    NativeSequentialDoubleCapOutputComparison.suffix_boundary m hm F a b k E hE,
    NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem suffix_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (squareDegree m a b k + 2) (suffixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialGHGlobalComparison.pullback_pre_zero _ _ _
    (NativeSequentialOutputFaces.suffix_face_zero m hm F a b k E i)

theorem suffix_full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      (suffixOriginal m hm F a b k E - suffixCommon m hm F a b k E) =
    (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
      OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 2) ≫
      suffixPrimitive m hm F a b k E := by
  rw [← suffix_boundary m hm F a b k E hE]
  exact NativeRawTimeSquareBoundary.full_boundary_evaluation (m + 1) (squareDegree m a b k)
    (suffixPrimitive m hm F a b k E) (suffix_face_zero m hm F a b k E)

theorem suffix_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      suffixOriginal m hm F a b k E =
    c ≫ OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      suffixCommon m hm F a b k E := by
  have h := congrArg (fun T => c ≫ T) (suffix_full_comparison m hm F a b k E hE)
  rw [← Category.assoc c ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k)), hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h

end
end Finsler.NativeSequentialOutputSquare
