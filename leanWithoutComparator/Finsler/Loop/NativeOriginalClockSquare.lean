module

public import Finsler.Loop.NativeOriginalAllTimeFaces
public import Finsler.Loop.NativeSequentialOutputSquare

/-! BOTH ORIGINAL postponed two-stage Thom/GH operations agree with
the SAME Stage95 clock pullbacks on the genuine canonical shuffle-square
insertion of EVERY source cycle. All degree casts and the full source
boundary term are retained. Complete interleaved time/test alignment is
still separate from this actual postponed-cochain comparison. -/
@[expose] public section
namespace Finsler.NativeOriginalClockSquare
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages
open Finsler.NativeRawClockSupportedAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

abbrev squareDegree := NativeSequentialOutputSquare.squareDegree

theorem primitive_degree (m : ℕ) (hm : 2 ≤ m) (a b k : ℕ) :
    squareDegree m a b k + 2 = index m a b k :=
  (NativeSequentialOutputSquare.primitive_degree m a b k).trans
    (NativeRawOriginalScalarReduction.primitive_degree m hm a b k).symm

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixPrimitive := CochainDegreeTransport.pre (source (m + 1)) (primitive_degree m hm a b k)
  (NativeOriginalTwoStageClockComparison.prefixOriginalPrimitive m hm F a b k E)
def prefixOriginal := CochainDegreeTransport.pre (source (m + 1)) (congrArg (fun n => n + 1) (primitive_degree m hm a b k))
  (NativeRawOriginalScalarReduction.prefixOriginal m hm F a b k E)
def prefixOrdered := CochainDegreeTransport.pre (source (m + 1)) (congrArg (fun n => n + 1) (primitive_degree m hm a b k))
  (NativeOriginalTwoStageClockComparison.prefixOrderedInput m hm F a b k E)

theorem prefix_original_stage97 : prefixOriginal m hm F a b k E =
    NativeSequentialOutputSquare.prefixOriginal m hm F a b k E := by
  unfold prefixOriginal NativeRawOriginalScalarReduction.prefixOriginal NativeSequentialOutputSquare.prefixOriginal
  rw [pre_trans]

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (squareDegree m a b k + 2) (prefixPrimitive m hm F a b k E) =
      prefixOriginal m hm F a b k E - prefixOrdered m hm F a b k E := by
  unfold prefixPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary,
    NativeOriginalTwoStageClockComparison.prefix_original_boundary m hm F a b k E hE,
    NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem prefix_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (squareDegree m a b k + 2) (prefixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialGHGlobalComparison.pullback_pre_zero _ _ _
    (NativeOriginalAllTimeFaces.prefix_original_face_zero m hm F a b k E i)

theorem prefix_full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      (prefixOriginal m hm F a b k E - prefixOrdered m hm F a b k E) =
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
      prefixOrdered m hm F a b k E := by
  have h := congrArg (fun T => c ≫ T) (prefix_full_comparison m hm F a b k E hE)
  rw [← Category.assoc c ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k)), hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h

def suffixPrimitive := CochainDegreeTransport.pre (source (m + 1)) (primitive_degree m hm a b k)
  (NativeOriginalTwoStageClockComparison.suffixOriginalPrimitive m hm F a b k E)
def suffixOriginal := CochainDegreeTransport.pre (source (m + 1)) (congrArg (fun n => n + 1) (primitive_degree m hm a b k))
  (NativeRawOriginalScalarReduction.suffixOriginal m hm F a b k E)
def suffixOrdered := CochainDegreeTransport.pre (source (m + 1)) (congrArg (fun n => n + 1) (primitive_degree m hm a b k))
  (NativeOriginalTwoStageClockComparison.suffixOrderedInput m hm F a b k E)

theorem suffix_original_stage97 : suffixOriginal m hm F a b k E =
    NativeSequentialOutputSquare.suffixOriginal m hm F a b k E := by
  unfold suffixOriginal NativeRawOriginalScalarReduction.suffixOriginal NativeSequentialOutputSquare.suffixOriginal
  rw [pre_trans]

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (squareDegree m a b k + 2) (suffixPrimitive m hm F a b k E) =
      suffixOriginal m hm F a b k E - suffixOrdered m hm F a b k E := by
  unfold suffixPrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary,
    NativeOriginalTwoStageClockComparison.suffix_original_boundary m hm F a b k E hE,
    NativeRawOriginalScalarReduction.pre_sub]
  rfl

theorem suffix_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (squareDegree m a b k + 2) (suffixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialGHGlobalComparison.pullback_pre_zero _ _ _
    (NativeOriginalAllTimeFaces.suffix_original_face_zero m hm F a b k E i)

theorem suffix_full_comparison (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
      (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      (suffixOriginal m hm F a b k E - suffixOrdered m hm F a b k E) =
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
      suffixOrdered m hm F a b k E := by
  have h := congrArg (fun T => c ≫ T) (suffix_full_comparison m hm F a b k E hE)
  rw [← Category.assoc c ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k)), hc, zero_comp] at h
  simp only [Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h

end
end Finsler.NativeOriginalClockSquare
