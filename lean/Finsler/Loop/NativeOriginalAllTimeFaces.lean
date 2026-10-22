module

public import Finsler.Loop.NativeRawEndpointCorrections
public import Finsler.Loop.NativeOriginalClockFaceReduction

/-! ALL FOUR face restrictions of the SAME Stage103 total comparison
primitive vanish. Its two duplicate inverse-image subdivision terms
cancel exactly. Equality on chains whose real boundary is a sum of four
face chains follows without a closed-face-union vanishing assertion. -/
@[expose] public section
namespace Finsler.NativeOriginalAllTimeFaces
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages
open Finsler.NativeRawClockSupportedAlignment Finsler.NativeOriginalTwoStageClockComparison
open Finsler.NativeRawEndpointGeometry Finsler.NativeRawEndpointCorrections
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_cancelled_decomposition : prefixCommonPrimitive m hm F a b k E =
    NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E + NativeRawCupOrder.prefixPrimitive m hm F a b k E + 
      NativeRawReindexedComparison.prefixPrimitive m hm F a b k E -
      cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (index m a b k)
        (NativeOrderedDoubleCapCommon.primitive m hm F a b k E) := by
  unfold prefixCommonPrimitive NativeRawStage101Bridge.prefixPrimitive NativeOrderedScalarPullback.primitive
  abel

theorem prefix_remaining_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k)
      (prefixCommonPrimitive m hm F a b k E) = 0 := by
  rw [prefix_cancelled_decomposition]
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)).op).f _).hom (_ - _) = 0
  simp only [map_sub, map_add]
  change cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k) (NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E) +
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k) (NativeRawCupOrder.prefixPrimitive m hm F a b k E) +
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k) (NativeRawReindexedComparison.prefixPrimitive m hm F a b k E) -
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k) (cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (index m a b k)
      (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)) = 0
  rw [prefix_double_zero, prefix_cup_one_zero, prefix_reindexed_zero, prefix_ordered_zero]
  simp only [add_zero, sub_self]

theorem prefix_common_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (prefixCommonPrimitive m hm F a b k E) = 0 := by
  fin_cases i
  · exact prefix_remaining_zero m hm F a b k E false
  · exact prefix_remaining_zero m hm F a b k E true
  · rw [← NativeOriginalClockFaceReduction.prefix_face_reduction]
    exact NativeOriginalClockFaceReduction.prefix_total_face_zero m hm F a b k E 2 (Or.inl rfl)
  · rw [← NativeOriginalClockFaceReduction.prefix_face_reduction]
    exact NativeOriginalClockFaceReduction.prefix_total_face_zero m hm F a b k E 3 (Or.inr rfl)

theorem prefix_original_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (prefixOriginalPrimitive m hm F a b k E) = 0 := by
  rw [NativeOriginalClockFaceReduction.prefix_face_reduction]
  exact prefix_common_face_zero m hm F a b k E i

theorem prefix_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : (i : Fin 4) → coeff ⟶ (chains (TopCat.of (NativeRawTimeSquareBoundary.face (m + 1) i))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      ∑ i : Fin 4, d i ≫ (push (SupportedCap.subspaceMap (source (m + 1))
        (NativeRawTimeSquareBoundary.face (m + 1) i))).f (index m a b k)) :
    c ≫ NativeRawOriginalScalarReduction.prefixOriginal m hm F a b k E =
      c ≫ prefixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (prefix_original_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    prefixOriginalPrimitive m hm F a b k E) = _ at hb
  have hz (i : Fin 4) : (push (SupportedCap.subspaceMap (source (m + 1))
      (NativeRawTimeSquareBoundary.face (m + 1) i))).f (index m a b k) ≫ prefixOriginalPrimitive m hm F a b k E = 0 :=
    prefix_original_face_zero m hm F a b k E i
  rw [← Category.assoc, hc, Preadditive.sum_comp] at hb
  simp only [Category.assoc, hz, comp_zero, Finset.sum_const_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

theorem suffix_cancelled_decomposition : suffixCommonPrimitive m hm F a b k E =
    NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E + 
      NativeRawReindexedComparison.suffixPrimitive m hm F a b k E -
      cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (index m a b k)
        (NativeOrderedDoubleCapCommon.primitive m hm F a b k E) := by
  unfold suffixCommonPrimitive NativeRawStage101Bridge.suffixPrimitive NativeOrderedScalarPullback.primitive
  abel

theorem suffix_remaining_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (index m a b k)
      (suffixCommonPrimitive m hm F a b k E) = 0 := by
  rw [suffix_cancelled_decomposition]
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)).op).f _).hom (_ - _) = 0
  simp only [map_sub, map_add]
  change cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (index m a b k) (NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E) +
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (index m a b k) (NativeRawReindexedComparison.suffixPrimitive m hm F a b k E) -
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (index m a b k) (cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (index m a b k)
      (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)) = 0
  rw [suffix_double_zero, suffix_reindexed_zero, suffix_ordered_zero]
  simp only [add_zero, sub_self]

theorem suffix_common_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (suffixCommonPrimitive m hm F a b k E) = 0 := by
  fin_cases i
  · rw [← NativeOriginalClockFaceReduction.suffix_face_reduction]
    exact NativeOriginalClockFaceReduction.suffix_total_face_zero m hm F a b k E 0 (Or.inl rfl)
  · rw [← NativeOriginalClockFaceReduction.suffix_face_reduction]
    exact NativeOriginalClockFaceReduction.suffix_total_face_zero m hm F a b k E 1 (Or.inr rfl)
  · exact suffix_remaining_zero m hm F a b k E true
  · exact suffix_remaining_zero m hm F a b k E false

theorem suffix_original_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (suffixOriginalPrimitive m hm F a b k E) = 0 := by
  rw [NativeOriginalClockFaceReduction.suffix_face_reduction]
  exact suffix_common_face_zero m hm F a b k E i

theorem suffix_relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : (i : Fin 4) → coeff ⟶ (chains (TopCat.of (NativeRawTimeSquareBoundary.face (m + 1) i))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      ∑ i : Fin 4, d i ≫ (push (SupportedCap.subspaceMap (source (m + 1))
        (NativeRawTimeSquareBoundary.face (m + 1) i))).f (index m a b k)) :
    c ≫ NativeRawOriginalScalarReduction.suffixOriginal m hm F a b k E =
      c ≫ suffixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (suffix_original_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    suffixOriginalPrimitive m hm F a b k E) = _ at hb
  have hz (i : Fin 4) : (push (SupportedCap.subspaceMap (source (m + 1))
      (NativeRawTimeSquareBoundary.face (m + 1) i))).f (index m a b k) ≫ suffixOriginalPrimitive m hm F a b k E = 0 :=
    suffix_original_face_zero m hm F a b k E i
  rw [← Category.assoc, hc, Preadditive.sum_comp] at hb
  simp only [Category.assoc, hz, comp_zero, Finset.sum_const_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.NativeOriginalAllTimeFaces
