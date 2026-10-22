module

public import Finsler.Loop.NativeSequentialOutputFaces
public import Finsler.Loop.NativeOriginalTwoStageClockComparison
public import Finsler.Loop.NativeRawClockScalarComparison

/-! Isolate the remaining Stage103 boundary obligation: on EVERY actual
time face its original-output total primitive restricts to the SAME
common-output primitive. On the two faces carried by the inverse diagonal,
both are zero. No zero on the closed union or the other faces is claimed. -/
@[expose] public section
namespace Finsler.NativeOriginalClockFaceReduction
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages
open Finsler.NativeRawClockSupportedAlignment Finsler.NativeOriginalTwoStageClockComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_primitive_decomposition : prefixOriginalPrimitive m hm F a b k E =
    CochainDegreeTransport.pre (source (m + 1)) (NativeRawOriginalScalarReduction.primitive_degree m hm a b k)
      (NativeSequentialDoubleCapOutputComparison.prefixPrimitive m hm F a b k E) +
        prefixCommonPrimitive m hm F a b k E := by
  unfold prefixOriginalPrimitive NativeRawOriginalScalarReduction.prefixPrimitive prefixCommonPrimitive
  abel

theorem prefix_face_reduction (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (prefixOriginalPrimitive m hm F a b k E) =
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (prefixCommonPrimitive m hm F a b k E) := by
  have hz := NativeSequentialGHGlobalComparison.pullback_pre_zero
    (NativeRawOriginalScalarReduction.primitive_degree m hm a b k) _ _
    (NativeSequentialOutputFaces.prefix_face_zero m hm F a b k E i)
  rw [prefix_primitive_decomposition]
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i)).op).f _).hom (_ + _) = _
  rw [map_add]
  change cochainPullback _ _ (CochainDegreeTransport.pre _ _ _) + _ = _
  rw [hz, zero_add]
  rfl

theorem prefix_face_diagonal (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    NativeRawTimeSquareBoundary.face (m + 1) i ⊆ NativeRawDoubleCapCommon.prefixDiagonal m := by
  intro z hz
  apply (NativeRawClockScalarComparison.prefix_diagonal_iff m z).mpr
  rcases hi with rfl | rfl
  · apply Or.inr
    change z.2 = 1 at hz
    exact congrArg (fun t : IntervalSobolev.ClosedInterval => (t : ℝ)) hz
  · apply Or.inl
    change z.1.1 = 0 at hz
    exact congrArg (fun t : IntervalSobolev.ClosedInterval => (t : ℝ)) hz

theorem prefix_total_face_zero (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (prefixOriginalPrimitive m hm F a b k E) = 0 := by
  rw [prefix_face_reduction]
  exact NativeSupportedStageCarrier.map_zero
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i)) (NativeRawDoubleCapCommon.prefixDiagonal m)
    (fun z => prefix_face_diagonal m i hi z.property) _ _
      (prefix_common_primitive_diagonal_zero m hm F a b k E)

theorem suffix_primitive_decomposition : suffixOriginalPrimitive m hm F a b k E =
    CochainDegreeTransport.pre (source (m + 1)) (NativeRawOriginalScalarReduction.primitive_degree m hm a b k)
      (NativeSequentialDoubleCapOutputComparison.suffixPrimitive m hm F a b k E) +
        suffixCommonPrimitive m hm F a b k E := by
  unfold suffixOriginalPrimitive NativeRawOriginalScalarReduction.suffixPrimitive suffixCommonPrimitive
  abel

theorem suffix_face_reduction (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (suffixOriginalPrimitive m hm F a b k E) =
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (suffixCommonPrimitive m hm F a b k E) := by
  have hz := NativeSequentialGHGlobalComparison.pullback_pre_zero
    (NativeRawOriginalScalarReduction.primitive_degree m hm a b k) _ _
    (NativeSequentialOutputFaces.suffix_face_zero m hm F a b k E i)
  rw [suffix_primitive_decomposition]
  change ((singularCochainComplexZMod2.map
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i)).op).f _).hom (_ + _) = _
  rw [map_add]
  change cochainPullback _ _ (CochainDegreeTransport.pre _ _ _) + _ = _
  rw [hz, zero_add]
  rfl

theorem suffix_face_diagonal (i : Fin 4) (hi : i = 0 ∨ i = 1) :
    NativeRawTimeSquareBoundary.face (m + 1) i ⊆ NativeRawDoubleCapCommon.suffixDiagonal m := by
  intro z hz
  apply (NativeRawClockScalarComparison.suffix_diagonal_iff m z).mpr
  rcases hi with rfl | rfl
  · apply Or.inr
    change z.2 = 0 at hz
    exact congrArg (fun t : IntervalSobolev.ClosedInterval => (t : ℝ)) hz
  · apply Or.inl
    change z.1.1 = 1 at hz
    exact congrArg (fun t : IntervalSobolev.ClosedInterval => (t : ℝ)) hz

theorem suffix_total_face_zero (i : Fin 4) (hi : i = 0 ∨ i = 1) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      (index m a b k) (suffixOriginalPrimitive m hm F a b k E) = 0 := by
  rw [suffix_face_reduction]
  exact NativeSupportedStageCarrier.map_zero
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i)) (NativeRawDoubleCapCommon.suffixDiagonal m)
    (fun z => suffix_face_diagonal m i hi z.property) _ _
      (suffix_common_primitive_diagonal_zero m hm F a b k E)

theorem prefix_two_face_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (NativeRawTimeSquareBoundary.face (m + 1) 2))).X (index m a b k))
    (e : coeff ⟶ (chains (TopCat.of (NativeRawTimeSquareBoundary.face (m + 1) 3))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 2))).f (index m a b k) +
      e ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 3))).f (index m a b k)) :
    c ≫ NativeRawOriginalScalarReduction.prefixOriginal m hm F a b k E =
      c ≫ prefixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (prefix_original_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    prefixOriginalPrimitive m hm F a b k E) = _ at hb
  have hd : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 2))).f (index m a b k) ≫
      prefixOriginalPrimitive m hm F a b k E = 0 := prefix_total_face_zero m hm F a b k E 2 (Or.inl rfl)
  have he : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 3))).f (index m a b k) ≫
      prefixOriginalPrimitive m hm F a b k E = 0 := prefix_total_face_zero m hm F a b k E 3 (Or.inr rfl)
  rw [← Category.assoc, hc, Preadditive.add_comp, Category.assoc, Category.assoc, hd, he,
    comp_zero, comp_zero, add_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

theorem suffix_two_face_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of (NativeRawTimeSquareBoundary.face (m + 1) 0))).X (index m a b k))
    (e : coeff ⟶ (chains (TopCat.of (NativeRawTimeSquareBoundary.face (m + 1) 1))).X (index m a b k))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 0))).f (index m a b k) +
      e ≫ (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 1))).f (index m a b k)) :
    c ≫ NativeRawOriginalScalarReduction.suffixOriginal m hm F a b k E =
      c ≫ suffixOrderedInput m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (suffix_original_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    suffixOriginalPrimitive m hm F a b k E) = _ at hb
  have hd : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 0))).f (index m a b k) ≫
      suffixOriginalPrimitive m hm F a b k E = 0 := suffix_total_face_zero m hm F a b k E 0 (Or.inl rfl)
  have he : (push (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) 1))).f (index m a b k) ≫
      suffixOriginalPrimitive m hm F a b k E = 0 := suffix_total_face_zero m hm F a b k E 1 (Or.inr rfl)
  rw [← Category.assoc, hc, Preadditive.add_comp, Category.assoc, Category.assoc, hd, he,
    comp_zero, comp_zero, add_zero, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.NativeOriginalClockFaceReduction
