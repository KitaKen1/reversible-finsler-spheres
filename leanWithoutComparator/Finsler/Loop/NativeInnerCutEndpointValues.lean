module

public import Finsler.Loop.NormalizedCutScalarCarrier
public import Finsler.Loop.NativeInnerCutPullback
public import Finsler.Loop.NativePrefixTestFaces
public import Finsler.Loop.NativeSuffixTestFaces

/-! Both actual inner-cut values, including the ORIGINAL ambient cut,
vanish at both raw-half endpoints. At the seam the original retained
or tested loop is genuinely short. Consequently the SAME subdivision
pullback-comparison primitives have zero restrictions on all four faces. -/
@[expose] public section
namespace Finsler.NativeInnerCutEndpointValues
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
open Finsler.NativeInnerCutPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_local_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      ((m + 1) + NativePrefixTestOrder.pairDegree m a b) (prefixLocal m hm F a b) = 0 := by
  rw [prefix_local]
  rcases ht with rfl | rfl
  · have h := congrArg (fun c => c ≫ NativePrefixTestOrder.psi m hm F a b)
      (prefix_inner_zero m hm F (NativePrefixTestOrder.pairDegree m a b))
    simp only [Category.assoc, zero_comp] at h
    exact h
  · exact SupportedCutCochainCarrierZero.subspace_cochain_zero (outerSpace m hm F)
      (NativePrefixTestOrder.far m hm F) (NativePrefixTestOrder.near m hm F) (outerInnerFace m hm F 1)
      (NativePrefixTestOrder.far_open m hm F) (NativePrefixTestOrder.near_open m hm F)
      (NativePrefixTestOrder.cover m hm F) (m + 1) (NativePrefixTestOrder.pairDegree m a b)
      (NativePrefixTestOrder.theta m hm F) (NativePrefixTestOrder.theta_supported m hm F)
      (NativePrefixTestOrder.psi m hm F a b) (NativePrefixTestFaces.psi_seam_zero m hm F a b)

theorem suffix_local_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      ((m + 1) + NativeSuffixTestOrder.restDegree m b k) (suffixLocal m hm F b k E) = 0 := by
  rw [suffix_local]
  rcases ht with rfl | rfl
  · exact SupportedCutCochainCarrierZero.subspace_cochain_zero (outerSpace m hm F)
      (NativeSuffixTestOrder.far m hm F) (NativeSuffixTestOrder.near m hm F) (outerInnerFace m hm F 0)
      (NativeSuffixTestOrder.far_open m hm F) (NativeSuffixTestOrder.near_open m hm F)
      (NativeSuffixTestOrder.cover m hm F) (m + 1) (NativeSuffixTestOrder.restDegree m b k)
      (NativeSuffixTestOrder.theta m hm F) (NativeSuffixTestOrder.theta_supported m hm F)
      (NativeSuffixTestOrder.psi m hm F b k E) (NativeSuffixTestFaces.psi_seam_zero m hm F b k E)
  · have h := congrArg (fun c => c ≫ NativeSuffixTestOrder.psi m hm F b k E)
      (suffix_inner_one m hm F (NativeSuffixTestOrder.restDegree m b k))
    simp only [Category.assoc, zero_comp] at h
    exact h

theorem prefix_original_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      ((m + 1) + NativePrefixTestOrder.pairDegree m a b) (prefixOriginal m hm F a b) = 0 := by
  rcases ht with rfl | rfl
  · apply NormalizedCutScalarCarrier.original_time_zero _ _ _ _ _ _ _ _ _ _ 0
    · intro x hx
      apply Subtype.ext
      change (x.val.2 : ℝ) / 2 = 0
      change x.val.2 = 0 at hx
      rw [hx]
      norm_num
    · exact NormalizedSelfCut.time_zero _ _ _
  · apply NormalizedCutScalarCarrier.original_retained_zero _ _ _ _ _ _ _ _ _ _
      (SelfCutOscillation.short F (NativeClosingArcPowerVanishing.supportScale m hm F))
      (NativeClosingArcPowerVanishing.powerCocycle_supported m hm F b)
    intro x hx hn
    have h : prefixFinal m hm F ⟨x, hn⟩ ∈ NativeSequentialCollarGeometry.prefixCollar m hm F := by
      apply NativeSequentialCollarGeometry.prefix_seam_in_collar m hm F ⟨prefixFinal m hm F ⟨x, hn⟩, ?_⟩
      change x.val.2 = 1 at hx
      change (x.val.2 : ℝ) = 1
      exact congrArg (fun u : ClosedInterval => (u : ℝ)) hx
    exact h.1

theorem suffix_original_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      ((m + 1) + NativeSuffixTestOrder.restDegree m b k) (suffixOriginal m hm F b k E) = 0 := by
  rcases ht with rfl | rfl
  · apply NormalizedCutScalarCarrier.original_tested_zero _ _ _ _ _ _ _ _ _ _
      (SelfCutOscillation.short F (NativeClosingArcPowerVanishing.supportScale m hm F))
      (NativeClosingArcPowerVanishing.powerCocycle_supported m hm F b)
    intro x hx hn
    have h : suffixFinal m hm F ⟨x, hn⟩ ∈ NativeSequentialCollarGeometry.suffixCollar m hm F := by
      apply NativeSequentialCollarGeometry.suffix_seam_in_collar m hm F ⟨suffixFinal m hm F ⟨x, hn⟩, ?_⟩
      change x.val.2 = 0 at hx
      change (x.val.2 : ℝ) = 0
      exact congrArg (fun u : ClosedInterval => (u : ℝ)) hx
    exact h.1
  · apply NormalizedCutScalarCarrier.original_time_zero _ _ _ _ _ _ _ _ _ _ 1
    · intro x hx
      apply Subtype.ext
      change (1 + (x.val.2 : ℝ)) / 2 = 1
      change x.val.2 = 1 at hx
      rw [hx]
      norm_num
    · exact NormalizedSelfCut.time_one _ _ _

theorem prefix_primitive_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      (m + NativePrefixTestOrder.pairDegree m a b) (prefixPrimitive m hm F a b) = 0 :=
  NormalizedCutScalarCarrier.primitive_zero _ _ _ _ _ _ _ _ _ _
    (prefix_local_endpoint m hm F a b t ht) (prefix_original_endpoint m hm F a b t ht)

theorem suffix_primitive_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      (m + NativeSuffixTestOrder.restDegree m b k) (suffixPrimitive m hm F b k E) = 0 :=
  NormalizedCutScalarCarrier.primitive_zero _ _ _ _ _ _ _ _ _ _
    (suffix_local_endpoint m hm F b k E t ht) (suffix_original_endpoint m hm F b k E t ht)

end
end Finsler.NativeInnerCutEndpointValues
