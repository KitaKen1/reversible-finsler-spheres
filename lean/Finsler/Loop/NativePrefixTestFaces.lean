module

public import Finsler.Loop.SupportedRightTestOrder
public import Finsler.Loop.NativePrefixTestOrder
public import Finsler.Loop.NativeRawTimeSquareBoundary

/-! The SAME right-test subdivision primitive is zero on all four
actual prefix time faces: inner u=0 by Thom, inner u=1 by the short
middle GH test, and outer endpoints by the actual first Thom cut. -/
@[expose] public section
namespace Finsler.NativePrefixTestFaces
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
open Finsler.NativePrefixTestOrder
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem psi_seam_zero : cochainPullback
    (restriction (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 1))
      ((SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 1)) ⁻¹' near m hm F)
      (near m hm F) (fun _ h => h)) (pairDegree m a b) (psi m hm F a b) = 0 := by
  let f := restriction (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 1))
    ((SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 1)) ⁻¹' near m hm F)
    (near m hm F) (fun _ h => h)
  have hz : cochainPullback (f ≫ nearTriple m hm F ≫ NativeTripleGHTest.middle (m + 1))
      (NativeGHPowers.degree m b) (NativeClosingArcPowerVanishing.powerCocycle m hm F b) = 0 := by
    have hs : cochainPullback (SupportedCap.subspaceMap (Loops (m + 1))
        (SelfCutOscillation.short F (NativeClosingArcPowerVanishing.supportScale m hm F)))
        (NativeGHPowers.degree m b) (NativeClosingArcPowerVanishing.powerCocycle m hm F b) = 0 :=
      NativeClosingArcPowerVanishing.powerCocycle_supported m hm F b
    apply NativeSupportedStageCarrier.map_zero
      (f ≫ nearTriple m hm F ≫ NativeTripleGHTest.middle (m + 1))
      (SelfCutOscillation.short F (NativeClosingArcPowerVanishing.supportScale m hm F))
      _ (NativeGHPowers.degree m b) (NativeClosingArcPowerVanishing.powerCocycle m hm F b) hs
    intro z
    have h : prefixFinal m hm F (f z) ∈ NativeSequentialCollarGeometry.prefixCollar m hm F := by
      apply NativeSequentialCollarGeometry.prefix_seam_in_collar m hm F ⟨prefixFinal m hm F (f z), ?_⟩
      have ht : z.val.val.val.2 = 1 := z.val.property
      change (z.val.val.val.2 : ℝ) = 1
      exact congrArg (fun t : ClosedInterval => (t : ℝ)) ht
    exact h.1
  change cochainPullback f _ (psi m hm F a b) = 0
  rw [psi, cochainCup_naturality]
  have hz' := hz
  rw [pullback_comp] at hz'
  rw [hz', cochainCup_zero_right]

theorem primitive_inner_zero : cochainPullback
    (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 0)) (index m a b k)
      (primitive m hm F a b k E) = 0 :=
  SupportedRightTestOrder.primitive_thom_zero (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) k m (pairDegree m a b)
    (alpha m hm F k E) (theta m hm F) (theta_supported m hm F) (psi m hm F a b)
    (outerInnerFace m hm F 0) (prefix_thom_inner_zero m hm F)

theorem primitive_inner_one : cochainPullback
    (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 1)) (index m a b k)
      (primitive m hm F a b k E) = 0 :=
  SupportedRightTestOrder.primitive_test_zero (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F) k m (pairDegree m a b)
    (alpha m hm F k E) (theta m hm F) (theta_supported m hm F) (psi m hm F a b)
    (outerInnerFace m hm F 1) (psi_seam_zero m hm F a b)

theorem global_outer_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (outerFace (m + 1) t)) ((m + 1) + index m a b k)
      (globalPrimitive m hm F a b k E) = 0 := by
  have h := congrArg (fun c => c ≫ primitive m hm F a b k E)
    (first_endpoint m hm F t ht (index m a b k))
  simp only [Category.assoc, zero_comp] at h
  exact h

theorem global_inner_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 0)) ((m + 1) + index m a b k)
      (globalPrimitive m hm F a b k E) = 0 :=
  NativeSupportedStageCarrier.output_zero (firstParameter (m + 1)) (by omega)
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)
    (innerFace (m + 1) 0) (index m a b k) (primitive m hm F a b k E) (primitive_inner_zero m hm F a b k E)

theorem global_inner_one : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 1)) ((m + 1) + index m a b k)
      (globalPrimitive m hm F a b k E) = 0 :=
  NativeSupportedStageCarrier.output_zero (firstParameter (m + 1)) (by omega)
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)
    (innerFace (m + 1) 1) (index m a b k) (primitive m hm F a b k E) (primitive_inner_one m hm F a b k E)

theorem global_face_zero (i : Fin 4) : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
      ((m + 1) + index m a b k) (globalPrimitive m hm F a b k E) = 0 := by
  fin_cases i
  · exact global_inner_zero m hm F a b k E
  · exact global_outer_zero m hm F a b k E 1 (Or.inr rfl)
  · exact global_inner_one m hm F a b k E
  · exact global_outer_zero m hm F a b k E 0 (Or.inl rfl)

end
end Finsler.NativePrefixTestFaces
