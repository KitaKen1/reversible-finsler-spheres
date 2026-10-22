module

public import Finsler.Loop.SupportedTestOrderThomCarrier
public import Finsler.Loop.NativeSuffixTestOrder
public import Finsler.Loop.NativeRawTimeSquareBoundary

/-! All four actual time-face restrictions of the SAME original suffix
test/Thom commutation primitive. The seam uses the actual short middle
GH test; the opposite inner endpoint uses the actual Thom factor. -/
@[expose] public section
namespace Finsler.NativeSuffixTestFaces
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
open Finsler.NativeSuffixTestOrder
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem psi_seam_zero : cochainPullback
    (restriction (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 0))
      ((SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 0)) ⁻¹' near m hm F)
      (near m hm F) (fun _ h => h)) (restDegree m b k) (psi m hm F b k E) = 0 := by
  let f := restriction (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 0))
    ((SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 0)) ⁻¹' near m hm F)
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
    have h : suffixFinal m hm F (f z) ∈ NativeSequentialCollarGeometry.suffixCollar m hm F := by
      apply NativeSequentialCollarGeometry.suffix_seam_in_collar m hm F ⟨suffixFinal m hm F (f z), ?_⟩
      have ht : z.val.val.val.2 = 0 := z.val.property
      change (z.val.val.val.2 : ℝ) = 0
      exact congrArg (fun t : ClosedInterval => (t : ℝ)) ht
    exact h.1
  change cochainPullback f _ (psi m hm F b k E) = 0
  rw [psi, cochainCup_naturality, ← pullback_comp, hz, cochainCup_zero_left]

theorem primitive_inner_zero : cochainPullback
    (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 0)) (index m a b k)
      (primitive m hm F a b k E) = 0 :=
  primitive_carrier_zero m hm F a b k E (outerInnerFace m hm F 0) (psi_seam_zero m hm F b k E)

theorem primitive_inner_one : cochainPullback
    (SupportedCap.subspaceMap (space m hm F) (outerInnerFace m hm F 1)) (index m a b k)
      (primitive m hm F a b k E) = 0 :=
  SupportedTestOrderThomCarrier.primitive_zero (space m hm F) (far m hm F) (near m hm F)
    (far_open m hm F) (near_open m hm F) (cover m hm F)
    (NativeGHPowers.degree m a) m (restDegree m b k)
    (alpha m hm F a) (theta m hm F) (theta_supported m hm F) (psi m hm F b k E)
    (outerInnerFace m hm F 1) (suffix_thom_inner_one m hm F)

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
end Finsler.NativeSuffixTestFaces
