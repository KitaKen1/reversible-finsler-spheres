module

public import Finsler.Loop.NativeOriginalClockSquare
public import Finsler.Loop.NativeOrderedDoubleCutClockComparison

/-! The SAME Stage95 input at the actual source-square degree, with
literal endpoint/diagonal carrier zero and all four raw face restrictions.
No changed cohomology representative or test is substituted. -/
@[expose] public section
namespace Finsler.NativeOrderedSquareInput
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeOriginalClockSquare Finsler.NativeRawClockSupportedAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem pre_pullback {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (T : singularCochainGroup (ZMod 2) Y j) :
    CochainDegreeTransport.pre X h (cochainPullback f j T) =
      cochainPullback f i (CochainDegreeTransport.pre Y h T) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def input : singularCochainGroup (ZMod 2) (NativeOrderedDoubleCapCommon.source m) (squareDegree m a b k + 3) :=
  CochainDegreeTransport.pre _ (congrArg (fun n => n + 1) (primitive_degree m hm a b k))
    (CochainDegreeTransport.pre _ (NativeOrderedDoubleCapCommon.degree_match m a b k)
      (NativeOrderedDoubleCutSupported.cochain m hm F a b k E))

theorem input_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (input m hm F a b k E) = 0 :=
  CochainDegreeTransport.closed _ _ _ (CochainDegreeTransport.closed _ _ _
    (NativeOrderedDoubleCutSupported.cochain_closed m hm F a b k E hE))

theorem input_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (NativeOrderedDoubleCapCommon.source m) (NativeOrderedDoubleCutSupported.diagonal m))
    (squareDegree m a b k + 3) (input m hm F a b k E) = 0 :=
  NativeOrderedDoubleCutClockComparison.pullback_pre_zero _ _ _
    (NativeOrderedDoubleCutClockComparison.pullback_pre_zero _ _ _
      (NativeOrderedDoubleCutSupported.cochain_diagonal_zero m hm F a b k E))

theorem input_diagonal_map_zero : cochainPullback
    (Loops (m + 1) ◁ OrderedDoubleCutTriangle.diagonal) (squareDegree m a b k + 3) (input m hm F a b k E) = 0 := by
  rw [← NativeOrderedDoubleCutClockComparison.diagonal_factor, pullback_comp, input_diagonal_zero]
  change (push _).f _ ≫ 0 = 0
  exact comp_zero

theorem input_endpoint_zero (last : Bool) : cochainPullback
    (SupportedCap.subspaceMap (NativeOrderedDoubleCapCommon.source m) (NativeOrderedEndpointCarrier.endpoint m last))
    (squareDegree m a b k + 3) (input m hm F a b k E) = 0 := by
  unfold input
  apply NativeOrderedDoubleCutClockComparison.pullback_pre_zero
  rw [NativeOrderedDoubleCapCommon.stage95_compare]
  rcases NativeOrderedEndpointCarrier.thom_zero m hm F last with h | h
  · exact DoubleCapThomCarrier.sequential_first_zero (NativeOrderedDoubleCapCommon.source m)
      (NativeOrderedDoubleCapCommon.firstFar m hm F) (NativeOrderedDoubleCapCommon.firstNear m hm F)
      (NativeOrderedDoubleCapCommon.lastFar m hm F) (NativeOrderedDoubleCapCommon.lastNear m hm F)
      (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
      (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
      (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
      (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
      (m + 1) m (NativeOrderedDoubleCapCommon.testDegree m a b k)
      (NativeOrderedDoubleCapCommon.firstThom m hm F) (NativeOrderedDoubleCapCommon.lastThom m hm F)
      (NativeOrderedDoubleCapCommon.first_supported m hm F) (NativeOrderedDoubleCapCommon.last_supported m hm F)
      (NativeOrderedDoubleCapCommon.test m hm F a b k E) (NativeOrderedEndpointCarrier.endpoint m last) h
  · exact DoubleCapThomCarrier.sequential_second_zero (NativeOrderedDoubleCapCommon.source m)
      (NativeOrderedDoubleCapCommon.firstFar m hm F) (NativeOrderedDoubleCapCommon.firstNear m hm F)
      (NativeOrderedDoubleCapCommon.lastFar m hm F) (NativeOrderedDoubleCapCommon.lastNear m hm F)
      (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
      (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
      (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
      (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
      (m + 1) m (NativeOrderedDoubleCapCommon.testDegree m a b k)
      (NativeOrderedDoubleCapCommon.firstThom m hm F) (NativeOrderedDoubleCapCommon.lastThom m hm F)
      (NativeOrderedDoubleCapCommon.first_supported m hm F) (NativeOrderedDoubleCapCommon.last_supported m hm F)
      (NativeOrderedDoubleCapCommon.test m hm F a b k E) (NativeOrderedEndpointCarrier.endpoint m last) h

include hm in
theorem clock_degree : squareDegree m a b k = NativeOrderedDoubleCutClockComparison.clockDegree m a b k := by
  have h := (congrArg (fun n => n + 1) (primitive_degree m hm a b k)).trans
    (NativeOrderedDoubleCapCommon.degree_match m a b k)
  have h' := NativeOrderedDoubleCutClockComparison.degree_match m hm a b k
  omega

theorem input_existing_clock : input m hm F a b k E =
    CochainDegreeTransport.pre _ (congrArg (fun n => n + 3) (clock_degree m hm a b k))
      (NativeOrderedDoubleCutClockComparison.input m hm F a b k E) := by
  unfold input NativeOrderedDoubleCutClockComparison.input
  exact (pre_trans _ _ _ _).trans
    (pre_trans (NativeOrderedDoubleCapCommon.source m)
      (congrArg (fun n => n + 3) (clock_degree m hm a b k))
      (NativeOrderedDoubleCutClockComparison.degree_match m hm a b k)
      (NativeOrderedDoubleCutSupported.cochain m hm F a b k E)).symm

theorem prefix_input : prefixOrdered m hm F a b k E =
    cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (squareDegree m a b k + 3) (input m hm F a b k E) := by
  unfold prefixOrdered NativeOriginalTwoStageClockComparison.prefixOrderedInput input
  rw [pre_pullback]

theorem prefix_face_zero (i : Fin 4) : cochainPullback
    (SupportedCap.subspaceMap (NativeSequentialSupportedStages.source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
    (squareDegree m a b k + 3) (prefixOrdered m hm F a b k E) = 0 := by
  rw [prefix_input]
  fin_cases i
  · exact pullback_support (NativeRawClockMaps.prefixClock (m + 1)) _
      (NativeOrderedEndpointCarrier.endpoint m false) (NativeRawEndpointGeometry.prefix_maps m false) _ _
      (input_endpoint_zero m hm F a b k E false)
  · exact pullback_support (NativeRawClockMaps.prefixClock (m + 1)) _
      (NativeOrderedEndpointCarrier.endpoint m true) (NativeRawEndpointGeometry.prefix_maps m true) _ _
      (input_endpoint_zero m hm F a b k E true)
  · exact pullback_support (NativeRawClockMaps.prefixClock (m + 1)) _
      (NativeOrderedDoubleCutSupported.diagonal m)
      (fun _ h => NativeOriginalClockFaceReduction.prefix_face_diagonal m 2 (Or.inl rfl) h) _ _
      (input_diagonal_zero m hm F a b k E)
  · exact pullback_support (NativeRawClockMaps.prefixClock (m + 1)) _
      (NativeOrderedDoubleCutSupported.diagonal m)
      (fun _ h => NativeOriginalClockFaceReduction.prefix_face_diagonal m 3 (Or.inr rfl) h) _ _
      (input_diagonal_zero m hm F a b k E)

theorem prefix_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (prefixOrdered m hm F a b k E) = 0 := by
  rw [prefix_input]
  exact pullback_closed _ _ _ (input_closed m hm F a b k E hE)

theorem prefix_square (n : ℕ) : NativeRawTimeSquareBoundary.squareMap n ≫ NativeRawClockMaps.prefixClock n =
    Loops n ◁ OrderedDoubleCutTimes.leftClock := rfl

theorem suffix_input : suffixOrdered m hm F a b k E =
    cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (squareDegree m a b k + 3) (input m hm F a b k E) := by
  unfold suffixOrdered NativeOriginalTwoStageClockComparison.suffixOrderedInput input
  rw [pre_pullback]

theorem suffix_face_zero (i : Fin 4) : cochainPullback
    (SupportedCap.subspaceMap (NativeSequentialSupportedStages.source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i))
    (squareDegree m a b k + 3) (suffixOrdered m hm F a b k E) = 0 := by
  rw [suffix_input]
  fin_cases i
  · exact pullback_support (NativeRawClockMaps.suffixClock (m + 1)) _
      (NativeOrderedDoubleCutSupported.diagonal m)
      (fun _ h => NativeOriginalClockFaceReduction.suffix_face_diagonal m 0 (Or.inl rfl) h) _ _
      (input_diagonal_zero m hm F a b k E)
  · exact pullback_support (NativeRawClockMaps.suffixClock (m + 1)) _
      (NativeOrderedDoubleCutSupported.diagonal m)
      (fun _ h => NativeOriginalClockFaceReduction.suffix_face_diagonal m 1 (Or.inr rfl) h) _ _
      (input_diagonal_zero m hm F a b k E)
  · exact pullback_support (NativeRawClockMaps.suffixClock (m + 1)) _
      (NativeOrderedEndpointCarrier.endpoint m true) (NativeRawEndpointGeometry.suffix_maps m true) _ _
      (input_endpoint_zero m hm F a b k E true)
  · exact pullback_support (NativeRawClockMaps.suffixClock (m + 1)) _
      (NativeOrderedEndpointCarrier.endpoint m false) (NativeRawEndpointGeometry.suffix_maps m false) _ _
      (input_endpoint_zero m hm F a b k E false)

theorem suffix_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (suffixOrdered m hm F a b k E) = 0 := by
  rw [suffix_input]
  exact pullback_closed _ _ _ (input_closed m hm F a b k E hE)

theorem suffix_square (n : ℕ) : NativeRawTimeSquareBoundary.squareMap n ≫ NativeRawClockMaps.suffixClock n =
    Loops n ◁ OrderedDoubleCutTimes.rightClock := rfl

end
end Finsler.NativeOrderedSquareInput
