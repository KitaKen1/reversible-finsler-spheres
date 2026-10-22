module

public import Finsler.Loop.NativeSequentialTestedFaces
public import Finsler.Loop.NativeSequentialDoubleCapOutputComparison
public import Finsler.Loop.NativeRawTimeSquareBoundary

/-! The SAME Stage97 GH output-substitution primitives vanish on EACH
of the four genuine raw time faces. This concerns that actual output
correction, not the additional cap-order/pullback corrections of Stage103. -/
@[expose] public section
namespace Finsler.NativeSequentialOutputFaces
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
open Finsler.NativeSequentialDoubleCapOutputComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_outer_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (outerFace (m + 1) t)) _
      (prefixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialTestedFaces.prefix_outer_zero m hm F _ _ t ht

theorem suffix_outer_zero (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (outerFace (m + 1) t)) _
      (suffixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialTestedFaces.suffix_outer_zero m hm F _ _ t ht

theorem prefix_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 0)) _
      (prefixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialTestedFaces.prefix_inner_zero m hm F _ _

theorem suffix_inner_one :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 1)) _
      (suffixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialTestedFaces.suffix_inner_one m hm F _ _

theorem prefix_inner_one :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 1)) _
      (prefixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialTestedFaces.prefix_seam_zero m hm F _ _
    (NativeSequentialGHGlobalComparison.prefix_collar_zero m hm F a b k E)

theorem suffix_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 0)) _
      (suffixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialTestedFaces.suffix_seam_zero m hm F _ _
    (NativeSequentialGHGlobalComparison.suffix_collar_zero m hm F a b k E)

theorem prefix_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i)) _
      (prefixPrimitive m hm F a b k E) = 0 := by
  fin_cases i
  · exact prefix_inner_zero m hm F a b k E
  · exact prefix_outer_zero m hm F a b k E 1 (Or.inr rfl)
  · exact prefix_inner_one m hm F a b k E
  · exact prefix_outer_zero m hm F a b k E 0 (Or.inl rfl)

theorem suffix_face_zero (i : Fin 4) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (NativeRawTimeSquareBoundary.face (m + 1) i)) _
      (suffixPrimitive m hm F a b k E) = 0 := by
  fin_cases i
  · exact suffix_inner_zero m hm F a b k E
  · exact suffix_outer_zero m hm F a b k E 1 (Or.inr rfl)
  · exact suffix_inner_one m hm F a b k E
  · exact suffix_outer_zero m hm F a b k E 0 (Or.inl rfl)

end
end Finsler.NativeSequentialOutputFaces
