module

public import Finsler.Loop.NativeGHProductPullback
public import Finsler.Loop.NativeGHOuterTimeComparison

/-! The target of the product-cover comparison is literally the SAME
Stage108 raw global interleaved cochain, in BOTH branches, with every
source-degree transport retained. -/
@[expose] public section
namespace Finsler.NativeGHProductRawAlignment
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests Finsler.NativeGHProductPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

abbrev squareDegree := NativeGHOuterTimeComparison.squareDegree

theorem input_degree (m : ℕ) (hm : 2 ≤ m) (a b k : ℕ) (side : Bool) :
    squareDegree m a b k + 3 = m + index m a b k side + 1 + 1 := by
  have h := NativeGHOuterTimeComparison.input_degree m hm a b k side
  change squareDegree m a b k + 2 = m + index m a b k side + 1 at h
  omega

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

def rawInterleaved := (NativeSequentialSupportedStages.firstOperation m hm F).component (index m a b k side + 1) ≫
  rawTest m hm F a b k E side

def stage108 : singularCochainGroup (ZMod 2) (raw m) (squareDegree m a b k + 3) :=
  match side with
  | false => NativePrefixInterleavedSquare.interleaved m hm F a b k E
  | true => NativeSuffixInterleavedSquare.interleaved m hm F a b k E

theorem original_raw : originalValue m hm F a b k E side =
    cochainPullback (rawSource m) (m + index m a b k side + 1 + 1)
      (CochainDegreeTransport.pre (raw m) (show m + index m a b k side + 1 + 1 = (m + 1) + (index m a b k side + 1) by omega)
        (rawInterleaved m hm F a b k E side)) := by
  apply congrArg (cochainPullback (rawSource m) _)
  exact (NativeSuffixPostponedAlignment.pre_cut (raw m) (farRaw m hm F) (nearRaw m hm F)
    (farRawOpen m hm F) (nearRawOpen m hm F) (rawCover m hm F) (m + 1) (index m a b k side + 1)
    (m + index m a b k side + 1 + 1) ((m + 1) + (index m a b k side + 1)) (by omega) rfl (by omega)
    (theta m hm F) (thetaSupport m hm F) (rawTest m hm F a b k E side)).symm

theorem original_stage108 : CochainDegreeTransport.pre (RightIntervalCochain.space (base m))
    (input_degree m hm a b k side) (originalValue m hm F a b k E side) =
    cochainPullback (rawSource m) (squareDegree m a b k + 3) (stage108 m hm F a b k E side) := by
  rw [original_raw, ← NativeSuffixPostponedAlignment.pre_pullback, NativeRawClockSupportedAlignment.pre_trans]
  cases side <;> rfl

end
end Finsler.NativeGHProductRawAlignment
