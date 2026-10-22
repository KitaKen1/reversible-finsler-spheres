module

public import Finsler.Loop.NativeOrderedScalarPullback
public import Finsler.Loop.NativeRawClockMaps

/-! BOTH actual original raw clocks instantiate the scalar pullback
comparison for the SAME Stage95 input and SAME GH tests. The genuine
source primitive and its full inverse-diagonal support are retained.
The remaining equality to complete interleaved sequential operations
and the high-power UNIT scalar have NOT been inferred. -/
@[expose] public section
namespace Finsler.NativeRawClockScalarComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeOrderedDoubleCapCommon
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def clock (n : ℕ) (branch : Bool) : NativeSequentialSupportedStages.source n ⟶
    NativeOrderedDoubleCutGeometry.source n :=
  if branch then NativeRawClockMaps.prefixClock n else NativeRawClockMaps.suffixClock n

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (branch : Bool)
  (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def localValue := NativeOrderedScalarPullback.localValue m hm F (clock (m + 1) branch) a b k E
def primitive := NativeOrderedScalarPullback.primitive m hm F (clock (m + 1) branch) a b k E

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (NativeSequentialSupportedStages.source (m + 1)) (index m a b k)
      (primitive m hm F branch a b k E) =
    cochainPullback (clock (m + 1) branch) (index m a b k + 1)
      (CochainDegreeTransport.pre (source m) (degree_match m a b k)
        (NativeOrderedDoubleCutSupported.cochain m hm F a b k E)) - localValue m hm F branch a b k E :=
  NativeOrderedScalarPullback.original_boundary m hm F (clock (m + 1) branch) a b k E hE

theorem primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (NativeSequentialSupportedStages.source (m + 1))
      ((clock (m + 1) branch) ⁻¹' NativeOrderedDoubleCutSupported.diagonal m)) (index m a b k)
    (primitive m hm F branch a b k E) = 0 :=
  NativeOrderedScalarPullback.primitive_diagonal_zero m hm F (clock (m + 1) branch) a b k E

theorem relative_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (NativeSequentialSupportedStages.source (m + 1))).X (index m a b k + 1))
    (d : coeff ⟶ (chains (TopCat.of ((clock (m + 1) branch) ⁻¹'
      NativeOrderedDoubleCutSupported.diagonal m))).X (index m a b k))
    (hc : c ≫ (chains (NativeSequentialSupportedStages.source (m + 1))).d (index m a b k + 1) (index m a b k) =
      d ≫ (push (SupportedCap.subspaceMap (NativeSequentialSupportedStages.source (m + 1))
        ((clock (m + 1) branch) ⁻¹' NativeOrderedDoubleCutSupported.diagonal m))).f (index m a b k)) :
    c ≫ cochainPullback (clock (m + 1) branch) (index m a b k + 1)
      (CochainDegreeTransport.pre (source m) (degree_match m a b k)
        (NativeOrderedDoubleCutSupported.cochain m hm F a b k E)) = c ≫ localValue m hm F branch a b k E :=
  NativeOrderedScalarPullback.relative_values_eq m hm F (clock (m + 1) branch) a b k E hE c d hc

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (NativeSequentialSupportedStages.source (m + 1))).X (index m a b k + 1))
    (hc : c ≫ (chains (NativeSequentialSupportedStages.source (m + 1))).d (index m a b k + 1) (index m a b k) = 0) :
    c ≫ cochainPullback (clock (m + 1) branch) (index m a b k + 1)
      (CochainDegreeTransport.pre (source m) (degree_match m a b k)
        (NativeOrderedDoubleCutSupported.cochain m hm F a b k E)) = c ≫ localValue m hm F branch a b k E := by
  apply relative_values_eq m hm F branch a b k E hE c 0
  rw [zero_comp]
  exact hc

theorem prefix_diagonal_iff (z : NativeSequentialSupportedStages.source (m + 1)) :
    NativeRawClockMaps.prefixClock (m + 1) z ∈ NativeOrderedDoubleCutSupported.diagonal m ↔
      (z.1.1 : ℝ) = 0 ∨ (z.2 : ℝ) = 1 := by
  change NativeSelfCutSegmentClocks.prefixTime z.1.1 z.2 = z.1.1 ↔ _
  rw [Subtype.ext_iff]
  change (z.1.1 : ℝ) * z.2 = (z.1.1 : ℝ) ↔ _
  constructor
  · intro h
    have hz : (z.1.1 : ℝ) * ((z.2 : ℝ) - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with ht | hu
    · exact Or.inl ht
    · exact Or.inr (sub_eq_zero.mp hu)
  · rintro (h | h)
    · rw [h, zero_mul]
    · rw [h, mul_one]

theorem suffix_diagonal_iff (z : NativeSequentialSupportedStages.source (m + 1)) :
    NativeRawClockMaps.suffixClock (m + 1) z ∈ NativeOrderedDoubleCutSupported.diagonal m ↔
      (z.1.1 : ℝ) = 1 ∨ (z.2 : ℝ) = 0 := by
  change z.1.1 = NativeSelfCutSegmentClocks.suffixTime z.1.1 z.2 ↔ _
  rw [Subtype.ext_iff]
  change (z.1.1 : ℝ) = (z.1.1 : ℝ) + (1 - z.1.1) * z.2 ↔ _
  constructor
  · intro h
    have hz : (1 - (z.1.1 : ℝ)) * (z.2 : ℝ) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with ht | hu
    · exact Or.inl (sub_eq_zero.mp ht).symm
    · exact Or.inr hu
  · rintro (h | h)
    · rw [h, sub_self, zero_mul, add_zero]
    · rw [h, mul_zero, add_zero]

end
end Finsler.NativeRawClockScalarComparison
