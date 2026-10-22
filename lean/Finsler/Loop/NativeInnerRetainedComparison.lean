module

public import Finsler.Loop.NativeInnerCutPullback
public import Finsler.Loop.CupScalarBoundary

/-! Retain the actual outside GH/evaluation factors while replacing BOTH
raw inner caps by the pullback of the ORIGINAL normalized inner cut.
The difference is an explicit scalar coboundary, with exact degrees. -/
@[expose] public section
namespace Finsler.NativeInnerRetainedComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem cup_left_pre (X : TopCat.{0}) {p p' q N : ℕ} (e : p = p') (h : p + q = N)
    (T : singularCochainGroup (ZMod 2) X p') (B : singularCochainGroup (ZMod 2) X q) :
    CupOne.cup X p q N h (CochainDegreeTransport.pre X e T) B =
      CupOne.cup X p' q N (by omega) T B := by
  cases e
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem cup_right_pre (X : TopCat.{0}) {p q q' N : ℕ} (e : q = q') (h : p + q = N)
    (T : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q') :
    CupOne.cup X p q N h T (CochainDegreeTransport.pre X e B) =
      CupOne.cup X p q' N (by omega) T B := by
  cases e
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixPrimitive : singularCochainGroup (ZMod 2) (outerSpace m hm F) (NativePrefixTestOrder.index m a b k) :=
  CupOne.cup (outerSpace m hm F) (m + NativePrefixTestOrder.pairDegree m a b) k
    (NativePrefixTestOrder.index m a b k) rfl (NativeInnerCutPullback.prefixPrimitive m hm F a b)
    (NativePrefixTestOrder.alpha m hm F k E)

def prefixOriginal : singularCochainGroup (ZMod 2) (outerSpace m hm F) (NativePrefixTestOrder.index m a b k + 1) :=
  CupOne.cup (outerSpace m hm F) ((m + 1) + NativePrefixTestOrder.pairDegree m a b) k
    (NativePrefixTestOrder.index m a b k + 1) (by dsimp [NativePrefixTestOrder.index]; omega)
    (NativeInnerCutPullback.prefixOriginal m hm F a b) (NativePrefixTestOrder.alpha m hm F k E)

def suffixPrimitive : singularCochainGroup (ZMod 2) (outerSpace m hm F) (NativeSuffixTestOrder.index m a b k) :=
  CupOne.cup (outerSpace m hm F) (NativeGHPowers.degree m a) (m + NativeSuffixTestOrder.restDegree m b k)
    (NativeSuffixTestOrder.index m a b k) (by dsimp [NativeSuffixTestOrder.index]; omega)
    (NativeSuffixTestOrder.alpha m hm F a) (NativeInnerCutPullback.suffixPrimitive m hm F b k E)

def suffixOriginal : singularCochainGroup (ZMod 2) (outerSpace m hm F) (NativeSuffixTestOrder.index m a b k + 1) :=
  CupOne.cup (outerSpace m hm F) (NativeGHPowers.degree m a) ((m + 1) + NativeSuffixTestOrder.restDegree m b k)
    (NativeSuffixTestOrder.index m a b k + 1) (by dsimp [NativeSuffixTestOrder.index]; omega)
    (NativeSuffixTestOrder.alpha m hm F a) (NativeInnerCutPullback.suffixOriginal m hm F b k E)

theorem prefix_local : CupOne.cup (outerSpace m hm F) ((m + 1) + NativePrefixTestOrder.pairDegree m a b) k
    (NativePrefixTestOrder.index m a b k + 1) (by dsimp [NativePrefixTestOrder.index]; omega)
    (NativeInnerCutPullback.prefixLocal m hm F a b) (NativePrefixTestOrder.alpha m hm F k E) =
      NativePrefixTestOrder.interleaved m hm F a b k E := by
  rw [NativeInnerCutPullback.prefix_local]
  rfl

theorem suffix_local : CupOne.cup (outerSpace m hm F) (NativeGHPowers.degree m a) ((m + 1) + NativeSuffixTestOrder.restDegree m b k)
    (NativeSuffixTestOrder.index m a b k + 1) (by dsimp [NativeSuffixTestOrder.index]; omega)
    (NativeSuffixTestOrder.alpha m hm F a) (NativeInnerCutPullback.suffixLocal m hm F b k E) =
      NativeSuffixTestOrder.interleaved m hm F a b k E := by
  rw [NativeInnerCutPullback.suffix_local]
  exact (SupportedRightTestLocal.dual_at_degree _ _ _ _ _ _ _).symm

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (outerSpace m hm F) (NativePrefixTestOrder.index m a b k)
      (prefixPrimitive m hm F a b k E) = NativePrefixTestOrder.interleaved m hm F a b k E - prefixOriginal m hm F a b k E := by
  unfold prefixPrimitive
  rw [CupScalarBoundary.right_closed _ _ _ _ _ _ _ (NativePrefixTestOrder.alpha_closed m hm F k E hE),
    NativeInnerCutPullback.prefix_boundary, cup_left_pre, CupScalarBoundary.sub_left, prefix_local]
  rfl

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (outerSpace m hm F) (NativeSuffixTestOrder.index m a b k)
      (suffixPrimitive m hm F a b k E) = NativeSuffixTestOrder.interleaved m hm F a b k E - suffixOriginal m hm F a b k E := by
  unfold suffixPrimitive
  rw [CupScalarBoundary.left_closed _ _ _ _ _ _ _ (NativeSuffixTestOrder.alpha_closed m hm F a),
    NativeInnerCutPullback.suffix_boundary m hm F b k E hE, cup_right_pre, CupScalarBoundary.sub_right, suffix_local]
  rfl

end
end Finsler.NativeInnerRetainedComparison
