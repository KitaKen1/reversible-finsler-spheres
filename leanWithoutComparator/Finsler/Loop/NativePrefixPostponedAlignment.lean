module

public import Finsler.Loop.NativePrefixTestOrder
public import Finsler.Loop.NativeSuffixPostponedAlignment
public import Finsler.Loop.CochainDegreeTransport

/-! Reassociate the SAME three near-output factors and transport
both cap source and output degrees. The postponed prefix cochain is
the SAME Stage97 original, with no representative replacement. -/
@[expose] public section
namespace Finsler.NativePrefixPostponedAlignment
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Finsler.NativeSuffixPostponedAlignment

theorem pre_cup (X : TopCat.{0}) (p q i j : ℕ) (hi : p + q = i) (hj : p + q = j) (h : i = j)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q) :
    CochainDegreeTransport.pre X h (CupOne.cup X p q j hj α β) = CupOne.cup X p q i hi α β := by
  cases h
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem pre_cut_output (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q r i j : ℕ) (hi : p + q = i) (hj : p + r = j)
    (hq : q = r) (h : i = j) (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (T : singularCochainGroup (ZMod 2) (TopCat.of B) r) :
    CochainDegreeTransport.pre X h (SupportedCap.cut X A B hA hB hc p r j hj θ hs ≫ T) =
      SupportedCap.cut X A B hA hB hc p q i hi θ hs ≫ CochainDegreeTransport.pre (TopCat.of B) hq T := by
  cases hq
  cases h
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

abbrev innerDegree := (m + 1) + NativeTripleGHTest.degree m a b k

theorem degree_match : NativePrefixTestOrder.index m a b k + 1 = innerDegree m a b k := by
  dsimp [NativePrefixTestOrder.index, NativePrefixTestOrder.pairDegree, innerDegree, NativeTripleGHTest.degree]
  omega

def canonicalInner : singularCochainGroup (ZMod 2) (NativePrefixTestOrder.space m hm F) (innerDegree m a b k) :=
  (NativeSequentialSupportedStages.prefixOperation m hm F).component (NativeTripleGHTest.degree m a b k) ≫
    cochainPullback (NativePrefixTestOrder.nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E)

theorem postponed_compare :
    CochainDegreeTransport.pre (NativePrefixTestOrder.space m hm F) (degree_match m a b k)
      (canonicalInner m hm F a b k E) = NativePrefixTestOrder.postponed m hm F a b k E := by
  have hq : NativePrefixTestOrder.pairDegree m a b + k = NativeTripleGHTest.degree m a b k := by
    dsimp [NativePrefixTestOrder.pairDegree, NativeTripleGHTest.degree]; omega
  have h := pre_cut_output (NativePrefixTestOrder.space m hm F) (NativePrefixTestOrder.far m hm F) (NativePrefixTestOrder.near m hm F)
    (NativePrefixTestOrder.far_open m hm F) (NativePrefixTestOrder.near_open m hm F) (NativePrefixTestOrder.cover m hm F)
    (m + 1) (NativePrefixTestOrder.pairDegree m a b + k) (NativeTripleGHTest.degree m a b k)
    (NativePrefixTestOrder.index m a b k + 1) (innerDegree m a b k)
    (by dsimp [NativePrefixTestOrder.index]; omega) rfl hq (degree_match m a b k)
    (NativePrefixTestOrder.theta m hm F) (NativePrefixTestOrder.theta_supported m hm F)
    (cochainPullback (NativePrefixTestOrder.nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E))
  rw [← NativePrefixTestOrder.near_output m hm F a b k E, pre_cup] at h
  rw [NativePrefixTestOrder.near_output m hm F a b k E] at h
  exact h

def canonicalGlobal : singularCochainGroup (ZMod 2) (NativeSequentialSupportedStages.source (m + 1))
    ((m + 1) + innerDegree m a b k) :=
  (NativeSequentialSupportedStages.firstOperation m hm F).component (innerDegree m a b k) ≫ canonicalInner m hm F a b k E

theorem global_postponed_compare :
    CochainDegreeTransport.pre (NativeSequentialSupportedStages.source (m + 1))
      (congrArg (fun t => (m + 1) + t) (degree_match m a b k)) (canonicalGlobal m hm F a b k E) =
        NativePrefixTestOrder.globalPostponed m hm F a b k E := by
  have h := pre_lowering (degree_match m a b k) (NativeSequentialSupportedStages.firstOperation m hm F)
    (canonicalInner m hm F a b k E)
  exact h.trans (congrArg
    (fun T => (NativeSequentialSupportedStages.firstOperation m hm F).component (NativePrefixTestOrder.index m a b k + 1) ≫ T)
    (postponed_compare m hm F a b k E))

theorem stage97_compare :
    CochainDegreeTransport.pre (NativeSequentialSupportedStages.source (m + 1))
      (congrArg (fun t => (m + 1) + ((m + 1) + t)) (NativeSequentialGHGlobalComparison.degree_match m hm a b k))
      (canonicalGlobal m hm F a b k E) = NativeSequentialDoubleCapOutputComparison.prefixOriginal m hm F a b k E := by
  let hT := NativeSequentialGHGlobalComparison.degree_match m hm a b k
  have hi := pre_lowering hT (NativeSequentialSupportedStages.prefixOperation m hm F)
    (cochainPullback (NativePrefixTestOrder.nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E))
  have hp := pre_pullback hT (NativePrefixTestOrder.nearTriple m hm F) (NativeTripleGHTest.test m hm F a b k E)
  have hi' := hi.trans (congrArg
    (fun T => (NativeSequentialSupportedStages.prefixOperation m hm F).component
      (NativeSequentialGHGlobalComparison.testDegree m a b k + 1) ≫ T) hp.symm)
  have ho := pre_lowering (congrArg (fun t => (m + 1) + t) hT)
    (NativeSequentialSupportedStages.firstOperation m hm F) (canonicalInner m hm F a b k E)
  have he := ho.trans (congrArg
    (fun T => (NativeSequentialSupportedStages.firstOperation m hm F).component
      ((m + 1) + (NativeSequentialGHGlobalComparison.testDegree m a b k + 1)) ≫ T) hi')
  rw [NativePrefixTestOrder.nearTriple, pullback_comp] at he
  change CochainDegreeTransport.pre (NativeSequentialSupportedStages.source (m + 1))
      (congrArg (fun t => (m + 1) + ((m + 1) + t)) (NativeSequentialGHGlobalComparison.degree_match m hm a b k))
      (canonicalGlobal m hm F a b k E) = NativeSequentialDoubleCapOutputComparison.prefixOriginal m hm F a b k E at he
  exact he

end
end Finsler.NativePrefixPostponedAlignment
