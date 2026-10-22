module

public import Finsler.Loop.NativeSuffixTestOrder
public import Finsler.Loop.CochainDegreeTransport

/-! Keep EVERY actual source-degree transport when connecting the
proved suffix interleaved-test comparison to the SAME Stage97 original
triple-test cochain after TWO actual supported Thom caps. This aligns
cochains, not merely numerically equal degrees or abstract classes.
Original sequential time insertion and changing two-cap order remain. -/
@[expose] public section
namespace Finsler.NativeSuffixPostponedAlignment
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem pre_lowering {X Y : TopCat.{0}} {p i j : ℕ} (h : i = j)
    (f : DegreeLoweringHomology.Map (chains X) (chains Y) p)
    (T : singularCochainGroup (ZMod 2) Y j) :
    CochainDegreeTransport.pre X (congrArg (fun t => p + t) h) (f.component j ≫ T) =
      f.component i ≫ CochainDegreeTransport.pre Y h T := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem pre_pullback {X Y : TopCat.{0}} {i j : ℕ} (h : i = j) (f : X ⟶ Y)
    (T : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h T) =
      CochainDegreeTransport.pre X h (cochainPullback f j T) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem pre_cut (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hc : A ∪ B = Set.univ) (p q i j : ℕ) (hi : p + q = i) (hj : p + q = j) (h : i = j)
    (θ : singularCochainGroup (ZMod 2) X p)
    (hs : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
    (T : singularCochainGroup (ZMod 2) (TopCat.of B) q) :
    CochainDegreeTransport.pre X h (SupportedCap.cut X A B hA hB hc p q j hj θ hs ≫ T) =
      SupportedCap.cut X A B hA hB hc p q i hi θ hs ≫ T := by
  cases h
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

abbrev innerDegree := (m + 1) + NativeTripleGHTest.degree m a b k

theorem degree_match : NativeSuffixTestOrder.index m a b k + 1 = innerDegree m a b k := by
  dsimp [NativeSuffixTestOrder.index, NativeSuffixTestOrder.restDegree, innerDegree, NativeTripleGHTest.degree]
  omega

def canonicalInner : singularCochainGroup (ZMod 2) (NativeSuffixTestOrder.space m hm F) (innerDegree m a b k) :=
  (NativeSequentialSupportedStages.suffixOperation m hm F).component (NativeTripleGHTest.degree m a b k) ≫
    cochainPullback (NativeSuffixTestOrder.nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E)

theorem postponed_compare :
    CochainDegreeTransport.pre (NativeSuffixTestOrder.space m hm F) (degree_match m a b k)
      (canonicalInner m hm F a b k E) = NativeSuffixTestOrder.postponed m hm F a b k E := by
  have h := pre_cut (NativeSuffixTestOrder.space m hm F) (NativeSuffixTestOrder.far m hm F) (NativeSuffixTestOrder.near m hm F)
    (NativeSuffixTestOrder.far_open m hm F) (NativeSuffixTestOrder.near_open m hm F) (NativeSuffixTestOrder.cover m hm F)
    (m + 1) (NativeTripleGHTest.degree m a b k) (NativeSuffixTestOrder.index m a b k + 1) (innerDegree m a b k)
    (by have h := degree_match m a b k; dsimp [innerDegree] at h; omega) rfl (degree_match m a b k)
    (NativeSuffixTestOrder.theta m hm F) (NativeSuffixTestOrder.theta_supported m hm F)
    (cochainPullback (NativeSuffixTestOrder.nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E))
  exact h.trans (NativeSuffixTestOrder.postponed_output m hm F a b k E).symm

def canonicalGlobal : singularCochainGroup (ZMod 2) (NativeSequentialSupportedStages.source (m + 1))
    ((m + 1) + innerDegree m a b k) :=
  (NativeSequentialSupportedStages.firstOperation m hm F).component (innerDegree m a b k) ≫ canonicalInner m hm F a b k E

theorem global_postponed_compare :
    CochainDegreeTransport.pre (NativeSequentialSupportedStages.source (m + 1))
      (congrArg (fun t => (m + 1) + t) (degree_match m a b k)) (canonicalGlobal m hm F a b k E) =
        NativeSuffixTestOrder.globalPostponed m hm F a b k E := by
  have h := pre_lowering (degree_match m a b k) (NativeSequentialSupportedStages.firstOperation m hm F)
    (canonicalInner m hm F a b k E)
  exact h.trans (congrArg
    (fun T => (NativeSequentialSupportedStages.firstOperation m hm F).component (NativeSuffixTestOrder.index m a b k + 1) ≫ T)
    (postponed_compare m hm F a b k E))

theorem stage97_compare :
    CochainDegreeTransport.pre (NativeSequentialSupportedStages.source (m + 1))
      (congrArg (fun t => (m + 1) + ((m + 1) + t)) (NativeSequentialGHGlobalComparison.degree_match m hm a b k))
      (canonicalGlobal m hm F a b k E) = NativeSequentialDoubleCapOutputComparison.suffixOriginal m hm F a b k E := by
  let hT := NativeSequentialGHGlobalComparison.degree_match m hm a b k
  have hi := pre_lowering hT (NativeSequentialSupportedStages.suffixOperation m hm F)
    (cochainPullback (NativeSuffixTestOrder.nearTriple m hm F) _ (NativeTripleGHTest.test m hm F a b k E))
  have hp := pre_pullback hT (NativeSuffixTestOrder.nearTriple m hm F) (NativeTripleGHTest.test m hm F a b k E)
  have hi' := hi.trans (congrArg
    (fun T => (NativeSequentialSupportedStages.suffixOperation m hm F).component
      (NativeSequentialGHGlobalComparison.testDegree m a b k + 1) ≫ T) hp.symm)
  have ho := pre_lowering (congrArg (fun t => (m + 1) + t) hT)
    (NativeSequentialSupportedStages.firstOperation m hm F) (canonicalInner m hm F a b k E)
  have he := ho.trans (congrArg
    (fun T => (NativeSequentialSupportedStages.firstOperation m hm F).component
      ((m + 1) + (NativeSequentialGHGlobalComparison.testDegree m a b k + 1)) ≫ T) hi')
  rw [NativeSuffixTestOrder.nearTriple, pullback_comp] at he
  change CochainDegreeTransport.pre (NativeSequentialSupportedStages.source (m + 1))
      (congrArg (fun t => (m + 1) + ((m + 1) + t)) (NativeSequentialGHGlobalComparison.degree_match m hm a b k))
      (canonicalGlobal m hm F a b k E) = NativeSequentialDoubleCapOutputComparison.suffixOriginal m hm F a b k E at he
  exact he

end
end Finsler.NativeSuffixPostponedAlignment
