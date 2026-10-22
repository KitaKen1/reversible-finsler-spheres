module

public import Finsler.Loop.NativeSequentialGlobalComparison
public import Finsler.Loop.CochainDegreeTransport

/-! Discharge EVERY test/support input of the whole-source seam gluing
with the SAME actual genuine GH-power cocycles. Both ORIGINAL complete
raw-half sequential triple tests differ from the SAME common tests by
explicit GLOBAL primitives, literally zero on the actual open collars.
All original degrees are transported, with the actual class preserved.
This is still before the original two-stage Thom/cap and time comparison. -/
@[expose] public section
namespace Finsler.NativeSequentialGHGlobalComparison
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialCollarGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

abbrev testDegree := NativeTripleGHTest.degree m a b k - 1

include hm in
theorem degree_match : testDegree m a b k + 1 = NativeTripleGHTest.degree m a b k := by
  have h := NativeGHPowers.degree_ge m a
  dsimp [testDegree, NativeTripleGHTest.degree]
  omega

def input : singularCochainGroup (ZMod 2) (NativeSequentialTripleComparison.triple (m + 1))
    (testDegree m a b k + 1) :=
  CochainDegreeTransport.pre _ (degree_match m hm a b k) (NativeTripleGHTest.test m hm F a b k E)

theorem input_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ _ (input m hm F a b k E) = 0 :=
  CochainDegreeTransport.closed _ _ _ (NativeTripleGHTest.test_closed m hm F a b k E hE)

theorem pullback_pre_zero {X Y : TopCat.{0}} {i j : ℕ} (h : i = j) (f : X ⟶ Y)
    (T : singularCochainGroup (ZMod 2) Y j) (hT : cochainPullback f j T = 0) :
    cochainPullback f i (CochainDegreeTransport.pre Y h T) = 0 := by
  subst j
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using hT

theorem input_short_zero :
    cochainPullback (SupportedCap.subspaceMap (NativeSequentialTripleComparison.triple (m + 1))
      (NativeTripleGHTest.short F (scale m hm F))) _ (input m hm F a b k E) = 0 :=
  pullback_pre_zero _ _ _ (NativeTripleGHTest.test_short_zero m hm F a b k E)

theorem input_class (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cocycleClass _ (testDegree m a b k + 1) (input m hm F a b k E) (input_closed m hm F a b k E hE) =
      CupUnit.absoluteCast _ (degree_match m hm a b k).symm
        (cocycleClass _ (NativeTripleGHTest.degree m a b k) (NativeTripleGHTest.test m hm F a b k E)
          (NativeTripleGHTest.test_closed m hm F a b k E hE)) :=
  CochainDegreeTransport.class_cast _ _ _ (NativeTripleGHTest.test_closed m hm F a b k E hE)

def prefixPrimitive : singularCochainGroup (ZMod 2) (prefixSource m hm F) (testDegree m a b k) :=
  NativeSequentialGlobalComparison.prefixPrimitive m hm F (testDegree m a b k) (input m hm F a b k E)

def suffixPrimitive : singularCochainGroup (ZMod 2) (suffixSource m hm F) (testDegree m a b k) :=
  NativeSequentialGlobalComparison.suffixPrimitive m hm F (testDegree m a b k) (input m hm F a b k E)

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (prefixSource m hm F) _ (prefixPrimitive m hm F a b k E) =
      cochainPullback (prefixOriginal m hm F) _ (input m hm F a b k E) -
        cochainPullback (prefixCommon m hm F) _ (input m hm F a b k E) :=
  NativeSequentialGlobalComparison.prefix_boundary m hm F _ _ (input_closed m hm F a b k E hE)
    (input_short_zero m hm F a b k E)

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (suffixSource m hm F) _ (suffixPrimitive m hm F a b k E) =
      cochainPullback (suffixOriginal m hm F) _ (input m hm F a b k E) -
        cochainPullback (suffixCommon m hm F) _ (input m hm F a b k E) :=
  NativeSequentialGlobalComparison.suffix_boundary m hm F _ _ (input_closed m hm F a b k E hE)
    (input_short_zero m hm F a b k E)

theorem prefix_collar_zero :
    cochainPullback (SupportedCap.subspaceMap (prefixSource m hm F) (prefixCollar m hm F)) _
      (prefixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialGlobalComparison.prefix_primitive_collar_zero m hm F _ _ (input_short_zero m hm F a b k E)

theorem suffix_collar_zero :
    cochainPullback (SupportedCap.subspaceMap (suffixSource m hm F) (suffixCollar m hm F)) _
      (suffixPrimitive m hm F a b k E) = 0 :=
  NativeSequentialGlobalComparison.suffix_primitive_collar_zero m hm F _ _ (input_short_zero m hm F a b k E)

theorem prefix_class_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    CochainClass.classOf (cochainCxZMod2 (prefixSource m hm F)) _
      (cochainPullback (prefixOriginal m hm F) _ (input m hm F a b k E))
      (pullback_closed _ _ _ (input_closed m hm F a b k E hE)) =
    CochainClass.classOf (cochainCxZMod2 (prefixSource m hm F)) _
      (cochainPullback (prefixCommon m hm F) _ (input m hm F a b k E))
      (pullback_closed _ _ _ (input_closed m hm F a b k E hE)) :=
  NativeSequentialGlobalComparison.prefix_class_eq m hm F _ _ (input_closed m hm F a b k E hE)
    (input_short_zero m hm F a b k E)

theorem suffix_class_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    CochainClass.classOf (cochainCxZMod2 (suffixSource m hm F)) _
      (cochainPullback (suffixOriginal m hm F) _ (input m hm F a b k E))
      (pullback_closed _ _ _ (input_closed m hm F a b k E hE)) =
    CochainClass.classOf (cochainCxZMod2 (suffixSource m hm F)) _
      (cochainPullback (suffixCommon m hm F) _ (input m hm F a b k E))
      (pullback_closed _ _ _ (input_closed m hm F a b k E hE)) :=
  NativeSequentialGlobalComparison.suffix_class_eq m hm F _ _ (input_closed m hm F a b k E hE)
    (input_short_zero m hm F a b k E)

end
end Finsler.NativeSequentialGHGlobalComparison
