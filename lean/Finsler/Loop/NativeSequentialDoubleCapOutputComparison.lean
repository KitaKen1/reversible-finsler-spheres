module

public import Finsler.Loop.NativeSequentialSupportedStages
public import Finsler.Loop.NativeSequentialGHGlobalComparison

/-! Pass the PROVED whole-source GH triple-test comparison through
BOTH ACTUAL original normalized supported Thom-cap chain maps.
The output substitution error is an EXPLICIT global cochain boundary,
including every actual small approximation. These use the original
Thom stages with the triple tests AFTER both caps. Equality with the
original INTERLEAVED tested-cap composition, changing cap ORDER and
original sequential time insertion versus the common square remain
unproved. -/
@[expose] public section
namespace Finsler.NativeSequentialDoubleCapOutputComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialSupportedStages
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

theorem lowering_boundary {X Y : TopCat.{0}} {p : ℕ}
    (f : DegreeLoweringHomology.Map (chains X) (chains Y) p) (q : ℕ)
    (B : singularCochainGroup (ZMod 2) Y q) :
    cochainCoboundary (ZMod 2) X (p + q) (f.component q ≫ B) =
      f.component (q + 1) ≫ cochainCoboundary (ZMod 2) Y q B := by
  change (chains X).d (p + (q + 1)) (p + q) ≫ (f.component q ≫ B) = _
  rw [← Category.assoc, ← f.comm q, Category.assoc]
  rfl

private theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (A B : singularCochainGroup (ZMod 2) Y q) :
    cochainPullback f q (A - B) = cochainPullback f q A - cochainPullback f q B :=
  map_sub ((singularCochainComplexZMod2.map f.op).f q).hom A B

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)
abbrev q := NativeSequentialGHGlobalComparison.testDegree m a b k

def prefixPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) ((m + 1) + ((m + 1) + q m a b k)) :=
  (firstOperation m hm F).component ((m + 1) + q m a b k) ≫
    (prefixOperation m hm F).component (q m a b k) ≫
      cochainPullback (prefixFinal m hm F) (q m a b k) (NativeSequentialGHGlobalComparison.prefixPrimitive m hm F a b k E)

def suffixPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) ((m + 1) + ((m + 1) + q m a b k)) :=
  (firstOperation m hm F).component ((m + 1) + q m a b k) ≫
    (suffixOperation m hm F).component (q m a b k) ≫
      cochainPullback (suffixFinal m hm F) (q m a b k) (NativeSequentialGHGlobalComparison.suffixPrimitive m hm F a b k E)

def prefixOriginal : singularCochainGroup (ZMod 2) (source (m + 1)) ((m + 1) + ((m + 1) + (q m a b k + 1))) :=
  (firstOperation m hm F).component ((m + 1) + (q m a b k + 1)) ≫
    (prefixOperation m hm F).component (q m a b k + 1) ≫
      cochainPullback (prefixFinal m hm F) _
        (cochainPullback (NativeSequentialCollarGeometry.prefixOriginal m hm F) _
          (NativeSequentialGHGlobalComparison.input m hm F a b k E))

def suffixOriginal : singularCochainGroup (ZMod 2) (source (m + 1)) ((m + 1) + ((m + 1) + (q m a b k + 1))) :=
  (firstOperation m hm F).component ((m + 1) + (q m a b k + 1)) ≫
    (suffixOperation m hm F).component (q m a b k + 1) ≫
      cochainPullback (suffixFinal m hm F) _
        (cochainPullback (NativeSequentialCollarGeometry.suffixOriginal m hm F) _
          (NativeSequentialGHGlobalComparison.input m hm F a b k E))

def prefixCommon : singularCochainGroup (ZMod 2) (source (m + 1)) ((m + 1) + ((m + 1) + (q m a b k + 1))) :=
  (firstOperation m hm F).component ((m + 1) + (q m a b k + 1)) ≫
    (prefixOperation m hm F).component (q m a b k + 1) ≫
      cochainPullback (prefixFinal m hm F) _
        (cochainPullback (NativeSequentialCollarGeometry.prefixCommon m hm F) _
          (NativeSequentialGHGlobalComparison.input m hm F a b k E))

def suffixCommon : singularCochainGroup (ZMod 2) (source (m + 1)) ((m + 1) + ((m + 1) + (q m a b k + 1))) :=
  (firstOperation m hm F).component ((m + 1) + (q m a b k + 1)) ≫
    (suffixOperation m hm F).component (q m a b k + 1) ≫
      cochainPullback (suffixFinal m hm F) _
        (cochainPullback (NativeSequentialCollarGeometry.suffixCommon m hm F) _
          (NativeSequentialGHGlobalComparison.input m hm F a b k E))

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) _ (prefixPrimitive m hm F a b k E) =
      prefixOriginal m hm F a b k E - prefixCommon m hm F a b k E := by
  unfold prefixPrimitive
  rw [lowering_boundary, lowering_boundary]
  have hp := SmallChainPrimitiveCorrection.pullback_boundary (prefixFinal m hm F) (q m a b k) (q m a b k + 1)
    (NativeSequentialGHGlobalComparison.prefixPrimitive m hm F a b k E)
  change cochainCoboundary (ZMod 2) _ _ (cochainPullback (prefixFinal m hm F) _ _) =
    cochainPullback (prefixFinal m hm F) _
      (cochainCoboundary (ZMod 2) _ _ (NativeSequentialGHGlobalComparison.prefixPrimitive m hm F a b k E)) at hp
  rw [hp, NativeSequentialGHGlobalComparison.prefix_boundary m hm F a b k E hE, pullback_sub]
  simp only [Preadditive.comp_sub, prefixOriginal, prefixCommon]
  rfl

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) _ (suffixPrimitive m hm F a b k E) =
      suffixOriginal m hm F a b k E - suffixCommon m hm F a b k E := by
  unfold suffixPrimitive
  rw [lowering_boundary, lowering_boundary]
  have hp := SmallChainPrimitiveCorrection.pullback_boundary (suffixFinal m hm F) (q m a b k) (q m a b k + 1)
    (NativeSequentialGHGlobalComparison.suffixPrimitive m hm F a b k E)
  change cochainCoboundary (ZMod 2) _ _ (cochainPullback (suffixFinal m hm F) _ _) =
    cochainPullback (suffixFinal m hm F) _
      (cochainCoboundary (ZMod 2) _ _ (NativeSequentialGHGlobalComparison.suffixPrimitive m hm F a b k E)) at hp
  rw [hp, NativeSequentialGHGlobalComparison.suffix_boundary m hm F a b k E hE, pullback_sub]
  simp only [Preadditive.comp_sub, suffixOriginal, suffixCommon]
  rfl

theorem prefix_original_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) _ (prefixOriginal m hm F a b k E) = 0 :=
  DegreeLoweringCochainPullback.closed (firstOperation m hm F) _ _
    (DegreeLoweringCochainPullback.closed (prefixOperation m hm F) _ _
      (pullback_closed _ _ _ (pullback_closed _ _ _ (NativeSequentialGHGlobalComparison.input_closed m hm F a b k E hE))))

theorem suffix_original_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) _ (suffixOriginal m hm F a b k E) = 0 :=
  DegreeLoweringCochainPullback.closed (firstOperation m hm F) _ _
    (DegreeLoweringCochainPullback.closed (suffixOperation m hm F) _ _
      (pullback_closed _ _ _ (pullback_closed _ _ _ (NativeSequentialGHGlobalComparison.input_closed m hm F a b k E hE))))

theorem prefix_common_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) _ (prefixCommon m hm F a b k E) = 0 :=
  DegreeLoweringCochainPullback.closed (firstOperation m hm F) _ _
    (DegreeLoweringCochainPullback.closed (prefixOperation m hm F) _ _
      (pullback_closed _ _ _ (pullback_closed _ _ _ (NativeSequentialGHGlobalComparison.input_closed m hm F a b k E hE))))

theorem suffix_common_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) _ (suffixCommon m hm F a b k E) = 0 :=
  DegreeLoweringCochainPullback.closed (firstOperation m hm F) _ _
    (DegreeLoweringCochainPullback.closed (suffixOperation m hm F) _ _
      (pullback_closed _ _ _ (pullback_closed _ _ _ (NativeSequentialGHGlobalComparison.input_closed m hm F a b k E hE))))

theorem prefix_class_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    CochainClass.classOf (cochainCxZMod2 (source (m + 1))) _ (prefixOriginal m hm F a b k E)
      (prefix_original_closed m hm F a b k E hE) =
    CochainClass.classOf (cochainCxZMod2 (source (m + 1))) _ (prefixCommon m hm F a b k E)
      (prefix_common_closed m hm F a b k E hE) := by
  apply RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 (source (m + 1)))
    ((m + 1) + ((m + 1) + q m a b k)) _ (prefixPrimitive m hm F a b k E)
  change prefixOriginal m hm F a b k E - prefixCommon m hm F a b k E =
    cochainCoboundary (ZMod 2) _ _ (prefixPrimitive m hm F a b k E)
  exact (prefix_boundary m hm F a b k E hE).symm

theorem suffix_class_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    CochainClass.classOf (cochainCxZMod2 (source (m + 1))) _ (suffixOriginal m hm F a b k E)
      (suffix_original_closed m hm F a b k E hE) =
    CochainClass.classOf (cochainCxZMod2 (source (m + 1))) _ (suffixCommon m hm F a b k E)
      (suffix_common_closed m hm F a b k E hE) := by
  apply RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 (source (m + 1)))
    ((m + 1) + ((m + 1) + q m a b k)) _ (suffixPrimitive m hm F a b k E)
  change suffixOriginal m hm F a b k E - suffixCommon m hm F a b k E =
    cochainCoboundary (ZMod 2) _ _ (suffixPrimitive m hm F a b k E)
  exact (suffix_boundary m hm F a b k E hE).symm

end
end Finsler.NativeSequentialDoubleCapOutputComparison
