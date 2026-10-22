module

public import Finsler.Loop.NativeRawDoubleCapCommon

/-! Combine the original triple-output correction with the actual
raw double-cap subdivision correction. This gives a scalar reduction
of BOTH original postponed two-stage operations to their common cup
caps, on every genuine source cycle. Full relative support for the
triple-output correction and original time/test insertion remain. -/
@[expose] public section
namespace Finsler.NativeRawOriginalScalarReduction
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeSequentialSupportedStages
open Finsler.NativeRawClockSupportedAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem pre_boundary (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (T : singularCochainGroup (ZMod 2) X j) :
    cochainCoboundary (ZMod 2) X i (CochainDegreeTransport.pre X h T) =
    CochainDegreeTransport.pre X (congrArg (fun n => n + 1) h) (cochainCoboundary (ZMod 2) X j T) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem pre_sub (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (A B : singularCochainGroup (ZMod 2) X j) :
    CochainDegreeTransport.pre X h (A - B) =
    CochainDegreeTransport.pre X h A - CochainDegreeTransport.pre X h B := by
  unfold CochainDegreeTransport.pre
  exact Preadditive.comp_sub _ _ _

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

include hm in
theorem primitive_degree : index m a b k =
    (m + 1) + ((m + 1) + NativeSequentialGHGlobalComparison.testDegree m a b k) := by
  have h := NativeSequentialGHGlobalComparison.degree_match m hm a b k
  dsimp [index, testDegree]
  omega

def prefixOriginal := CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
  (NativeSequentialDoubleCapOutputComparison.prefixOriginal m hm F a b k E)

def prefixPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  CochainDegreeTransport.pre (source (m + 1)) (primitive_degree m hm a b k)
    (NativeSequentialDoubleCapOutputComparison.prefixPrimitive m hm F a b k E) +
    NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixPrimitive m hm F a b k E) =
    prefixOriginal m hm F a b k E - NativeRawDoubleCapCommon.prefixCoupled m hm F a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom (_ + _) = _
  rw [map_add]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (CochainDegreeTransport.pre _ (primitive_degree m hm a b k)
        (NativeSequentialDoubleCapOutputComparison.prefixPrimitive m hm F a b k E)) +
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E) = _
  rw [pre_boundary, NativeSequentialDoubleCapOutputComparison.prefix_boundary m hm F a b k E hE,
    pre_sub, NativeRawDoubleCapCommon.prefix_stage97_boundary m hm F a b k E hE]
  change (prefixOriginal m hm F a b k E - _) + (_ - _) = _
  abel

theorem prefix_original_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k + 1) (prefixOriginal m hm F a b k E) = 0 :=
  CochainDegreeTransport.closed _ _ _ (NativeSequentialDoubleCapOutputComparison.prefix_original_closed m hm F a b k E hE)

theorem prefix_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) = 0) :
    c ≫ prefixOriginal m hm F a b k E = c ≫ NativeRawDoubleCapCommon.prefixCoupled m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (prefix_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    prefixPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, zero_comp, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

def suffixOriginal := CochainDegreeTransport.pre (source (m + 1)) (stage97_degree m hm a b k)
  (NativeSequentialDoubleCapOutputComparison.suffixOriginal m hm F a b k E)

def suffixPrimitive : singularCochainGroup (ZMod 2) (source (m + 1)) (index m a b k) :=
  CochainDegreeTransport.pre (source (m + 1)) (primitive_degree m hm a b k)
    (NativeSequentialDoubleCapOutputComparison.suffixPrimitive m hm F a b k E) +
    NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixPrimitive m hm F a b k E) =
    suffixOriginal m hm F a b k E - NativeRawDoubleCapCommon.suffixCoupled m hm F a b k E := by
  change ((cochainCxZMod2 (source (m + 1))).d (index m a b k) (index m a b k + 1)).hom (_ + _) = _
  rw [map_add]
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (CochainDegreeTransport.pre _ (primitive_degree m hm a b k)
        (NativeSequentialDoubleCapOutputComparison.suffixPrimitive m hm F a b k E)) +
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k)
      (NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E) = _
  rw [pre_boundary, NativeSequentialDoubleCapOutputComparison.suffix_boundary m hm F a b k E hE,
    pre_sub, NativeRawDoubleCapCommon.suffix_stage97_boundary m hm F a b k E hE]
  change (suffixOriginal m hm F a b k E - _) + (_ - _) = _
  abel

theorem suffix_original_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k + 1) (suffixOriginal m hm F a b k E) = 0 :=
  CochainDegreeTransport.closed _ _ _ (NativeSequentialDoubleCapOutputComparison.suffix_original_closed m hm F a b k E hE)

theorem suffix_cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (source (m + 1))).X (index m a b k + 1))
    (hc : c ≫ (chains (source (m + 1))).d (index m a b k + 1) (index m a b k) = 0) :
    c ≫ suffixOriginal m hm F a b k E = c ≫ NativeRawDoubleCapCommon.suffixCoupled m hm F a b k E := by
  have hb := congrArg (fun T => c ≫ T) (suffix_boundary m hm F a b k E hE)
  change c ≫ ((chains (source (m + 1))).d (index m a b k + 1) (index m a b k) ≫
    suffixPrimitive m hm F a b k E) = _ at hb
  rw [← Category.assoc, hc, zero_comp, Preadditive.comp_sub] at hb
  exact sub_eq_zero.mp hb.symm

end
end Finsler.NativeRawOriginalScalarReduction
