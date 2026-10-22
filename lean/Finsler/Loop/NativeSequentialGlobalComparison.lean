module

public import Finsler.Loop.NativeSequentialCollarPrimitive

/-! Whole-source comparison across BOTH previously excluded seams.
The EXPLICIT original interior prism is zero-extended, then corrected
by the ACTUAL subdivision prism of the genuine two-open-set cover.
Its exact boundary is the original/common full triple-test difference,
and the primitive vanishes literally on the entire actual open collar.
Original two-stage Thom/cap and sequential-time alignment remain separate. -/
@[expose] public section
namespace Finsler.NativeSequentialGlobalComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialCollarGeometry Finsler.NativeSequentialCollarPrimitive
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (q : ℕ)
  (T : singularCochainGroup (ZMod 2) (NativeSequentialTripleComparison.triple (m + 1)) (q + 1))

def prefixPrimitive : singularCochainGroup (ZMod 2) (prefixSource m hm F) q :=
  PatchCochainPrimitive.primitive (prefixSource m hm F) (prefixInterior m hm F) (prefixCollar m hm F) q
    (prefixDifference m hm F q T) (prefixLocal m hm F q T)

def suffixPrimitive : singularCochainGroup (ZMod 2) (suffixSource m hm F) q :=
  PatchCochainPrimitive.primitive (suffixSource m hm F) (suffixInterior m hm F) (suffixCollar m hm F) q
    (suffixDifference m hm F q T) (suffixLocal m hm F q T)

variable (hT : cochainCoboundary (ZMod 2) _ (q + 1) T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (NativeSequentialTripleComparison.triple (m + 1))
    (NativeTripleGHTest.short F (scale m hm F))) (q + 1) T = 0)

include hT hshort in
theorem prefix_boundary : cochainCoboundary (ZMod 2) (prefixSource m hm F) q (prefixPrimitive m hm F q T) =
    prefixDifference m hm F q T :=
  PatchCochainPrimitive.primitive_boundary (prefixSource m hm F) (prefixInterior m hm F) (prefixCollar m hm F) q _ _
    (prefix_interior_open m hm F) (prefix_collar_open m hm F) (prefix_cover m hm F)
    (prefix_closed m hm F q T hT) (prefix_local_boundary m hm F q T hT)
    (prefix_collar_zero m hm F q T hshort) (prefix_overlap_zero m hm F q T hshort)

include hT hshort in
theorem suffix_boundary : cochainCoboundary (ZMod 2) (suffixSource m hm F) q (suffixPrimitive m hm F q T) =
    suffixDifference m hm F q T :=
  PatchCochainPrimitive.primitive_boundary (suffixSource m hm F) (suffixInterior m hm F) (suffixCollar m hm F) q _ _
    (suffix_interior_open m hm F) (suffix_collar_open m hm F) (suffix_cover m hm F)
    (suffix_closed m hm F q T hT) (suffix_local_boundary m hm F q T hT)
    (suffix_collar_zero m hm F q T hshort) (suffix_overlap_zero m hm F q T hshort)

include hshort in
theorem prefix_primitive_collar_zero :
    cochainPullback (SupportedCap.subspaceMap (prefixSource m hm F) (prefixCollar m hm F)) q
      (prefixPrimitive m hm F q T) = 0 :=
  PatchCochainPrimitive.primitive_carrier_zero (prefixSource m hm F) (prefixInterior m hm F) (prefixCollar m hm F)
    q _ _ (prefixCollar m hm F) (prefix_collar_zero m hm F q T hshort) (prefix_overlap_zero m hm F q T hshort)

include hshort in
theorem suffix_primitive_collar_zero :
    cochainPullback (SupportedCap.subspaceMap (suffixSource m hm F) (suffixCollar m hm F)) q
      (suffixPrimitive m hm F q T) = 0 :=
  PatchCochainPrimitive.primitive_carrier_zero (suffixSource m hm F) (suffixInterior m hm F) (suffixCollar m hm F)
    q _ _ (suffixCollar m hm F) (suffix_collar_zero m hm F q T hshort) (suffix_overlap_zero m hm F q T hshort)

include hT hshort in
theorem prefix_class_eq :
    CochainClass.classOf (cochainCxZMod2 (prefixSource m hm F)) (q + 1)
      (cochainPullback (prefixOriginal m hm F) (q + 1) T) (pullback_closed _ _ T hT) =
    CochainClass.classOf (cochainCxZMod2 (prefixSource m hm F)) (q + 1)
      (cochainPullback (prefixCommon m hm F) (q + 1) T) (pullback_closed _ _ T hT) :=
by
  apply RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 (prefixSource m hm F))
    q (q + 1) (prefixPrimitive m hm F q T)
  change prefixDifference m hm F q T =
    cochainCoboundary (ZMod 2) (prefixSource m hm F) q (prefixPrimitive m hm F q T)
  exact (prefix_boundary m hm F q T hT hshort).symm

include hT hshort in
theorem suffix_class_eq :
    CochainClass.classOf (cochainCxZMod2 (suffixSource m hm F)) (q + 1)
      (cochainPullback (suffixOriginal m hm F) (q + 1) T) (pullback_closed _ _ T hT) =
    CochainClass.classOf (cochainCxZMod2 (suffixSource m hm F)) (q + 1)
      (cochainPullback (suffixCommon m hm F) (q + 1) T) (pullback_closed _ _ T hT) :=
by
  apply RelativeCupCommutativity.classOf_eq_of_boundary (cochainCxZMod2 (suffixSource m hm F))
    q (q + 1) (suffixPrimitive m hm F q T)
  change suffixDifference m hm F q T =
    cochainCoboundary (ZMod 2) (suffixSource m hm F) q (suffixPrimitive m hm F q T)
  exact (suffix_boundary m hm F q T hT hshort).symm

theorem relative_class_eq_of_ambient_boundary {X : TopCat.{0}} (C : Set X) (q : ℕ)
    (φ ψ : RelativeCupCochain.relative (TopPair.ofSubset C) (q + 1))
    (hφ : RelativeCupCochain.differential (TopPair.ofSubset C) (q + 1) φ = 0)
    (hψ : RelativeCupCochain.differential (TopPair.ofSubset C) (q + 1) ψ = 0)
    (κ : singularCochainGroup (ZMod 2) X q)
    (hκ : cochainPullback (SupportedCap.subspaceMap X C) q κ = 0)
    (hb : cochainCoboundary (ZMod 2) X q κ =
      RelativeCupCochain.toAmbient (TopPair.ofSubset C) (q + 1) φ -
        RelativeCupCochain.toAmbient (TopPair.ofSubset C) (q + 1) ψ) :
    CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset C)) (q + 1) φ hφ =
      CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset C)) (q + 1) ψ hψ := by
  obtain ⟨η, hη⟩ := RelativeCupCochain.exists_lift (TopPair.ofSubset C) q κ hκ
  have he : RelativeCupCochain.differential (TopPair.ofSubset C) q η = φ - ψ := by
    apply RelativeCupCochain.toAmbient_injective (TopPair.ofSubset C) (q + 1)
    rw [RelativeCupCochain.toAmbient_differential, hη, map_sub]
    exact hb
  exact RelativeCupCommutativity.classOf_eq_of_boundary _ q (q + 1) η φ ψ hφ hψ he.symm

include hT hshort in
theorem prefix_relative_class_eq
    (φ ψ : RelativeCupCochain.relative (TopPair.ofSubset (prefixCollar m hm F)) (q + 1))
    (hφ : RelativeCupCochain.differential (TopPair.ofSubset (prefixCollar m hm F)) (q + 1) φ = 0)
    (hψ : RelativeCupCochain.differential (TopPair.ofSubset (prefixCollar m hm F)) (q + 1) ψ = 0)
    (hφa : RelativeCupCochain.toAmbient (TopPair.ofSubset (prefixCollar m hm F)) (q + 1) φ =
      cochainPullback (prefixOriginal m hm F) (q + 1) T)
    (hψa : RelativeCupCochain.toAmbient (TopPair.ofSubset (prefixCollar m hm F)) (q + 1) ψ =
      cochainPullback (prefixCommon m hm F) (q + 1) T) :
    CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset (prefixCollar m hm F))) (q + 1) φ hφ =
      CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset (prefixCollar m hm F))) (q + 1) ψ hψ := by
  apply relative_class_eq_of_ambient_boundary _ q φ ψ hφ hψ (prefixPrimitive m hm F q T)
    (prefix_primitive_collar_zero m hm F q T hshort)
  rw [hφa, hψa]
  exact prefix_boundary m hm F q T hT hshort

include hT hshort in
theorem suffix_relative_class_eq
    (φ ψ : RelativeCupCochain.relative (TopPair.ofSubset (suffixCollar m hm F)) (q + 1))
    (hφ : RelativeCupCochain.differential (TopPair.ofSubset (suffixCollar m hm F)) (q + 1) φ = 0)
    (hψ : RelativeCupCochain.differential (TopPair.ofSubset (suffixCollar m hm F)) (q + 1) ψ = 0)
    (hφa : RelativeCupCochain.toAmbient (TopPair.ofSubset (suffixCollar m hm F)) (q + 1) φ =
      cochainPullback (suffixOriginal m hm F) (q + 1) T)
    (hψa : RelativeCupCochain.toAmbient (TopPair.ofSubset (suffixCollar m hm F)) (q + 1) ψ =
      cochainPullback (suffixCommon m hm F) (q + 1) T) :
    CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset (suffixCollar m hm F))) (q + 1) φ hφ =
      CochainClass.classOf (RelativeCup.cx (TopPair.ofSubset (suffixCollar m hm F))) (q + 1) ψ hψ := by
  apply relative_class_eq_of_ambient_boundary _ q φ ψ hφ hψ (suffixPrimitive m hm F q T)
    (suffix_primitive_collar_zero m hm F q T hshort)
  rw [hφa, hψa]
  exact suffix_boundary m hm F q T hT hshort

end
end Finsler.NativeSequentialGlobalComparison
