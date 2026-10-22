module

public import Finsler.Loop.NativeSequentialCollarGeometry
public import Finsler.Loop.NativeTripleGHTest
public import Finsler.Loop.PatchCochainPrimitive

/-! The ORIGINAL sequential-to-common prism primitives vanish on the
ACTUAL interior/collar overlaps. Both full-source test differences are
closed, vanish literally on their open collars, and restrict to the
EXPLICIT original prism boundaries on the actual positive-split patches.
These are the concrete inputs to whole-parent subdivision gluing. -/
@[expose] public section
namespace Finsler.NativeSequentialCollarPrimitive
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.NativeSequentialCollarGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ)
    (A B : singularCochainGroup (ZMod 2) Y q) :
    cochainPullback f q (A - B) = cochainPullback f q A - cochainPullback f q B :=
  map_sub ((singularCochainComplexZMod2.map f.op).f q).hom A B

theorem pullback_range_zero {X Y : TopCat.{0}} (f : X ⟶ Y) (K : Set Y) (q : ℕ)
    (T : singularCochainGroup (ZMod 2) Y q)
    (hT : cochainPullback (SupportedCap.subspaceMap Y K) q T = 0) (hf : ∀ x, f x ∈ K) :
    cochainPullback f q T = 0 := by
  let g : X ⟶ TopCat.of K := TopCat.ofHom ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk _⟩
  have he : f = g ≫ SupportedCap.subspaceMap Y K := rfl
  rw [he, pullback_comp, hT]
  change (push g).f q ≫ 0 = 0
  exact comp_zero

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (q : ℕ)
  (T : singularCochainGroup (ZMod 2) (NativeSequentialTripleComparison.triple (m + 1)) (q + 1))

def prefixDifference : singularCochainGroup (ZMod 2) (prefixSource m hm F) (q + 1) :=
  cochainPullback (prefixOriginal m hm F) (q + 1) T - cochainPullback (prefixCommon m hm F) (q + 1) T

def suffixDifference : singularCochainGroup (ZMod 2) (suffixSource m hm F) (q + 1) :=
  cochainPullback (suffixOriginal m hm F) (q + 1) T - cochainPullback (suffixCommon m hm F) (q + 1) T

theorem prefix_closed (hT : cochainCoboundary (ZMod 2) _ (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) (prefixSource m hm F) (q + 1) (prefixDifference m hm F q T) = 0 := by
  change ((cochainCxZMod2 (prefixSource m hm F)).d (q + 1) (q + 2)).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((pullback_closed _ _ T hT).trans (pullback_closed _ _ T hT).symm)

theorem suffix_closed (hT : cochainCoboundary (ZMod 2) _ (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) (suffixSource m hm F) (q + 1) (suffixDifference m hm F q T) = 0 := by
  change ((cochainCxZMod2 (suffixSource m hm F)).d (q + 1) (q + 2)).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((pullback_closed _ _ T hT).trans (pullback_closed _ _ T hT).symm)

def prefixLocal : singularCochainGroup (ZMod 2) (TopCat.of (prefixInterior m hm F)) q :=
  NativeSequentialTriplePrism.prefixPrimitive (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) q T

def suffixLocal : singularCochainGroup (ZMod 2) (TopCat.of (suffixInterior m hm F)) q :=
  NativeSequentialTriplePrism.suffixPrimitive (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F) q T

theorem prefix_local_boundary (hT : cochainCoboundary (ZMod 2) _ (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (prefixInterior m hm F)) q (prefixLocal m hm F q T) =
      cochainPullback (SupportedCap.subspaceMap (prefixSource m hm F) (prefixInterior m hm F))
        (q + 1) (prefixDifference m hm F q T) := by
  rw [prefixDifference, pullback_sub, ← pullback_comp, ← pullback_comp]
  exact NativeSequentialTriplePrism.prefix_boundary _ q T hT

theorem suffix_local_boundary (hT : cochainCoboundary (ZMod 2) _ (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (suffixInterior m hm F)) q (suffixLocal m hm F q T) =
      cochainPullback (SupportedCap.subspaceMap (suffixSource m hm F) (suffixInterior m hm F))
        (q + 1) (suffixDifference m hm F q T) := by
  rw [suffixDifference, pullback_sub, ← pullback_comp, ← pullback_comp]
  exact NativeSequentialTriplePrism.suffix_boundary _ q T hT

variable (hshort : cochainPullback (SupportedCap.subspaceMap (NativeSequentialTripleComparison.triple (m + 1))
  (NativeTripleGHTest.short F (scale m hm F))) (q + 1) T = 0)

include hshort in
theorem prefix_collar_zero :
    cochainPullback (SupportedCap.subspaceMap (prefixSource m hm F) (prefixCollar m hm F))
      (q + 1) (prefixDifference m hm F q T) = 0 := by
  let j := SupportedCap.subspaceMap (prefixSource m hm F) (prefixCollar m hm F)
  have h₀ := pullback_range_zero (j ≫ prefixOriginal m hm F) _ (q + 1) T hshort
    (fun z : prefixCollar m hm F => z.property.1)
  have h₁ := pullback_range_zero (j ≫ prefixCommon m hm F) _ (q + 1) T hshort
    (fun z : prefixCollar m hm F => z.property.2)
  rw [prefixDifference, pullback_sub, ← pullback_comp, ← pullback_comp, h₀, h₁, sub_self]

include hshort in
theorem suffix_collar_zero :
    cochainPullback (SupportedCap.subspaceMap (suffixSource m hm F) (suffixCollar m hm F))
      (q + 1) (suffixDifference m hm F q T) = 0 := by
  let j := SupportedCap.subspaceMap (suffixSource m hm F) (suffixCollar m hm F)
  have h₀ := pullback_range_zero (j ≫ suffixOriginal m hm F) _ (q + 1) T hshort
    (fun z : suffixCollar m hm F => z.property.1)
  have h₁ := pullback_range_zero (j ≫ suffixCommon m hm F) _ (q + 1) T hshort
    (fun z : suffixCollar m hm F => z.property.2)
  rw [suffixDifference, pullback_sub, ← pullback_comp, ← pullback_comp, h₀, h₁, sub_self]

include hshort in
theorem prefix_overlap_zero :
    cochainPullback (PatchCochainPrimitive.overlapMap (prefixSource m hm F)
      (prefixInterior m hm F) (prefixCollar m hm F)) q (prefixLocal m hm F q T) = 0 := by
  let e := PatchCochainPrimitive.overlapMap (prefixSource m hm F) (prefixInterior m hm F) (prefixCollar m hm F)
  let H := NativeSequentialTripleComparison.prefixHomotopy (n := m + 1) (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)
  have hz := NativeTripleGHTest.prism_zero (H.comp (TopCat.Homotopy.refl e))
    (NativeTripleGHTest.short F (scale m hm F)) q T
    (fun z => prefix_homotopy_short m hm F z.1 (e z.2) z.2.val.property) hshort
  change (push e).f q ≫ ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ T) = 0
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  exact hz

include hshort in
theorem suffix_overlap_zero :
    cochainPullback (PatchCochainPrimitive.overlapMap (suffixSource m hm F)
      (suffixInterior m hm F) (suffixCollar m hm F)) q (suffixLocal m hm F q T) = 0 := by
  let e := PatchCochainPrimitive.overlapMap (suffixSource m hm F) (suffixInterior m hm F) (suffixCollar m hm F)
  let H := NativeSequentialTripleComparison.suffixHomotopy (n := m + 1) (NativeOrderedDoubleCutDiagonal.radius_le_one m hm F)
  have hz := NativeTripleGHTest.prism_zero (H.comp (TopCat.Homotopy.refl e))
    (NativeTripleGHTest.short F (scale m hm F)) q T
    (fun z => suffix_homotopy_short m hm F z.1 (e z.2) z.2.val.property) hshort
  change (push e).f q ≫ ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ T) = 0
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  exact hz

end
end Finsler.NativeSequentialCollarPrimitive
