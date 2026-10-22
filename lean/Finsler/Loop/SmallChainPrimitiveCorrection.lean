module

public import Finsler.Loop.SupportedSmallCochainComparison

/-! Correct an ACTUAL proposed primitive using the original
subdivision prism. If its boundary is right on source-small chains,
the corrected primitive has exactly the desired global boundary.
Every separately specified carrier zero is preserved. No assertion
about zero on an arbitrary union of carriers is used. -/
@[expose] public section
namespace Finsler.SmallChainPrimitiveCorrection
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

private theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a b : singularCochainGroup (ZMod 2) Y n) :
    cochainPullback f n (a - b) = cochainPullback f n a - cochainPullback f n b :=
  map_sub ((singularCochainComplexZMod2.map f.op).f n).hom a b

private theorem pullback_add {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a b : singularCochainGroup (ZMod 2) Y n) :
    cochainPullback f n (a + b) = cochainPullback f n a + cochainPullback f n b :=
  map_add ((singularCochainComplexZMod2.map f.op).f n).hom a b

theorem pullback_boundary {X Y : TopCat.{0}} (f : X ⟶ Y) (i j : ℕ)
    (χ : singularCochainGroup (ZMod 2) Y i) :
    ((cochainCxZMod2 X).d i j).hom (cochainPullback f i χ) =
      cochainPullback f j (((cochainCxZMod2 Y).d i j).hom χ) :=
  ConcreteCategory.congr_hom ((singularCochainComplexZMod2.map f.op).comm i j) χ

variable {X : TopCat.{0}} {ι : Type*} (U : ι → Set X) (n : ℕ)
  (Φ : singularCochainGroup (ZMod 2) X (n + 1)) (χ : singularCochainGroup (ZMod 2) X n)

def difference : singularCochainGroup (ZMod 2) X (n + 1) := Φ - cochainCoboundary (ZMod 2) X n χ

theorem difference_closed (hΦ : cochainCoboundary (ZMod 2) X (n + 1) Φ = 0) :
    cochainCoboundary (ZMod 2) X (n + 1) (difference n Φ χ) = 0 := by
  change ((cochainCxZMod2 X).d (n + 1) (n + 2)).hom (Φ - cochainCoboundary (ZMod 2) X n χ) = 0
  rw [map_sub]
  change cochainCoboundary (ZMod 2) X (n + 1) Φ -
    cochainCoboundary (ZMod 2) X (n + 1) (cochainCoboundary (ZMod 2) X n χ) = 0
  have hb : cochainCoboundary (ZMod 2) X (n + 1) (cochainCoboundary (ZMod 2) X n χ) = 0 :=
    CochainClass.closed_boundary (cochainCxZMod2 X) n (n + 1) χ
  rw [hΦ, hb, sub_self]

theorem difference_small_zero
    (hsmall : (SmallChainCarrier.inclusion X U).f (n + 1) ≫ Φ =
      (SmallChainCarrier.inclusion X U).f (n + 1) ≫ cochainCoboundary (ZMod 2) X n χ) :
    (SmallChainCarrier.inclusion X U).f (n + 1) ≫ difference n Φ χ = 0 := by
  rw [difference, Preadditive.comp_sub, hsmall, sub_self]

def correction : singularCochainGroup (ZMod 2) X n :=
  SupportedSmallCochainComparison.primitive U n (difference n Φ χ)

theorem correction_boundary (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ)
    (hΦ : cochainCoboundary (ZMod 2) X (n + 1) Φ = 0)
    (hsmall : (SmallChainCarrier.inclusion X U).f (n + 1) ≫ Φ =
      (SmallChainCarrier.inclusion X U).f (n + 1) ≫ cochainCoboundary (ZMod 2) X n χ) :
    cochainCoboundary (ZMod 2) X n (correction U n Φ χ) = difference n Φ χ :=
  SupportedSmallCochainComparison.primitive_boundary U hU hc n (difference n Φ χ)
    (difference_closed n Φ χ hΦ) (difference_small_zero U n Φ χ hsmall)

def primitive : singularCochainGroup (ZMod 2) X n := χ + correction U n Φ χ

theorem primitive_boundary (hU : ∀ i, IsOpen (U i)) (hc : ⋃ i, U i = Set.univ)
    (hΦ : cochainCoboundary (ZMod 2) X (n + 1) Φ = 0)
    (hsmall : (SmallChainCarrier.inclusion X U).f (n + 1) ≫ Φ =
      (SmallChainCarrier.inclusion X U).f (n + 1) ≫ cochainCoboundary (ZMod 2) X n χ) :
    cochainCoboundary (ZMod 2) X n (primitive U n Φ χ) = Φ := by
  change ((cochainCxZMod2 X).d n (n + 1)).hom (χ + correction U n Φ χ) = Φ
  rw [map_add]
  change cochainCoboundary (ZMod 2) X n χ + cochainCoboundary (ZMod 2) X n (correction U n Φ χ) = Φ
  rw [correction_boundary U n Φ χ hU hc hΦ hsmall, difference]
  abel

theorem difference_support_zero (C : Set X)
    (hΦ : cochainPullback (SupportedCap.subspaceMap X C) (n + 1) Φ = 0)
    (hχ : cochainPullback (SupportedCap.subspaceMap X C) n χ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) (n + 1) (difference n Φ χ) = 0 := by
  have he := pullback_boundary (SupportedCap.subspaceMap X C) n (n + 1) χ
  rw [hχ, map_zero] at he
  change 0 = cochainPullback (SupportedCap.subspaceMap X C) (n + 1)
    (cochainCoboundary (ZMod 2) X n χ) at he
  rw [difference, pullback_sub, hΦ, ← he, sub_self]

theorem primitive_support_zero (C : Set X)
    (hΦ : cochainPullback (SupportedCap.subspaceMap X C) (n + 1) Φ = 0)
    (hχ : cochainPullback (SupportedCap.subspaceMap X C) n χ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) n (primitive U n Φ χ) = 0 := by
  have hg := SupportedSmallCochainComparison.primitive_support_zero U C n (difference n Φ χ)
    (difference_support_zero n Φ χ C hΦ hχ)
  rw [primitive, pullback_add, hχ]
  exact (zero_add _).trans hg

end
end Finsler.SmallChainPrimitiveCorrection
