module

public import Finsler.Loop.NativeGlobalTimeSquare
public import Finsler.Loop.RelativePrismCochainBoundary
public import Finsler.Loop.CochainCarrierPullbackZero

/-! Evaluate a genuine coboundary on the ORIGINAL double prism.
The two cut endpoints and the rotation-boundary cylinder are killed
SEPARATELY. This never assumes cochain zero on all four-face union
and never treats either ordinary prism as an absolute cycle. -/
@[expose] public section
namespace Finsler.DoublePrismCochainBoundary
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.DoubleRelativeTimeCylinder
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem prism_zero {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (q : ℕ)
    (κ : singularCochainGroup (ZMod 2) Y (q + 1)) (hκ : cochainPullback H.h (q + 1) κ = 0) :
    (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ = 0 := by
  rw [← TimeShuffleComparison.rectangle_eq_prism, TimeShuffleComparison.rectangle, Category.assoc]
  change _ ≫ cochainPullback H.h (q + 1) κ = 0
  rw [hκ, comp_zero]

theorem prism_pre_zero {X Y Z : TopCat.{0}} {f g : Y ⟶ Z} (H : TopCat.Homotopy f g) (e : X ⟶ Y) (q : ℕ)
    (κ : singularCochainGroup (ZMod 2) Z (q + 1))
    (hκ : cochainPullback (H.comp (TopCat.Homotopy.refl e)).h (q + 1) κ = 0) :
    cochainPullback e q ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ) = 0 := by
  change (push e).f q ≫ ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ) = 0
  rw [← Category.assoc, TimePrismNaturality.prism_pre]
  exact prism_zero _ q κ hκ

def rotationFaces (X : TopCat.{0}) : Set (cylinder (cylinder X)) := {z | z.2 ∈ boundary X}

theorem rotation_prism_zero (X : TopCat.{0}) (q : ℕ)
    (κ : singularCochainGroup (ZMod 2) (cylinder (cylinder X)) (q + 1))
    (hκ : cochainPullback (SupportedCap.subspaceMap _ (rotationFaces X)) (q + 1) κ = 0) :
    cochainPullback (SupportedCap.subspaceMap (cylinder X) (boundary X)) q
      (((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ) = 0 :=
  prism_pre_zero (homotopy (cylinder X)) (SupportedCap.subspaceMap (cylinder X) (boundary X)) q κ
    (CochainCarrierPullbackZero.family_zero (rotationFaces X) (q + 1) κ hκ _ (fun z => z.1.property))

theorem double_boundary_zero (X : TopCat.{0}) (q : ℕ)
    (κ : singularCochainGroup (ZMod 2) (cylinder (cylinder X)) (q + 1))
    (h0 : cochainPullback (atTime (cylinder X) 0) (q + 1) κ = 0)
    (h1 : cochainPullback (atTime (cylinder X) 1) (q + 1) κ = 0)
    (hrot : cochainPullback (SupportedCap.subspaceMap _ (rotationFaces X)) (q + 1) κ = 0) :
    (chains X).iCycles q ≫ NativeGlobalTimeSquare.squarePrism X q ≫
      cochainCoboundary (ZMod 2) (cylinder (cylinder X)) (q + 1) κ = 0 := by
  have hc := RelativePrismCochainBoundary.ordinary_boundary_zero (boundary X) (homotopy X)
    (fun _ => Or.inl rfl) (fun _ => Or.inr rfl) q
    (((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ)
    (rotation_prism_zero X q κ hrot)
  have he : (push (atTime (cylinder X) 0)).f (q + 1) =
      (chains (cylinder X)).d (q + 1) q ≫
        ((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) +
      ((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫
        (chains (cylinder (cylinder X))).d (q + 2) (q + 1) +
      (push (atTime (cylinder X) 1)).f (q + 1) := by
    simpa only [push, SmallChainCarrier.chains, Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
      ((homotopy (cylinder X)).toSSet.chainComplexMap coeff).comm (q + 1)
  have hz0 : (push (atTime (cylinder X) 0)).f (q + 1) ≫ κ = 0 := h0
  have hz1 : (push (atTime (cylinder X) 1)).f (q + 1) ≫ κ = 0 := h1
  have hb := congrArg (fun a => (chains X).iCycles q ≫
    ((homotopy X).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ a ≫ κ) he
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, hz0, hz1, comp_zero, hc, add_zero, zero_add] at hb
  exact hb.symm

end
end Finsler.DoublePrismCochainBoundary
