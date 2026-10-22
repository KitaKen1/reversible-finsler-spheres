module

public import Finsler.Loop.DoublePrismCochainBoundary
public import Finsler.Loop.CylinderPrismNaturality

/-! A square coboundary vanishes on source cycles when the cut faces
vanish and the two rotation faces AGREE. No individual vanishing of
the rotation faces, or absolute-cycle assertion for the prism, is used. -/
@[expose] public section
namespace Finsler.PeriodicSquareCochainBoundary
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.DoubleRelativeTimeCylinder
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem prism_boundary_equal_faces {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (q : ℕ) (T : singularCochainGroup (ZMod 2) Y q)
    (hT : cochainPullback f q T = cochainPullback g q T) :
    (chains X).iCycles q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (chains Y).d (q + 1) q ≫ T = 0 := by
  have he := (H.toSSet.chainComplexMap coeff).comm q
  have hb := congrArg (fun a => (chains X).iCycles q ≫ a ≫ T) he
  have ht : (push f).f q ≫ T = (push g).f q ≫ T := hT
  cases q with
  | zero =>
    simp only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
      zero_add, Preadditive.add_comp, Preadditive.comp_add, Category.assoc] at hb
    change (chains X).iCycles 0 ≫ (push f).f 0 ≫ T = _ at hb
    rw [ht] at hb
    exact add_right_cancel (hb.symm.trans (zero_add _).symm)
  | succ q =>
    simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc] at hb
    change (chains X).iCycles (q + 1) ≫ (push f).f (q + 1) ≫ T = _ at hb
    rw [ht] at hb
    have hz : (chains X).iCycles (q + 1) ≫ (chains X).d (q + 1) q = 0 :=
      (chains X).iCycles_d _ _
    simp only [← Category.assoc, hz, zero_comp, zero_add] at hb
    exact add_right_cancel (hb.symm.trans (zero_add _).symm)

def rotationFace (X : TopCat.{0}) (s : _root_.unitInterval) :
    cylinder X ⟶ cylinder (cylinder X) := CylinderPrismNaturality.map (atTime X s)

theorem rotation_prism_equal (X : TopCat.{0}) (q : ℕ)
    (κ : singularCochainGroup (ZMod 2) (cylinder (cylinder X)) (q + 1))
    (hκ : cochainPullback (rotationFace X 0) (q + 1) κ =
      cochainPullback (rotationFace X 1) (q + 1) κ) :
    cochainPullback (atTime X 0) q
        (((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ) =
      cochainPullback (atTime X 1) q
        (((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ) := by
  change (push (atTime X 0)).f q ≫ (AnnularTimeTrim.prism (cylinder X) q ≫ κ) =
    (push (atTime X 1)).f q ≫ (AnnularTimeTrim.prism (cylinder X) q ≫ κ)
  rw [← Category.assoc, CylinderPrismNaturality.prism, Category.assoc,
    ← Category.assoc ((push (atTime X 1)).f q), CylinderPrismNaturality.prism, Category.assoc]
  exact congrArg (fun T => AnnularTimeTrim.prism X q ≫ T) hκ

theorem double_boundary_zero (X : TopCat.{0}) (q : ℕ)
    (κ : singularCochainGroup (ZMod 2) (cylinder (cylinder X)) (q + 1))
    (h0 : cochainPullback (atTime (cylinder X) 0) (q + 1) κ = 0)
    (h1 : cochainPullback (atTime (cylinder X) 1) (q + 1) κ = 0)
    (hrot : cochainPullback (rotationFace X 0) (q + 1) κ =
      cochainPullback (rotationFace X 1) (q + 1) κ) :
    (chains X).iCycles q ≫ NativeGlobalTimeSquare.squarePrism X q ≫
      cochainCoboundary (ZMod 2) (cylinder (cylinder X)) (q + 1) κ = 0 := by
  have hc := prism_boundary_equal_faces (homotopy X) q
    (((homotopy (cylinder X)).toSSet.chainComplexMap coeff).hom q (q + 1) ≫ κ)
    (rotation_prism_equal X q κ hrot)
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
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, hz0, hz1,
    comp_zero, hc, add_zero, zero_add] at hb
  exact hb.symm

end
end Finsler.PeriodicSquareCochainBoundary
