module

public import Finsler.Loop.ComplementRotationShear
public import Finsler.Loop.PeriodicSquareCochainBoundary

/-! The actual shear homotopy gives a primitive whose cut restrictions
vanish and whose rotation restrictions agree. Consequently the original
double-prism values agree for every closed diagonal-zero Thom test. -/
@[expose] public section
namespace Finsler.ComplementRotationShearCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeBVRotationSquare Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (n q : ℕ) (T : singularCochainGroup (ZMod 2) (parameters n) (q + 2))

def primitive : singularCochainGroup (ZMod 2) (squareDomain n) (q + 1) :=
  ((ComplementRotationShear.homotopy n).toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫ T

theorem boundary (hT : cochainCoboundary (ZMod 2) _ (q + 2) T = 0) :
    cochainCoboundary (ZMod 2) _ (q + 1) (primitive n q T) =
      cochainPullback (ComplementRotationShear.reflected n) (q + 2) T -
        cochainPullback (intoCut n ≫ WholeSelfCutComplement.complement n) (q + 2) T := by
  have he : (push (ComplementRotationShear.reflected n)).f (q + 2) =
      (chains (squareDomain n)).d (q + 2) (q + 1) ≫
        ((ComplementRotationShear.homotopy n).toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) +
      ((ComplementRotationShear.homotopy n).toSSet.chainComplexMap coeff).hom (q + 2) (q + 3) ≫
        (chains (parameters n)).d (q + 3) (q + 2) +
      (push (intoCut n ≫ WholeSelfCutComplement.complement n)).f (q + 2) := by
    simpa only [push, chains, Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
      ((ComplementRotationShear.homotopy n).toSSet.chainComplexMap coeff).comm (q + 2)
  have hb := congrArg (fun f => f ≫ T) he
  have hz : (chains (parameters n)).d (q + 3) (q + 2) ≫ T = 0 := hT
  simp only [Preadditive.add_comp, Category.assoc, hz, comp_zero, add_zero] at hb
  exact eq_sub_iff_add_eq.mpr hb.symm

theorem cut_zero
    (hT : cochainPullback (SupportedCap.subspaceMap _ (FilteredGlobalThomTime.endpointCarrier n)) (q + 2) T = 0)
    (t : _root_.unitInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (DoubleRelativeTimeCylinder.atTime (rotationDomain n) t) (q + 1) (primitive n q T) = 0 :=
  DoublePrismCochainBoundary.prism_pre_zero (ComplementRotationShear.homotopy n) _ (q + 1) T
    (CochainCarrierPullbackZero.family_zero (FilteredGlobalThomTime.endpointCarrier n) (q + 2) T hT _
      (fun z => ComplementRotationShear.cut_face_diagonal n t ht z.2.down z.1))

theorem rotation_equal :
    cochainPullback (rotationFace n 0) (q + 1) (primitive n q T) =
      cochainPullback (rotationFace n 1) (q + 1) (primitive n q T) := by
  change (push (rotationFace n 0)).f (q + 1) ≫ (_ ≫ T) =
    (push (rotationFace n 1)).f (q + 1) ≫ (_ ≫ T)
  rw [← Category.assoc, TimePrismNaturality.prism_pre,
    ← Category.assoc ((push (rotationFace n 1)).f (q + 1)), TimePrismNaturality.prism_pre]
  exact congrArg (fun k => k ≫ T) (TimePrismNaturality.prism_congr _ _
    (ComplementRotationShear.rotation_homotopies n) (q + 1))

theorem square_boundary_zero
    (hT : cochainPullback (SupportedCap.subspaceMap _ (FilteredGlobalThomTime.endpointCarrier n)) (q + 2) T = 0) :
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainCoboundary (ZMod 2) _ (q + 1) (primitive n q T) = 0 :=
  PeriodicSquareCochainBoundary.double_boundary_zero (Loops n) q (primitive n q T)
    (cut_zero n q T hT 0 (Or.inl rfl)) (cut_zero n q T hT 1 (Or.inr rfl)) (rotation_equal n q T)

theorem square_values (hT : cochainCoboundary (ZMod 2) _ (q + 2) T = 0)
    (hD : cochainPullback (SupportedCap.subspaceMap _ (FilteredGlobalThomTime.endpointCarrier n)) (q + 2) T = 0) :
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (ComplementRotationShear.reflected n) (q + 2) T =
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (intoCut n ≫ WholeSelfCutComplement.complement n) (q + 2) T := by
  have hz := square_boundary_zero n q T hD
  rw [boundary n q T hT, Preadditive.comp_sub, Preadditive.comp_sub] at hz
  exact sub_eq_zero.mp hz

end
end Finsler.ComplementRotationShearCochain
