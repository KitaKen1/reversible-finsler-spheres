module

public import Finsler.Loop.CylinderReflectionCochain
public import Finsler.Loop.ComplementRotationShearCochain

/-! The ORIGINAL full-period rotation maps source cycles to ACTUAL
cycles. Apply the cylinder contraction/endpoint-trace shortcut there
to remove cut-time reflection, then combine with the actual shear. -/
@[expose] public section
namespace Finsler.NativeBVForwardSquare
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeBVRotationSquare Finsler.SelfCutThomCocycle
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem reflected_map (n : ℕ) : ComplementRotationShear.reflected n =
    intoCut n ≫ CylinderReflectionCochain.reflection (Loops n) := by
  ext z : 1
  rfl

theorem cylinder_prism (n q : ℕ) :
    ((DoubleRelativeTimeCylinder.homotopy (Loops n)).toSSet.chainComplexMap coeff).hom q (q + 1) =
      SelfCutTimePrism.prism n q := by
  apply TimePrismNaturality.prism_congr
  ext z : 1
  rfl

theorem rotated_prism_values (n q : ℕ)
    (T : singularCochainGroup (ZMod 2) (parameters n) (q + 2))
    (hT : cochainCoboundary (ZMod 2) _ (q + 2) T = 0)
    (h0 : cochainPullback (atTime n 0) (q + 2) T = 0) :
    (chains (Loops n)).iCycles q ≫ (H1LoopRotation.chainHomotopy n).hom q (q + 1) ≫
      SelfCutTimePrism.prism n (q + 1) ≫
        cochainPullback (CylinderReflectionCochain.reflection (Loops n)) (q + 2) T =
    (chains (Loops n)).iCycles q ≫ (H1LoopRotation.chainHomotopy n).hom q (q + 1) ≫
      SelfCutTimePrism.prism n (q + 1) ≫ T := by
  have hc := congrArg (fun a => SelfHomotopySweep.cycles (H1LoopRotation.chainHomotopy n) q ≫ a)
    (CylinderReflectionCochain.cycle_values (Loops n) (q + 1) T hT h0)
  simp only [← Category.assoc, SelfHomotopySweep.cycles_i] at hc
  simpa only [SelfHomotopySweep.component, Category.assoc, cylinder_prism] using hc

theorem reflected_square_values (n q : ℕ)
    (T : singularCochainGroup (ZMod 2) (parameters n) (q + 2))
    (hT : cochainCoboundary (ZMod 2) _ (q + 2) T = 0)
    (h0 : cochainPullback (atTime n 0) (q + 2) T = 0) :
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (ComplementRotationShear.reflected n) (q + 2) T =
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (intoCut n) (q + 2) T := by
  rw [reflected_map, pullback_comp]
  change (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      (push (intoCut n)).f (q + 2) ≫ cochainPullback (CylinderReflectionCochain.reflection (Loops n)) (q + 2) T =
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫ (push (intoCut n)).f (q + 2) ≫ T
  have he := rotated_prism_values n q T hT h0
  simpa only [← Category.assoc, NativeBVRotationSquare.double_prism] using he

theorem complemented_square_values (n q : ℕ)
    (T : singularCochainGroup (ZMod 2) (parameters n) (q + 2))
    (hT : cochainCoboundary (ZMod 2) _ (q + 2) T = 0)
    (hD : cochainPullback (SupportedCap.subspaceMap _ (FilteredGlobalThomTime.endpointCarrier n)) (q + 2) T = 0) :
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (intoCut n ≫ WholeSelfCutComplement.complement n) (q + 2) T =
    (chains (Loops n)).iCycles q ≫ NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (intoCut n) (q + 2) T := by
  have h0 : cochainPullback (atTime n 0) (q + 2) T = 0 :=
    CochainCarrierPullbackZero.family_zero (FilteredGlobalThomTime.endpointCarrier n) (q + 2) T hD _ (fun _ => rfl)
  exact (ComplementRotationShearCochain.square_values n q T hT hD).symm.trans
    (reflected_square_values n q T hT h0)

end
end Finsler.NativeBVForwardSquare
