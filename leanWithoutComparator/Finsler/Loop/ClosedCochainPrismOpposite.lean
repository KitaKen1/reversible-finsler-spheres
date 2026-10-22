module

public import Finsler.Loop.PrismCochainEndpointTrace
public import Finsler.Topology.TimePrismComparison

/-! Genuine prism identities for a closed cochain and for opposite
endpoint homotopies. Over F2, exact tests give equal opposite-prism
values on actual source cycles, including source degree zero. -/
@[expose] public section
namespace Finsler.ClosedCochainPrismOpposite
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem closed_boundary {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (q : ℕ) (T : singularCochainGroup (ZMod 2) Y (q + 1))
    (hT : cochainCoboundary (ZMod 2) Y (q + 1) T = 0) :
    cochainCoboundary (ZMod 2) X q ((H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ T) =
      cochainPullback f (q + 1) T - cochainPullback g (q + 1) T := by
  have he : (push f).f (q + 1) =
      (chains X).d (q + 1) q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) +
      (H.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫ (chains Y).d (q + 2) (q + 1) +
      (push g).f (q + 1) := by
    simpa only [push, chains, Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
      (H.toSSet.chainComplexMap coeff).comm (q + 1)
  have hb := congrArg (fun f => f ≫ T) he
  have hz : (chains Y).d (q + 2) (q + 1) ≫ T = 0 := hT
  simp only [Preadditive.add_comp, Category.assoc, hz, comp_zero, add_zero] at hb
  exact eq_sub_iff_add_eq.mpr hb.symm

theorem opposite_boundary_values {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (K : TopCat.Homotopy g f) (q : ℕ)
    (P : singularCochainGroup (ZMod 2) Y q) :
    (chains X).iCycles q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      cochainCoboundary (ZMod 2) Y q P =
    (chains X).iCycles q ≫ (K.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      cochainCoboundary (ZMod 2) Y q P := by
  have hs : (push f).f q - (push g).f q = (push g).f q - (push f).f q := by
    calc
      _ = -((push g).f q - (push f).f q) := (neg_sub _ _).symm
      _ = _ := (eq_neg_of_add_eq_zero_left (BorelCochain.two_eq_zero_of_mod _)).symm
  have hH := congrArg (fun a => a ≫ P)
    (TimePrismComparison.cycles_prism_boundary (H.toSSet.chainComplexMap coeff) q)
  have hK := congrArg (fun a => a ≫ P)
    (TimePrismComparison.cycles_prism_boundary (K.toSSet.chainComplexMap coeff) q)
  change ((chains X).iCycles q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1)) ≫
      (chains Y).d (q + 1) q ≫ P = (chains X).iCycles q ≫ ((push f).f q - (push g).f q) ≫ P at hH
  change ((chains X).iCycles q ≫ (K.toSSet.chainComplexMap coeff).hom q (q + 1)) ≫
      (chains Y).d (q + 1) q ≫ P = (chains X).iCycles q ≫ ((push g).f q - (push f).f q) ≫ P at hK
  change (chains X).iCycles q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) ≫
      (chains Y).d (q + 1) q ≫ P = (chains X).iCycles q ≫
      (K.toSSet.chainComplexMap coeff).hom q (q + 1) ≫ (chains Y).d (q + 1) q ≫ P
  simpa only [Category.assoc] using hH.trans ((congrArg (fun a => (chains X).iCycles q ≫ a ≫ P) hs).trans hK.symm)

end
end Finsler.ClosedCochainPrismOpposite
