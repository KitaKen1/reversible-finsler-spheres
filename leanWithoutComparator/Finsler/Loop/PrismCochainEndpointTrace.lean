module

public import Finsler.Loop.RelativePrismCochainBoundary

/-! Keep the genuine endpoint term when evaluating a coboundary on
an ordinary interval prism. Only the original source is a cycle; the
prism itself is not treated as an absolute cycle. -/
@[expose] public section
namespace Finsler.PrismCochainEndpointTrace
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem boundary {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (p : ℕ) (hp : 1 ≤ p)
    (κ : singularCochainGroup (ZMod 2) Y p) :
    (chains X).iCycles p ≫ (H.toSSet.chainComplexMap coeff).hom p (p + 1) ≫
      cochainCoboundary (ZMod 2) Y p κ =
    (chains X).iCycles p ≫ cochainPullback f p κ - (chains X).iCycles p ≫ cochainPullback g p κ := by
  cases p with
  | zero => omega
  | succ q =>
    have he : (push f).f (q + 1) =
        (chains X).d (q + 1) q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1) +
        (H.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫ (chains Y).d (q + 2) (q + 1) +
        (push g).f (q + 1) := by
      simpa only [push, SmallChainCarrier.chains, Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
        (H.toSSet.chainComplexMap coeff).comm (q + 1)
    have hb := congrArg (fun u => (chains X).iCycles (q + 1) ≫ u ≫ κ) he
    simp only [Preadditive.add_comp, Preadditive.comp_add] at hb
    have hz : (chains X).iCycles (q + 1) ≫
        ((chains X).d (q + 1) q ≫ (H.toSSet.chainComplexMap coeff).hom q (q + 1)) ≫ κ = 0 := by
      rw [← Category.assoc, ← Category.assoc, (chains X).iCycles_d, zero_comp, zero_comp]
    rw [hz, zero_add] at hb
    change (chains X).iCycles (q + 1) ≫
      ((H.toSSet.chainComplexMap coeff).hom (q + 1) (q + 2) ≫ (chains Y).d (q + 2) (q + 1)) ≫ κ = _
    exact eq_sub_iff_add_eq.mpr hb.symm

theorem boundary_zero_iff {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (p : ℕ) (hp : 1 ≤ p)
    (κ : singularCochainGroup (ZMod 2) Y p) :
    (chains X).iCycles p ≫ (H.toSSet.chainComplexMap coeff).hom p (p + 1) ≫
      cochainCoboundary (ZMod 2) Y p κ = 0 ↔
    (chains X).iCycles p ≫ cochainPullback f p κ = (chains X).iCycles p ≫ cochainPullback g p κ := by
  rw [boundary H p hp κ, sub_eq_zero]

theorem endpoint_sub_eq_of_same_boundary {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (p : ℕ) (hp : 1 ≤ p)
    (κ χ : singularCochainGroup (ZMod 2) Y p)
    (h : cochainCoboundary (ZMod 2) Y p κ = cochainCoboundary (ZMod 2) Y p χ) :
    (chains X).iCycles p ≫ cochainPullback f p κ - (chains X).iCycles p ≫ cochainPullback g p κ =
    (chains X).iCycles p ≫ cochainPullback f p χ - (chains X).iCycles p ≫ cochainPullback g p χ := by
  rw [← boundary H p hp κ, ← boundary H p hp χ, h]

end
end Finsler.PrismCochainEndpointTrace
