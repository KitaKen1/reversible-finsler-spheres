module

public import Finsler.Loop.TimePrismCapCoboundaryAnySource

/-! Include input degree zero in the genuine time-prism cap boundary.
The zero case follows from the actual degree-zero homotopy equation. -/

@[expose] public section
namespace Finsler.TimePrismCapCoboundaryAllDegrees

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SmallChainCarrier Finsler.CochainComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem cycle_boundary {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {g₀ g₁ : C ⟶ D} (H : Homotopy g₀ g₁) (n q : ℕ)
    (c₀ : D.X n ⟶ E.X q) (c₁ : D.X (n + 1) ⟶ E.X (q + 1))
    (v : D.X (n + 1) ⟶ E.X q)
    (hc : c₁ ≫ E.d (q + 1) q = D.d (n + 1) n ≫ c₀ - v)
    (h₀ : g₀.f n ≫ c₀ = 0) (h₁ : g₁.f n ≫ c₀ = 0)
    {Z : ModuleCat.{0} (ZMod 2)} (z : Z ⟶ C.X n) (hz : z ≫ C.d n (n - 1) = 0) :
    z ≫ H.hom n (n + 1) ≫ v =
      -(z ≫ H.hom n (n + 1) ≫ c₁) ≫ E.d (q + 1) q := by
  cases n with
  | succ n => exact TimePrismCapCoboundaryAnySource.cycle_boundary H (n + 1) q (by omega) c₀ c₁ v hc h₀ h₁ z hz
  | zero =>
    have hb : H.hom 0 1 ≫ D.d 1 0 ≫ c₀ = 0 := by
      have hh := congrArg (fun f => f ≫ c₀) (H.comm 0)
      simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        Preadditive.add_comp, Category.assoc, h₀, h₁, zero_comp, zero_add, add_zero] using hh.symm
    have hout : (z ≫ H.hom 0 1 ≫ c₁) ≫ E.d (q + 1) q = -(z ≫ H.hom 0 1 ≫ v) := by
      calc
        _ = z ≫ H.hom 0 1 ≫ (c₁ ≫ E.d (q + 1) q) := by simp only [Category.assoc]
        _ = z ≫ H.hom 0 1 ≫ (D.d 1 0 ≫ c₀ - v) := by rw [hc]
        _ = (z ≫ H.hom 0 1 ≫ D.d 1 0 ≫ c₀) - (z ≫ H.hom 0 1 ≫ v) := by
          simp only [Preadditive.comp_sub, Category.assoc]
        _ = _ := by rw [hb, comp_zero, zero_sub]
    simpa only [Preadditive.neg_comp, neg_neg] using (congrArg (fun u => -u) hout).symm

end
end Finsler.TimePrismCapCoboundaryAllDegrees
