module

public import Finsler.Topology.TimePrismDescent
public import Finsler.Topology.SmallChainCarrier

/-! Integrating a full cap coboundary over the genuine time prism
gives an explicit boundary on input cycles when the primitive vanishes
at both endpoints. The time-prism chain itself is never assumed closed. -/

@[expose] public section
namespace Finsler.TimePrismCapCoboundary

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SmallChainCarrier Finsler.CochainComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem cycle_boundary {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {g₀ g₁ : C ⟶ D} (H : Homotopy g₀ g₁) (n q : ℕ) (hn : 0 < n)
    (c₀ : D.X n ⟶ E.X q) (c₁ : D.X (n + 1) ⟶ E.X (q + 1))
    (v : D.X (n + 1) ⟶ E.X q)
    (hc : c₁ ≫ E.d (q + 1) q = D.d (n + 1) n ≫ c₀ - v)
    (h₀ : g₀.f n ≫ c₀ = 0) (h₁ : g₁.f n ≫ c₀ = 0)
    (z : coeff ⟶ C.X n) (hz : z ≫ C.d n (n - 1) = 0) :
    z ≫ H.hom n (n + 1) ≫ v =
      -(z ≫ H.hom n (n + 1) ≫ c₁) ≫ E.d (q + 1) q := by
  cases n with
  | zero => omega
  | succ n =>
    have hcycle : z ≫ C.d (n + 1) n = 0 := by simpa only [Nat.succ_sub_one] using hz
    have h := congrArg (fun k => z ≫ k ≫ c₀) (H.comm (n + 1))
    simp only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc, h₀, h₁,
      comp_zero, add_zero] at h
    have hb : z ≫ H.hom (n + 1) (n + 2) ≫ D.d (n + 2) (n + 1) ≫ c₀ = 0 := by
      simpa only [← Category.assoc, hcycle, zero_comp, zero_add] using h.symm
    have hout : (z ≫ H.hom (n + 1) (n + 2) ≫ c₁) ≫ E.d (q + 1) q =
        -(z ≫ H.hom (n + 1) (n + 2) ≫ v) := by
      calc
        _ = z ≫ H.hom (n + 1) (n + 2) ≫ (c₁ ≫ E.d (q + 1) q) := by simp only [Category.assoc]
        _ = z ≫ H.hom (n + 1) (n + 2) ≫ (D.d (n + 2) (n + 1) ≫ c₀ - v) := by rw [hc]
        _ = (z ≫ H.hom (n + 1) (n + 2) ≫ D.d (n + 2) (n + 1) ≫ c₀) -
            (z ≫ H.hom (n + 1) (n + 2) ≫ v) := by
          simp only [Preadditive.comp_sub, Category.assoc]
        _ = _ := by rw [hb, zero_sub]
    simpa only [Preadditive.neg_comp, neg_neg] using (congrArg (fun u => -u) hout).symm

end
end Finsler.TimePrismCapCoboundary
