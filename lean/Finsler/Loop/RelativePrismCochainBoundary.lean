module

public import Finsler.Loop.DoubleRelativeTimeCylinder
public import Finsler.Topology.RelativeCupCochain

/-! An ACTUAL prism whose endpoints lie in B kills the coboundary
of ANY cochain vanishing on B, on genuine source cycles. Use the real
relative prism and actual relative cochain lift: do not assume that
the absolute prism input is a cycle. No cochain closure is required. -/
@[expose] public section
namespace Finsler.RelativePrismCochainBoundary
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem toAmbient_eq (Q : TopPair.{0}) (p : ℕ) (ψ : RelativeCupCochain.relative Q p) :
    (Q.singularChainComplexπ coeff).f p ≫ ψ = RelativeCupCochain.toAmbient Q p ψ := rfl

theorem relative_cycle_boundary_zero (Q : TopPair.{0}) (p : ℕ) {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains Q.fst).X (p + 1))
    (hu : (u ≫ (Q.singularChainComplexπ coeff).f (p + 1)) ≫ (Q.singularChainComplex coeff).d (p + 1) p = 0)
    (χ : singularCochainGroup (ZMod 2) Q.fst p) (hχ : cochainPullback Q.map p χ = 0) :
    u ≫ (chains Q.fst).d (p + 1) p ≫ χ = 0 := by
  obtain ⟨ψ, hψ⟩ := RelativeCupCochain.exists_lift Q p χ hχ
  have hψ' : (Q.singularChainComplexπ coeff).f p ≫ ψ = χ := (toAmbient_eq Q p ψ).trans hψ
  have hc : (Q.singularChainComplexπ coeff).f (p + 1) ≫
      (Q.singularChainComplex coeff).d (p + 1) p =
      (chains Q.fst).d (p + 1) p ≫ (Q.singularChainComplexπ coeff).f p :=
    (Q.singularChainComplexπ coeff).comm (p + 1) p
  calc
    _ = u ≫ ((chains Q.fst).d (p + 1) p ≫ (Q.singularChainComplexπ coeff).f p) ≫ ψ := by
      simpa only [Category.assoc] using
        congrArg (fun k => u ≫ (chains Q.fst).d (p + 1) p ≫ k) hψ'.symm
    _ = ((u ≫ (Q.singularChainComplexπ coeff).f (p + 1)) ≫ (Q.singularChainComplex coeff).d (p + 1) p) ≫ ψ := by
      simpa only [Category.assoc] using congrArg (fun k => u ≫ k ≫ ψ) hc.symm
    _ = 0 := by rw [hu, zero_comp]

theorem ordinary_boundary_zero {X Y : TopCat.{0}} (B : Set Y) {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (hf : ∀ x, f x ∈ B) (hg : ∀ x, g x ∈ B) (p : ℕ)
    (χ : singularCochainGroup (ZMod 2) Y p)
    (hχ : cochainPullback (SupportedCap.subspaceMap Y B) p χ = 0) :
    (chains X).iCycles p ≫ (H.toSSet.chainComplexMap coeff).hom p (p + 1) ≫ (chains Y).d (p + 1) p ≫ χ = 0 := by
  have hc := SelfHomotopySweep.cycles_closed (RelativePrismSweep.ordinary B H hf hg) p
  rw [RelativePrismSweep.ordinary_component] at hc
  have hrel : (((chains X).iCycles p ≫ (H.toSSet.chainComplexMap coeff).hom p (p + 1)) ≫
      ((RelativePrismSweep.targetPair B).singularChainComplexπ coeff).f (p + 1)) ≫
      ((RelativePrismSweep.targetPair B).singularChainComplex coeff).d (p + 1) p = 0 := by
    simpa only [Category.assoc] using hc
  exact relative_cycle_boundary_zero (RelativePrismSweep.targetPair B) p _ hrel χ hχ

end
end Finsler.RelativePrismCochainBoundary
