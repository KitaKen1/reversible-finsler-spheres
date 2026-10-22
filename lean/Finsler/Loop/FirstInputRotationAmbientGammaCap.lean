module

public import Finsler.Loop.FirstInputRotationAmbientCupOne
public import Finsler.Loop.CapCupNested

/-! The genuine established bounded two-stage ambient cap has the
literal flat gamma cap source formula, with no assumption that its
ambient tested zero extension is closed. -/

@[expose] public section
namespace Finsler.FirstInputRotationAmbientGammaCap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1100000

private theorem transport_f {K D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : K ⟶ D) (i j : ℕ) (h : i = j) :
    eqToHom (congrArg K.X h) ≫ f.f j = f.f i ≫ eqToHom (congrArg D.X h) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (F : ReversibleMetric (m + 1)) (B η : ℝ)
  (good : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem component_source (q : ℕ) :
    (FirstInputRotationAmbientCap.operation α β R r hR hr p T (by omega) h F B η good hT).component q ≫
      (push (FirstInputRotationAmbientCap.source α β R r hR hr F B)).f q =
    (inclusion (FirstInputRotationAmbientCover.ambient α β R)
      (FirstInputRotationAmbientCover.cover α β R r η ρ)).f (((m + 1) + p) + q) ≫
      absoluteChain (FirstInputRotationAmbientCover.ambient α β R) ((m + 1) + p) q (((m + 1) + p) + q) rfl
        (FirstInputRotationAmbientCupOne.gamma α β R r hR hr h p T) := by
  rw [FirstInputRotationAmbientCap.component_source]
  have ht := transport_f
    (inclusion (FirstInputRotationAmbientCover.ambient α β R) (FirstInputRotationAmbientCover.cover α β R r η ρ))
    (((m + 1) + p) + q) ((m + 1) + (p + q)) (Nat.add_assoc (m + 1) p q)
  rw [← Category.assoc, ht, Category.assoc]
  exact congrArg (fun f => (inclusion (FirstInputRotationAmbientCover.ambient α β R)
    (FirstInputRotationAmbientCover.cover α β R r η ρ)).f (((m + 1) + p) + q) ≫ f)
    (CapCupNested.flat_nested _ (m + 1) p q _ _).symm

end
end Finsler.FirstInputRotationAmbientGammaCap
