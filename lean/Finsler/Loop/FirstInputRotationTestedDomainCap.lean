module

public import Finsler.Loop.FirstInputRotationTestedCap

/-! Retain the bounded proper cut domain before applying the fixed
output. This preserves a chain-monic source projection, needed for
relative time-prism and endpoint-collar arguments. -/

@[expose] public section
namespace Finsler.FirstInputRotationTestedDomainCap

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputRotationCochains Finsler.FirstInputRotationFilteredCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric n) (B η : ℝ)
  (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)

def operation : DegreeLoweringHomology.Map
    (small (space α β R r) (rectangle α β R r η))
    (chains (TopCat.of (domain α β R r hR hr F B))) p :=
  CapOutputSupport.operation (rectangle α β R r η) (𝟙 (space α β R r))
    (domain α β R r hR hr F B) p (tested α β R r hR hr p T)
    (fun q σ hc z hz => hgood q σ hc z hz) (tested_closed α β R r hR hr p T hT)

theorem component_inclusion (q : ℕ) :
    (operation α β R r hR hr F B η p T hgood hT).component q ≫
      (push (source α β R r hR hr F B)).f q =
        (inclusion (space α β R r) (rectangle α β R r η)).f (p + q) ≫
          absoluteChain (space α β R r) p q (p + q) rfl (tested α β R r hR hr p T) := by
  have he := CapOutputSupport.component_inclusion (rectangle α β R r η) (𝟙 (space α β R r))
    (domain α β R r hR hr F B) p (tested α β R r hR hr p T)
    (fun q σ hc z hz => hgood q σ hc z hz) q
  have hid : push (𝟙 (space α β R r)) = 𝟙 (chains (space α β R r)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map
      (TopCat.toSSet.map (𝟙 (space α β R r))) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.id_f] at he
  exact he.trans (congrArg (fun g => (inclusion (space α β R r) (rectangle α β R r η)).f (p + q) ≫ g)
    (Category.comp_id (absoluteChain (space α β R r) p q (p + q) rfl (tested α β R r hR hr p T))))

end
end Finsler.FirstInputRotationTestedDomainCap
