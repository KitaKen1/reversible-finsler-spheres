module

public import Finsler.Loop.BoundedCarrierUniformRawJoin
public import Finsler.Loop.StrictLengthProductBudget

/-! The actual bounded near join has a genuine coupled filtered output
map at a radius chosen before the individual thresholds. Equality of
its actual proper-near chain source with the original bounded output
source implies equality in the literal same strict length target. -/

@[expose] public section
namespace Finsler.BoundedCarrierFilteredOutput

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.StrictLengthEnergyBridge

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) {ε : ℝ} (hε : 0 < ε)
  (R : ℝ) (hR : R ≤ 1 / 2) (hRu : R < BoundedCarrierUniformRawJoin.radius α β r hr F hε)
  {a b A L : ℝ} (hab : a + b < A) (hβ : ∀ y, SobolevLength.length F (β y) < b)

def joinMap := BoundedCarrierUniformRawJoin.joinMap α β r hr F hε R hR hRu (a - L + 3 * ε) b hβ ≫
  StrictLengthProductBudget.outputInclusion F hab hε

theorem loop_square : joinMap α β r hr F hε R hR hRu (L := L) hab hβ ≫
    SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F (A - L + 5 * ε)) =
    BoundedKeptProductInputs.properTube α β r hr F (a - L + 3 * ε) R ≫
      TopCat.ofHom (OriginalFirstHalfCutOutputJoinGeometry.joined α β R r hr hR) := by
  rw [joinMap, Category.assoc, StrictLengthProductBudget.outputInclusion_source,
    BoundedCarrierUniformRawJoin.loop_square]

theorem component_eq {M : ModuleCat.{0} (ZMod 2)} (k : ℕ)
    (cn : M ⟶ (chains (TopCat.of (CompactNearJoinParameters.tube
      (BoundedKeptProductInputs.kept α r hr F (a - L + 3 * ε)) β R))).X k)
    (co : M ⟶ (chains (TopCat.of (OriginalFirstHalfJointSupportedCap.bounded α β R r hR hr F (A - L + 5 * ε)))).X k)
    (hc : cn ≫ (push (BoundedKeptProductInputs.properTube α β r hr F (a - L + 3 * ε) R)).f k =
      co ≫ (push (OriginalFirstHalfCutOutputJoinBounded.toNear α β R r hR hr F (A - L + 5 * ε))).f k) :
    cn ≫ (push (joinMap α β r hr F hε R hR hRu (L := L) hab hβ)).f k =
    co ≫ (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F (A - L + 5 * ε))).f k := by
  have : Mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F (A - L + 5 * ε)))).f k) := SupportedCap.subspacePush_mono _ _ _
  apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F (A - L + 5 * ε)))).f k)).mp
  have hn := congrArg (fun z => (push z).f k) (loop_square α β r hr F hε R hR hRu (L := L) hab hβ)
  have ho := congrArg (fun z => (push z).f k)
    (OriginalFirstHalfCutOutputJoinBounded.output_square α β R r hR hr F (A - L + 5 * ε))
  simp only [push_comp, HomologicalComplex.comp_f] at hn ho
  rw [Category.assoc, hn, ← Category.assoc, hc, Category.assoc, ho, ← Category.assoc]
  rfl

end
end Finsler.BoundedCarrierFilteredOutput
