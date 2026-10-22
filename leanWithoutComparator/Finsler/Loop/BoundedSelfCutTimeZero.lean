module

public import Finsler.Loop.BoundedSelfCutTimeExternalJoin
public import Finsler.Loop.BoundedCarrierEmpty

/-! Both nonpositive length branches vanish in the actual geometric
self-time/external-beta/join components, before passing to homology.
These are the genuine bounded and original proper time components. -/

@[expose] public section
namespace Finsler.BoundedSelfCutTimeZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalPreadditive HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ) (hr : r < 1)
  {κ δ ρ : ℝ} (hκ : 0 < κ) (hκR : 2 * κ ≤ R) (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)
  (otherIndex : Q → Q)
  (hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
    OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c))

theorem bounded_tensor_zero (hB : a - L + 3 * ε ≤ 0) (i j : ℕ) :
    BoundedSelfCutTimeExternalJoin.tensorInput α β r hr h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA otherIndex hother i j = 0 := by
  have hz := BoundedCarrierEmpty.component_zero α r hr F (a - L + 3 * ε)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ)
    (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA true) hB i
  dsimp only [BoundedSelfCutTimeExternalJoin.tensorInput]
  rw [hz, zero_tensor]

theorem bounded_geometric_zero (hB : a - L + 3 * ε ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    BoundedSelfCutTimeExternalJoin.geometric α β R r hr hκ hκR h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA otherIndex hother i j k hij = 0 := by
  rw [BoundedSelfCutTimeExternalJoin.geometric,
    bounded_tensor_zero α β r hr h p T hT F ε a L σ hσ hε hradius hsmall firstIndex hfirst hshortT hA
      otherIndex hother hB i j, zero_comp]

include hε hradius hsmall hshortT hA in
theorem original_first_nonpos_zero (hB : a - L + 3 * ε ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    FirstInputSelfCutTimeFactorization.geometric α β R r hr hκ hκR h p T hT σ hσ firstIndex hfirst
      otherIndex hother i j k hij = 0 := by
  have he := BoundedSelfCutTimeExternalJoin.to_proper α β R r hr hκ hκR h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA otherIndex hother i j k hij
  rw [bounded_geometric_zero α β R r hr hκ hκR h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA otherIndex hother hB i j k hij, zero_comp] at he
  exact he.symm

theorem other_zero {b : ℝ} (hβ : ∀ y, SobolevLength.length F (β y) < b) (hb : b ≤ 0) (j : ℕ) :
    FirstInputSelfCutTimeFactorization.otherSection β σ hσ otherIndex hother j = 0 := by
  have := BoundedCarrierEmpty.family_empty β F hβ hb
  exact (EmptySingularChains.chains_zero (TopCat.of Q) j).eq_of_src _ _

theorem original_beta_nonpos_zero {b : ℝ} (hβ : ∀ y, SobolevLength.length F (β y) < b) (hb : b ≤ 0)
    (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    FirstInputSelfCutTimeFactorization.geometric α β R r hr hκ hκR h p T hT σ hσ firstIndex hfirst
      otherIndex hother i j k hij = 0 := by
  rw [FirstInputSelfCutTimeFactorization.geometric, other_zero β F σ hσ otherIndex hother hβ hb j,
    tensor_zero, zero_comp]

end
end Finsler.BoundedSelfCutTimeZero
