module

public import Finsler.Loop.NormalizedCapShuffleTensor
public import Finsler.Loop.OriginalFirstHalfCutNormalizedFactors

/-! Apply the general all-chain cap/shuffle identity to the actual
canonical proper self-cut gamma and the arbitrary second input. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizedCutShuffle

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem component_cap (i j : ℕ) :
    SingularChainCross.component (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (TopCat.of Q)
      (((m + 1) + p) + i) j ≫
      absoluteChain (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) ((m + 1) + p) (i + j)
        ((((m + 1) + p) + i) + j) (by omega)
        (SingularNormalization.normalize (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
          ((m + 1) + p) (OriginalFirstHalfCutProductCochains.gamma α r hr h p T (Q := Q))) =
    (absoluteChain (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) ((m + 1) + p) i
      (((m + 1) + p) + i) rfl (OriginalFirstHalfCutNormalizedFactors.normalized α r hr h p T) ▷
        (chains (TopCat.of Q)).X j) ≫
      SingularChainCross.component (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (TopCat.of Q) i j := by
  rw [OriginalFirstHalfCutNormalizedFactors.normalized_projection]
  exact NormalizedCapShuffleTensor.component_cap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
    (TopCat.of Q) ((m + 1) + p) i j _
      (OriginalFirstHalfCutNormalizedFactors.normalized_degeneracies α r hr h p T)

end
end Finsler.OriginalFirstHalfNormalizedCutShuffle
