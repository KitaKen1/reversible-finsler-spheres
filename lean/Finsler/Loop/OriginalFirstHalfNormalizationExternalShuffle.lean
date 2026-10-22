module

public import Finsler.Loop.OriginalFirstHalfNormalizationCochains
public import Finsler.Loop.NormalizedCapShuffleTensor

/-! Exact external-product factorization of the normalized literal
original-cylinder gamma, including its nonclosed tested zero extension.
The first factor is the actual whole cut-time x first-input space. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfNormalizationExternalShuffle

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity Finsler.SupportedCapNaturality
open Finsler.OriginalFirstHalfCupOneCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))

def reorder : TopCat.of (ClosedInterval × P) ⊗ TopCat.of Q ⟶ ambient α β :=
  TopCat.ofHom ⟨fun z => (z.1.1, (z.1.2, z.2)), by fun_prop⟩

theorem first_input_square : reorder α β ≫ firstInput α β =
    CartesianMonoidalCategory.fst (TopCat.of (ClosedInterval × P)) (TopCat.of Q) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

variable (r : ℝ) (hr : r < 1) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)

theorem cochain_factorization :
    cochainPullback (reorder α β) ((m + 1) + p)
      (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) =
    cochainPullback (CartesianMonoidalCategory.fst (TopCat.of (ClosedInterval × P)) (TopCat.of Q)) ((m + 1) + p)
      (SingularNormalization.normalize (TopCat.of (ClosedInterval × P)) ((m + 1) + p)
        (FirstInputRotationZeroTimeFactors.originalGamma α r hr h p T)) := by
  rw [OriginalFirstHalfNormalizationCochains.normalized_first_input, ← pullback_comp, first_input_square]

theorem component_cap (i j : ℕ) :
    SingularChainCross.component (TopCat.of (ClosedInterval × P)) (TopCat.of Q) (((m + 1) + p) + i) j ≫
      (push (reorder α β)).f ((((m + 1) + p) + i) + j) ≫
      absoluteChain (ambient α β) ((m + 1) + p) (i + j) ((((m + 1) + p) + i) + j) (by omega)
        (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) =
    (absoluteChain (TopCat.of (ClosedInterval × P)) ((m + 1) + p) i (((m + 1) + p) + i) rfl
      (SingularNormalization.normalize (TopCat.of (ClosedInterval × P)) ((m + 1) + p)
        (FirstInputRotationZeroTimeFactors.originalGamma α r hr h p T)) ▷ (chains (TopCat.of Q)).X j) ≫
      SingularChainCross.component (TopCat.of (ClosedInterval × P)) (TopCat.of Q) i j ≫
      (push (reorder α β)).f (i + j) := by
  have hn := RelativeCapBoundary.absolute_chain_natural (reorder α β) ((m + 1) + p) (i + j)
    ((((m + 1) + p) + i) + j) (by omega)
    (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T)
  change absoluteChain (TopCat.of (ClosedInterval × P) ⊗ TopCat.of Q) ((m + 1) + p) (i + j)
      ((((m + 1) + p) + i) + j) (by omega)
      (cochainPullback (reorder α β) ((m + 1) + p)
        (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T)) ≫
      (push (reorder α β)).f (i + j) =
    (push (reorder α β)).f ((((m + 1) + p) + i) + j) ≫
      absoluteChain (ambient α β) ((m + 1) + p) (i + j) ((((m + 1) + p) + i) + j) (by omega)
        (OriginalFirstHalfNormalizationCochains.normalized α β r hr h p T) at hn
  rw [← hn, cochain_factorization, ← Category.assoc,
    NormalizedCapShuffleTensor.normalized_component]
  simp only [Category.assoc]

end
end Finsler.OriginalFirstHalfNormalizationExternalShuffle
