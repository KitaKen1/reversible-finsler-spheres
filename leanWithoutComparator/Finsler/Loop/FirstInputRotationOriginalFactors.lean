module

public import Finsler.Loop.FirstInputRotationEndpoints

/-! At rotation zero the actual Thom and tested cochains factor through
the original first input and cut time. This is cochain-level independence
of the second input, before the fixed retained output is joined to it. -/

@[expose] public section
namespace Finsler.FirstInputRotationOriginalFactors

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.H1SelfCutNeighborhood Finsler.SelfCutThomCocycle
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputRotationCochains Finsler.FirstInputRotationEndpoints
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)

def projection : TopCat.of (FirstInputRotatingCut.source α β R r) ⟶
    TopCat.of (CompactRotatedCutData.source α r) :=
  TopCat.ofHom ⟨fun z => ⟨(z.val.1, z.val.2.val.1), z.property⟩, by fun_prop⟩

def originalEvaluation : TopCat.of (CompactRotatedCutData.source α r) ⟶ parameters n :=
  TopCat.ofHom ⟨fun z => (z.val.1, α z.val.2), by fun_prop⟩

def originalCut (hr : r < 1) : C(CompactRotatedCutData.source α r, H1SelfCutNeighborhood.tube n) := by
  refine ⟨fun z => ⟨(z.val.1, α z.val.2), ?_⟩, ?_⟩
  · change Finsler.SupportedSelfCut.distance n (z.val.1, α z.val.2) < 1
    exact z.property.trans_lt hr
  · fun_prop

def originalTester (hr : r < 1) :
    TopCat.of (CompactRotatedCutData.source α r) ⟶ TopCat.of (SphereLoop n) :=
  TopCat.ofHom ⟨fun z => left (originalCut α r hr z), continuous_left.comp (originalCut α r hr).continuous⟩

variable (hR : R ≤ 1 / 2) (hr : r < 1)

theorem evaluation_zero :
    stage α β R r 0 ≫ evaluation α β R r hR hr =
      projection α β R r ≫ originalEvaluation α r := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change (FirstInputRotatingCut.rotation α β R r hR hr (0, z)).val = _
  rw [FirstInputRotatingCut.rotation_zero, FirstInputRotatingCut.original_parameters]
  rfl

theorem tester_zero :
    stage α β R r 0 ≫ testedMap α β R r hR hr =
      projection α β R r ≫ originalTester α r hr := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change left (FirstInputRotatingCut.rotation α β R r hR hr (0, z)) = _
  rw [FirstInputRotatingCut.rotation_zero]
  congr 1

theorem thom_zero (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (stage α β R r 0) n (thom α β R r hR hr hn h) =
      cochainPullback (projection α β R r) n
        (cochainPullback (originalEvaluation α r) n (AnnularSelfCut.cocycle n hn h)) := by
  rw [thom, ← pullback_comp, evaluation_zero, pullback_comp]

theorem tested_zero (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (stage α β R r 0) p (tested α β R r hR hr p T) =
      cochainPullback (projection α β R r) p (cochainPullback (originalTester α r hr) p T) := by
  rw [tested, ← pullback_comp, tester_zero, pullback_comp]

theorem cap_zero_factor (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (p q : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    PartialDoubleCap.cap (TopCat.of (FirstInputRotatingCut.source α β R r)) n p q
      (cochainPullback (stage α β R r 0) n (thom α β R r hR hr hn h))
      (cochainPullback (stage α β R r 0) p (tested α β R r hR hr p T)) ≫
        (push (projection α β R r)).f q =
      (push (projection α β R r)).f (n + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (CompactRotatedCutData.source α r)) n p q
          (cochainPullback (originalEvaluation α r) n (AnnularSelfCut.cocycle n hn h))
          (cochainPullback (originalTester α r hr) p T) := by
  rw [thom_zero, tested_zero]
  exact PartialDoubleCap.cap_natural (projection α β R r) n p q _ _

end
end Finsler.FirstInputRotationOriginalFactors
