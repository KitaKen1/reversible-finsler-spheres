module

public import Finsler.Loop.FirstInputRotatingFixedOutput
public import Finsler.Loop.FixedOutputSupportedAdequacy
public import Finsler.Loop.FirstInputRotationCochains

/-! Supply the actual partial-rotation tester and fixed output to
whole-parent filtering. All radii and rectangle scales precede every
tested degree, cochain and threshold; arbitrary tested faces are allowed. -/

@[expose] public section
namespace Finsler.FirstInputRotationSupportedAdequacy

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.CompactH1Alignment Finsler.H1SelfCutNeighborhood Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ)

attribute [local instance] FirstInputRotationAdequacy.source_compactSpace

open Finsler.FirstInputRotationAdequacy

theorem exists_uniform_scale [CompactSpace P] [CompactSpace Q] (hr : r < 1) (F : ReversibleMetric n)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ ρ > 0, ρ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < ρ →
      ∃ η > 0, η ≤ b ∧
      ∀ (cx : _root_.unitInterval) (cy : FirstInputRotatingCut.source α β R r)
        (S : Set (_root_.unitInterval × FirstInputRotatingCut.source α β R r)),
      S ⊆ PairDistanceCover.cover id η cx ×ˢ PairDistanceCover.cover id η cy →
      ∀ (p : ℕ) (L A : ℝ)
      (ξ : singularCochainGroup (ZMod 2) (FirstInputRotationCochains.space α β R r) p),
      cochainPullback (SupportedCap.subspaceMap (FirstInputRotationCochains.space α β R r)
        {z | SobolevLength.length F (tested α β R r hR hr z) < L}) p ξ = 0 →
      (∀ z ∈ S, budget α β R r F z < A) →
      ∀ (τ : TopCat.toSSet.obj (TopCat.of (_root_.unitInterval × FirstInputRotatingCut.source α β R r)) _⦋p⦌),
      Set.range ((TopCat.of (_root_.unitInterval × FirstInputRotatingCut.source α β R r)).toSSetObjEquiv _ τ) ⊆ S →
      (TopCat.toSSet.obj (TopCat.of (_root_.unitInterval × FirstInputRotatingCut.source α β R r))).ιChainComplex τ ≫
        ξ ≠ 0 →
      ∀ z ∈ S, SobolevLength.length F (output α β R r hR hr z) < A - L + 5 * ε := by
  obtain ⟨ρ, hρ, hρ1, hbound⟩ := FirstInputRotatingFixedOutput.exists_sum_bound α β r hr F hε hradius
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro R hR hRρ
  obtain ⟨η, hη, hηb, had⟩ := FixedOutputSupportedAdequacy.exists_scale F
    (tested α β R r hR hr) (output α β R r hR hr) (budget α β R r F) (4 * ε)
    (fun z => hbound R hR hRρ z.1 z.2) hε hb
  refine ⟨η, hη, hηb, ?_⟩
  intro cx cy S hrect p L A ξ hshort hA τ hτS hτ z hz
  have hout := had cx cy S hrect p L A ξ hshort hA τ hτS hτ z hz
  linarith

end
end Finsler.FirstInputRotationSupportedAdequacy
