module

public import Finsler.Loop.FirstInputRotatingFixedOutput
public import Finsler.Loop.FixedOutputTestedAdequacy

/-! Supply the actual partial-rotation tester and fixed output to
whole-parent filtering. All radii and rectangle scales precede every
tested degree, cochain and threshold; arbitrary tested faces are allowed. -/

@[expose] public section
namespace Finsler.FirstInputRotationAdequacy

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

theorem source_compactSpace [CompactSpace P] [CompactSpace Q] : CompactSpace (FirstInputRotatingCut.source α β R r) := by
  letI : CompactSpace (CompactNearJoinParameters.tube α β R) :=
    isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)
  apply isCompact_iff_compactSpace.mp
  apply IsClosed.isCompact
  have hf : Continuous (fun z : ClosedInterval × CompactNearJoinParameters.tube α β R => α z.2.val.1) := by fun_prop
  exact isClosed_le ((continuous_distance n).comp (continuous_fst.prodMk hf)) continuous_const

attribute [local instance] source_compactSpace

def tested (hR : R ≤ 1 / 2) (hr : r < 1) :
    C(_root_.unitInterval × FirstInputRotatingCut.source α β R r, SphereLoop n) :=
  ⟨fun z => left (FirstInputRotatingCut.rotation α β R r hR hr z),
    continuous_left.comp (FirstInputRotatingCut.rotation α β R r hR hr).continuous⟩

def output (hR : R ≤ 1 / 2) (hr : r < 1) :
    C(_root_.unitInterval × FirstInputRotatingCut.source α β R r, SphereLoop n) :=
  (FirstInputRotatingFixedOutput.output α β R r hR hr).comp ⟨Prod.snd, continuous_snd⟩

def budget (F : ReversibleMetric n) (z : _root_.unitInterval × FirstInputRotatingCut.source α β R r) : ℝ :=
  SobolevLength.length F (α z.2.val.2.val.1) + SobolevLength.length F (β z.2.val.2.val.2)

theorem exists_uniform_scale [CompactSpace P] [CompactSpace Q] (hr : r < 1) (F : ReversibleMetric n)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ ρ > 0, ρ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < ρ →
      ∃ η > 0, η ≤ b ∧
      ∀ (cx : _root_.unitInterval) (cy : FirstInputRotatingCut.source α β R r)
        (S : Set (_root_.unitInterval × FirstInputRotatingCut.source α β R r)),
      S ⊆ PairDistanceCover.cover id η cx ×ˢ PairDistanceCover.cover id η cy →
      ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z ∈ S, budget α β R r F z < A) →
      ∀ (τ : TopCat.toSSet.obj (TopCat.of (_root_.unitInterval × FirstInputRotatingCut.source α β R r)) _⦋p⦌),
      Set.range ((TopCat.of (_root_.unitInterval × FirstInputRotatingCut.source α β R r)).toSSetObjEquiv _ τ) ⊆ S →
      (TopCat.toSSet.obj (TopCat.of (_root_.unitInterval × FirstInputRotatingCut.source α β R r))).ιChainComplex τ ≫
        cochainPullback (TopCat.ofHom (tested α β R r hR hr)) p T ≠ 0 →
      ∀ z ∈ S, SobolevLength.length F (output α β R r hR hr z) < A - L + 5 * ε := by
  obtain ⟨ρ, hρ, hρ1, hbound⟩ := FirstInputRotatingFixedOutput.exists_sum_bound α β r hr F hε hradius
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro R hR hRρ
  obtain ⟨η, hη, hηb, had⟩ := FixedOutputTestedAdequacy.exists_scale F
    (tested α β R r hR hr) (output α β R r hR hr) (budget α β R r F) (4 * ε)
    (fun z => hbound R hR hRρ z.1 z.2) hε hb
  refine ⟨η, hη, hηb, ?_⟩
  intro cx cy S hrect p L A T hshort hA τ hτS hτ z hz
  have hout := had cx cy S hrect p L A T hshort hA τ hτS hτ z hz
  linarith

end
end Finsler.FirstInputRotationAdequacy
