module

public import Finsler.Topology.JoinedLocalizedFiltered
public import Finsler.Topology.AnnularDoubleCap

/-! The original AnnularCutComparison.cut itself, applied to the actual
three joined-loop families on one common adequate rectangle refinement,
has closed linear components in the genuine retained length sublevel.
The actual strict retraction cancels on these already small chains.
Comparison with unsubdivided time prisms remains separate. -/

@[expose] public section
namespace Finsler.JoinedAnnularFiltered

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem exists_closed_filtered_output {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (u : C(X, H1JoinContinuity.composable (m + 1)))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∀ (i : Fin 3) (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      ∃ d : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X
          ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).X q,
      ∀ q,
        (d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).f q =
          (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f ((m + 1) + (p + q)) ≫
          (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
          AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q) ∧
        (d (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q =
          (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
            ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d q) := by
  have hρ : 0 < ρ := h.1.trans h.2.2
  have hρr' : ρ < r := by linarith
  obtain ⟨η, hη, hηb, hW, hop⟩ := JoinedLocalizedFiltered.exists_closed_filtered_output F u a ha ha1
    hρ hρr hr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro i p L A T hT hshort hA
  obtain ⟨d, hid⟩ := hop i (m + 1) p L A
    (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSelfCut.cocycle_closed (m + 1) (by omega) h)
    (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) T hT hshort hA
  refine ⟨d, ?_⟩
  intro q
  refine ⟨?_, (hid q).2⟩
  rw [(hid q).1]
  exact (AnnularDoubleCap.canonical_cut_on_small m p h hρr' hr T
    (JoinedFilteredCap.rectangleCover X η) (JoinedFamilyNaturality.globalMap u a ha ha1 i)
    (JoinedLocalizedCutComparison.familySmallMap u a ha ha1 ρ r i
      (JoinedFilteredCap.rectangleCover X η) (hW i))
    (JoinedLocalizedCutComparison.familySmallMap_inclusion u a ha ha1 ρ r i
      (JoinedFilteredCap.rectangleCover X η) (hW i)) hT q).symm

end
end Finsler.JoinedAnnularFiltered
