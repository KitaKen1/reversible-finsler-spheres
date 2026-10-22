module

public import Finsler.Topology.OriginalSecondHalfCompactHomology
import all Finsler.Topology.OriginalSecondHalfCompactHomology
public import Finsler.Topology.OriginalSecondHalfFullTensorHomology
import all Finsler.Topology.OriginalSecondHalfFullTensorHomology

/-! For actual compact input families, the genuine original second-input
tensor-time operation kills the required ordinary input homology cross
products. Both small input refinements are removed by actual homology
sections. The output remains in length < A-L+4 epsilon. The separate
comparison with the full product-time prism is still required. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfCompactFullTensorHomology

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open HomologicalComplex
open Finsler.OriginalSecondHalfUniformOperation
open Finsler.OriginalSecondHalfCompactTube
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors Finsler.SmallRectangleShuffle
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {s : ℕ}

theorem exists_uniform [CompactSpace P] [CompactSpace Q]
    (α : C(P, SphereLoop (s + 1))) (β : C(Q, SphereLoop (s + 1)))
    (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (s + 1)) (hn : 1 ≤ (s + 1))
    {δ ρ ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ R, ∃ hR : 0 < R, ∃ hR1 : R < 1, ∃ η, ∃ hη : 0 < η, η ≤ b ∧
    ∀ (ρJ : ℝ) (hρJ : 0 < ρJ), 2 * ρJ ≤ R →
    ∀ (a p : ℕ) (L A : ℝ)
      (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a),
      cochainCoboundary (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a J = 0 →
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q)))
        (NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) ρJ)) a J = 0 →
    ∀ (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (s + 1))) p),
      cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (s + 1))) p T = 0 →
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (s + 1)))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : P × Q, SobolevLength.length F (α z.1) + SobolevLength.length F (β z.2) < A) →
    ∃ C : DegreeLoweringHomology.Map
      (small (TopCat.of (P × (ClosedInterval × Q)))
        (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (leftCover α η ρJ) (rightCover β η ρJ)))
      (chains (TopCat.of (bounded α β (tube α β R) (near α β R hR1) r hr F (A - L + 4 * ε)))) (a + (s + 1) + p),
      ∃ hu : (∀ q, C.component q ≫ (push (source α β (tube α β R) (near α β R hR1) r hr F (A - L + 4 * ε))).f q =
        (inclusion (TopCat.of (P × (ClosedInterval × Q)))
          (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
            (leftCover α η ρJ) (rightCover β η ρJ))).f (a + (s + 1) + p + q) ≫
        threeCap (TopCat.of (P × (ClosedInterval × Q))) a (s + 1) p q J
          (SupportedSelfCutAdequacy.extension (tube α β R)
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (tube α β R) (near α β R hR1)) PUnit.unit (s + 1)
            (AnnularSelfCut.cocycle (s + 1) hn h))
          (SelfCutParameterFamily.testedExtension (tube α β R)
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (tube α β R) (near α β R hR1))
            (fun _ => r) (fun _ => hr) PUnit.unit p T)),
      ∀ (j k q : ℕ) (htotal : j + k = (a + s + p) + q), a + p < j →
        HomologicalComplex.homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q)) j k ((a + s + p) + q) htotal ≫
          (OriginalSecondHalfFullTensorHomology.unrefined α β (tube α β R) (near α β R hR1) r hr F (A - L + 4 * ε)
            (leftCover α η ρJ) (rightCover β η ρJ)
            (left_open α η ρJ) (left_covers α hη hρJ)
            (right_open β η ρJ) (right_covers β hη hρJ) h a p J T C hu).homology q = 0 := by
  obtain ⟨R, hR, hR1, η, hη, hηb, hconstruct⟩ := OriginalSecondHalfCompactHomology.exists_uniform
    α β r hr F hn h hρr hε hb hradius
  refine ⟨R, hR, hR1, η, hη, hηb, ?_⟩
  intro ρJ hρJ hρJR a p L A J hJ hJfar T hT hTshort hInput
  obtain ⟨C, hu, hzero⟩ := hconstruct ρJ hρJ hρJR a p L A J hJ hJfar T hT hTshort hInput
  refine ⟨C, hu, ?_⟩
  intro j k q htotal hdegree
  exact OriginalSecondHalfFullTensorHomology.homology_zero α β (tube α β R) (near α β R hR1) r hr F (A - L + 4 * ε)
            (leftCover α η ρJ) (rightCover β η ρJ)
            (left_open α η ρJ) (left_covers α hη hρJ)
            (right_open β η ρJ) (right_covers β hη hρJ) h a p J T C hu j k q htotal
    (hzero j k q htotal hdegree)

end
end Finsler.OriginalSecondHalfCompactFullTensorHomology
