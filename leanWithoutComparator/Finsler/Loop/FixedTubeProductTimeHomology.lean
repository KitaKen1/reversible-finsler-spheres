module

public import Finsler.Topology.OriginalSecondHalfTensorVanishing
public import Finsler.Topology.OriginalSecondHalfFullTensorHomology
import all Finsler.Topology.OriginalSecondHalfTensorHomology
import all Finsler.Topology.OriginalSecondHalfFullTensorHomology
public import Finsler.Topology.OriginalSecondHalfTimeModelComparison
import all Finsler.Topology.OriginalSecondHalfTimeModelComparison

/-! Choose the old factor scale on a specified compact near tube.
The tube is not chosen again. The genuine full product-time operation
kills the required ordinary bidegrees in the same bounded length target. -/

@[expose] public section
namespace Finsler.FixedTubeProductTimeHomology

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open HomologicalComplex
open Finsler.OriginalSecondHalfUniformOperation
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

theorem exists_uniform
    (α : C(P, SphereLoop (s + 1))) (β : C(Q, SphereLoop (s + 1)))
    (K : Set (P × (ClosedInterval × Q)))
    (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
    (hcompact : IsCompact K)
    (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (s + 1)) (hn : 1 ≤ (s + 1))
    {δ ρ ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η, ∃ hη : 0 < η, η ≤ b ∧
    ∀ (ρJ : ℝ) (hρJ : 0 < ρJ),
      (∀ z : P × (ClosedInterval × Q),
        dist (basepoint (α z.1)) (basepoint (β z.2.2)) < 2 * ρJ → z ∈ K) →
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
      (∀ z : K, SobolevLength.length F (OriginalSecondHalfFamily.family α β K hK z).2 < A) →
    ∃ C : DegreeLoweringHomology.Map
      (small (TopCat.of (P × (ClosedInterval × Q)))
        (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (leftCover α η ρJ) (rightCover β η ρJ)))
      (chains (TopCat.of (bounded α β K hK r hr F (A - L + 3 * ε)))) (a + (s + 1) + p),
      ∃ hu : (∀ q, C.component q ≫ (push (source α β K hK r hr F (A - L + 3 * ε))).f q =
        (inclusion (TopCat.of (P × (ClosedInterval × Q)))
          (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
            (leftCover α η ρJ) (rightCover β η ρJ))).f (a + (s + 1) + p + q) ≫
        threeCap (TopCat.of (P × (ClosedInterval × Q))) a (s + 1) p q J
          (SupportedSelfCutAdequacy.extension K
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit (s + 1)
            (AnnularSelfCut.cocycle (s + 1) hn h))
          (SelfCutParameterFamily.testedExtension K
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
            (fun _ => r) (fun _ => hr) PUnit.unit p T)),
      ∀ (j k q : ℕ) (htotal : j + k = (a + s + p) + q), a + p < j →
        HomologicalComplex.homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q)) j k ((a + s + p) + q) htotal ≫
          (OriginalSecondHalfTimeModelComparison.productOutput α β K hK r hr F (A - L + 3 * ε)
            (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
              (leftCover α η ρJ) (rightCover β η ρJ))
            (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
              (leftCover α η ρJ) (rightCover β η ρJ) (left_open α η ρJ) (right_open β η ρJ))
            (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
              (leftCover α η ρJ) (rightCover β η ρJ) (left_covers α hη hρJ) (right_covers β hη hρJ)) h a p J T C hu).homology q = 0 := by
  obtain ⟨η, hη, hηb, hconstruct⟩ := OriginalSecondHalfTensorVanishing.exists_uniform
    α β K hK r hr F hcompact hn h hρr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro ρJ hρJ hTube a p L A J hJ hJfar T hT hTshort hA
  obtain ⟨C, hu, hvan⟩ := hconstruct ρJ hρJ hTube a p L A J hJ hJfar T hT hTshort hA
  refine ⟨C, hu, ?_⟩
  intro j k q htotal hdegree
  rw [OriginalSecondHalfTimeModelComparison.homology_eq α β K hK r hr F (A - L + 3 * ε)
    (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
      (leftCover α η ρJ) (rightCover β η ρJ))
    (FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
      (leftCover α η ρJ) (rightCover β η ρJ) (left_open α η ρJ) (right_open β η ρJ))
    (FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
      (leftCover α η ρJ) (rightCover β η ρJ) (left_covers α hη hρJ) (right_covers β hη hρJ)) h a p J T C hu q]
  exact OriginalSecondHalfFullTensorHomology.homology_zero α β K hK r hr F (A - L + 3 * ε)
    (leftCover α η ρJ) (rightCover β η ρJ)
    (left_open α η ρJ) (left_covers α hη hρJ)
    (right_open β η ρJ) (right_covers β hη hρJ) h a p J T C hu j k q htotal
    (OriginalSecondHalfTensorHomology.homology_zero α β K hK r hr F (A - L + 3 * ε)
      (leftCover α η ρJ) (rightCover β η ρJ)
      (left_open α η ρJ) (left_covers α hη hρJ)
      (right_open β η ρJ) (right_covers β hη hρJ) h a p J T C hu hvan j k q htotal hdegree)

end
end Finsler.FixedTubeProductTimeHomology
