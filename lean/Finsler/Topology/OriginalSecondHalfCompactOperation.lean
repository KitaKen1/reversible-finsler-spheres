module

public import Finsler.Topology.OriginalSecondHalfCompactTube
public import Finsler.Topology.OriginalSecondHalfTensorVanishing

/-! Supply the actual compact tube and joined-length data for the
original second-half operation. The tube radius and common factor scale
precede all cochains, degrees and thresholds. Input sum < A gives the
literal retained bound A-L+4 epsilon: one join loss plus three cut losses. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfCompactOperation

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

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}

theorem exists_uniform [CompactSpace P] [CompactSpace Q]
    (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
    (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (hn : 1 ≤ n)
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
    ∀ (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0 →
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : P × Q, SobolevLength.length F (α z.1) + SobolevLength.length F (β z.2) < A) →
    ∃ C : DegreeLoweringHomology.Map
      (small (TopCat.of (P × (ClosedInterval × Q)))
        (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (leftCover α η ρJ) (rightCover β η ρJ)))
      (chains (TopCat.of (bounded α β (tube α β R) (near α β R hR1) r hr F (A - L + 4 * ε)))) (a + n + p),
      (∀ q, C.component q ≫ (push (source α β (tube α β R) (near α β R hR1) r hr F (A - L + 4 * ε))).f q =
        (inclusion (TopCat.of (P × (ClosedInterval × Q)))
          (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
            (leftCover α η ρJ) (rightCover β η ρJ))).f (a + n + p + q) ≫
        threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
          (SupportedSelfCutAdequacy.extension (tube α β R)
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (tube α β R) (near α β R hR1)) PUnit.unit n
            (AnnularSelfCut.cocycle n hn h))
          (SelfCutParameterFamily.testedExtension (tube α β R)
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β (tube α β R) (near α β R hR1))
            (fun _ => r) (fun _ => hr) PUnit.unit p T)) ∧
      ∀ (j k q : ℕ) (htotal : j + k + 1 = a + n + p + q), a + p < j →
        ιTensorObj (small (TopCat.of P) (leftCover α η ρJ))
          (small (TopCat.of Q) (CommonPrismRefinement.endpointCover (TopCat.of Q)
            (rightCover β η ρJ))) j k (j + k) rfl ≫
          (TensorTimePrismComparison.prism (X := TopCat.of P) (Y := TopCat.of Q)
            (leftCover α η ρJ) (rightCover β η ρJ)).hom (j + k) (j + k + 1) ≫
          (FactorwiseSubdivisionComparison.factorwise
            (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
            (leftCover α η ρJ) (rightCover β η ρJ)
            (left_open α η ρJ) (left_covers α hη hρJ)
            (right_open β η ρJ) (right_covers β hη hρJ)).f (j + k + 1) ≫
          eqToHom (congrArg (small (TopCat.of (P × (ClosedInterval × Q)))
            (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
              (leftCover α η ρJ) (rightCover β η ρJ))).X htotal) ≫
          C.component q ≫ (push (retained α β (tube α β R) (near α β R hR1) r hr F (A - L + 4 * ε))).f q ≫
          (SingularNormalization.projector
            (TopCat.of ({γ | SobolevLength.length F γ < A - L + 4 * ε} : Set (SphereLoop n)))).f q = 0 := by
  obtain ⟨R, hR, hR1, hlength⟩ := OriginalSecondHalfCompactTube.exists_length_tube F α β hε
  obtain ⟨η, hη, hηb, hconstruct⟩ := OriginalSecondHalfTensorVanishing.exists_uniform
    α β (tube α β R) (near α β R hR1) r hr F (compact α β R) hn h hρr hε hb hradius
  refine ⟨R, hR, hR1, η, hη, hηb, ?_⟩
  intro ρJ hρJ hρJR a p L A J hJ hJfar T hT hTshort hInput
  have hA : ∀ z : tube α β R,
      SobolevLength.length F (OriginalSecondHalfFamily.family α β (tube α β R)
        (near α β R hR1) z).2 < A + ε := by
    intro z
    have hi := hInput (z.val.1, z.val.2.2)
    have hl := hlength z
    linarith
  have hthreshold : (A + ε) - L + 3 * ε = A - L + 4 * ε := by ring
  rw [← hthreshold]
  exact hconstruct ρJ hρJ
    (contains_near α β hρJR) a p L (A + ε) J hJ hJfar T hT hTshort hA

end
end Finsler.OriginalSecondHalfCompactOperation
