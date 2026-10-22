module

public import Finsler.Topology.OriginalSecondHalfUniformOperation
public import Finsler.Topology.TensorTimePrismDegreeVanishing

/-! Apply the genuine constructed original bounded cap to the actual
second-input time prism. Its normalized retained output vanishes on
every required fixed bidegree, with one scale chosen before all tested
data. No component-zero or boundary-cover hypothesis is introduced. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfTensorVanishing

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

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}

theorem exists_uniform (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
    (K : Set (P × (ClosedInterval × Q)))
    (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
    (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (hcompact : IsCompact K) (hn : 1 ≤ n)
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
    ∀ (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0 →
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : K, SobolevLength.length F (OriginalSecondHalfFamily.family α β K hK z).2 < A) →
    ∃ C : DegreeLoweringHomology.Map
      (small (TopCat.of (P × (ClosedInterval × Q)))
        (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
          (leftCover α η ρJ) (rightCover β η ρJ)))
      (chains (TopCat.of (bounded α β K hK r hr F (A - L + 3 * ε)))) (a + n + p),
      (∀ q, C.component q ≫ (push (source α β K hK r hr F (A - L + 3 * ε))).f q =
        (inclusion (TopCat.of (P × (ClosedInterval × Q)))
          (rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
            (leftCover α η ρJ) (rightCover β η ρJ))).f (a + n + p + q) ≫
        threeCap (TopCat.of (P × (ClosedInterval × Q))) a n p q J
          (SupportedSelfCutAdequacy.extension K
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
            (AnnularSelfCut.cocycle n hn h))
          (SelfCutParameterFamily.testedExtension K
            (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
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
          C.component q ≫ (push (retained α β K hK r hr F (A - L + 3 * ε))).f q ≫
          (SingularNormalization.projector
            (TopCat.of ({γ | SobolevLength.length F γ < A - L + 3 * ε} : Set (SphereLoop n)))).f q = 0 := by
  obtain ⟨η, hη, hηb, hconstruct⟩ := OriginalSecondHalfUniformOperation.exists_uniform
    α β K hK r hr F hcompact hn h hρr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro ρJ hρJ hTube a p L A J hJ hJfar T hT hTshort hA
  obtain ⟨C, hsource, hvan⟩ := hconstruct ρJ hρJ hTube a p L A J hJ hJfar T hT hTshort hA
  refine ⟨C, hsource, ?_⟩
  intro j k q htotal hdegree
  exact TensorTimePrismDegreeVanishing.factorwise_zero
    (X := TopCat.of P) (Y := TopCat.of Q)
    (leftCover α η ρJ) (rightCover β η ρJ)
    (left_open α η ρJ) (left_covers α hη hρJ)
    (right_open β η ρJ) (right_covers β hη hρJ)
    j k (a + n + p + q) htotal
    (C.component q ≫ (push (retained α β K hK r hr F (A - L + 3 * ε))).f q ≫
      (SingularNormalization.projector
        (TopCat.of ({γ | SobolevLength.length F γ < A - L + 3 * ε} : Set (SphereLoop n)))).f q)
    (hvan j (k + 1) q (by omega) hdegree)

end
end Finsler.OriginalSecondHalfTensorVanishing
