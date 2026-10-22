module

public import Finsler.Topology.JointFactorCover
public import Finsler.Topology.OriginalSecondHalfGlobalOperation
public import Finsler.Topology.OriginalSecondHalfBidegreeZero
public import Finsler.Topology.PartialJoinRectangleRefinement

/-! One actual open/full pair of factor covers simultaneously supplies
the original second-half global bounded operation, its local boundary
cover, and normalized zero on every required cross-product bidegree.
The common scale is chosen before all cochains, degrees and length
thresholds. No boundary cover or bounded lift is postulated. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfUniformOperation

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open HomologicalComplex
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

def leftCover (α : C(P, SphereLoop n)) (η ρJ : ℝ) : P → Set P :=
  JointFactorCover.cover (fun x => basepoint (α x)) η ρJ

def rightCover (β : C(Q, SphereLoop n)) (η ρJ : ℝ) :
    (ClosedInterval × Q) → Set (ClosedInterval × Q) :=
  JointFactorCover.cover (fun y : ClosedInterval × Q => basepoint (β y.2)) η ρJ

theorem left_open (α : C(P, SphereLoop n)) (η ρJ : ℝ) (x : P) :
    IsOpen (leftCover α η ρJ x) :=
  JointFactorCover.isOpen _ (H1AlignmentHomotopy.basepoint_continuous.comp α.continuous) η ρJ x

theorem right_open (β : C(Q, SphereLoop n)) (η ρJ : ℝ) (y : ClosedInterval × Q) :
    IsOpen (rightCover β η ρJ y) :=
  JointFactorCover.isOpen _ ((H1AlignmentHomotopy.basepoint_continuous.comp β.continuous).comp continuous_snd) η ρJ y

theorem left_covers (α : C(P, SphereLoop n)) {η ρJ : ℝ} (hη : 0 < η) (hρJ : 0 < ρJ) :
    ⋃ x, leftCover α η ρJ x = Set.univ :=
  JointFactorCover.covers _ hη hρJ

theorem right_covers (β : C(Q, SphereLoop n)) {η ρJ : ℝ} (hη : 0 < η) (hρJ : 0 < ρJ) :
    ⋃ y, rightCover β η ρJ y = Set.univ :=
  JointFactorCover.covers _ hη hρJ

theorem exists_uniform (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
    (K : Set (P × (ClosedInterval × Q)))
    (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
    (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (hcompact : IsCompact K) (hn : 1 ≤ n)
    {δ ρ ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
    ∀ (ρJ : ℝ), 0 < ρJ →
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
      ∀ (j k q : ℕ) (htotal : j + k = a + n + p + q), a + p < j →
        ιTensorObj (small (TopCat.of P) (leftCover α η ρJ))
          (small (TopCat.of (ClosedInterval × Q)) (rightCover β η ρJ))
          j k (a + n + p + q) htotal ≫
          (SmallRectangleCross.cross (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
            (leftCover α η ρJ) (rightCover β η ρJ)).f (a + n + p + q) ≫ C.component q ≫
          (push (retained α β K hK r hr F (A - L + 3 * ε))).f q ≫
          (SingularNormalization.projector
            (TopCat.of ({γ | SobolevLength.length F γ < A - L + 3 * ε} : Set (SphereLoop n)))).f q = 0 := by
  obtain ⟨ηa, hηa, hηab, had⟩ := OriginalSecondHalfGlobalOperation.exists_scale
    α β K hK r hr F hn h hcompact hρr hε hb hradius
  obtain ⟨ηv, hηv, hηva, hvan⟩ := OriginalSecondHalfBidegreeZero.exists_scale
    α β K hK r hr F hcompact hn h hρr hε hηa hradius
  have hρ : 0 < ρ := h.1.trans h.2.2
  obtain ⟨η, hη, hηv, href⟩ := PartialJoinRectangleRefinement.exists_scale K hcompact
    (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
    (fun _ => r) (fun _ => ρ) (fun _ => hρ) (fun _ => by linarith) hηv
  refine ⟨η, hη, hηv.trans (hηva.trans hηab), ?_⟩
  intro ρJ hρJ hTube a p L A J hJ hJfar T hT hTshort hA
  let U := leftCover α η ρJ
  let V := rightCover β η ρJ
  let W := rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q)) U V
  let far := NearFarCapComparison.far (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
    (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) ρJ
  have hUa : ∀ x, U x ⊆ PairDistanceCover.cover id ηa x :=
    fun _ _ hz => hz.1.trans_le (hηv.trans hηva)
  have hVa : ∀ y, V y ⊆ PairDistanceCover.cover id ηa y :=
    fun _ _ hz => hz.1.trans_le (hηv.trans hηva)
  have hUJ : ∀ x, U x ⊆ PairDistanceCover.cover (fun x => basepoint (α x)) (ρJ / 4) x :=
    fun _ _ hz => hz.2
  have hVJ : ∀ y, V y ⊆ PairDistanceCover.cover
      (fun y : ClosedInterval × Q => basepoint (β y.2)) (ρJ / 4) y := fun _ _ hz => hz.2
  have hgood : OriginalSecondHalfGlobalOperation.adequate α β K hK r hr F hn h W a p J T
      (A - L + 3 * ε) :=
    had W Prod.fst Prod.snd (fun v _ hz => ⟨hUa v.1 hz.1, hVa v.2 hz.2⟩)
      ρJ (fun v _ hz => ⟨hUJ v.1 hz.1, hVJ v.2 hz.2⟩) hTube a p L A J hJfar T hTshort hA
  have hW : ∀ v, W v ⊆ far ∨
      W v ⊆ {z | ρ < SelfCutParameterFamily.distanceValue K
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit z} ∨
      W v ⊆ OriginalSecondHalfFamily.domain α β K hK r := by
    intro v
    exact href PUnit.unit v.1 v.2 (W v) (fun _ hz => ⟨hz.1.1, hz.2.1⟩)
      (fun x => basepoint (α x)) (fun y : ClosedInterval × Q => basepoint (β y.2)) ρJ
      (fun _ hz => ⟨hz.1.2, hz.2.2⟩) hTube
  let C := OriginalSecondHalfGlobalOperation.operation α β K hK r hr F hn h W
    (A - L + 3 * ε) a p J T hgood hJ hT far hJfar hW
  have hsource := OriginalSecondHalfGlobalOperation.source_inclusion α β K hK r hr F hn h W
    (A - L + 3 * ε) a p J T hgood hJ hT far hJfar hW
  refine ⟨C, hsource, ?_⟩
  intro j k q htotal hdegree
  exact hvan U V id id (fun _ _ hz => hz.1.trans_le hηv) (fun _ _ hz => hz.1.trans_le hηv)
    ρJ hUJ hVJ hTube a p L A J hJfar T hTshort hA C hsource j k q htotal hdegree

end
end Finsler.OriginalSecondHalfUniformOperation
