module

public import Finsler.Topology.FirstHalfRefinedTimeAgreement
public import Finsler.Loop.FullSecondHalfCompactTimeOperation
public import Finsler.Topology.JoinedNativeTimePackage
public import Finsler.Loop.FirstInputRotationNativeTimeComparison
import all Finsler.Loop.FirstInputRotationNativeTimeComparison

/-! Accept a supplied actual interior collar, then choose both
genuine cap scales before tested data. Their minimum refines only the source. Replace the
first term in the actual filtered full-time split by the original
first-half cap followed by its length-preserving retained deformation.
The original full and both native interior time images are retained. -/

@[expose] public section
namespace Finsler.JoinedRotationFilteredSplit

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.JoinedCommonInputRefinement Finsler.JoinedSimultaneousPrisms Finsler.JoinedSmallCapExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

theorem exists_uniform_on_collar {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ) (hR : R ≤ 1 / 2)
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r < 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    (ζ : ℝ) (hζ : 0 < ζ)
    (hrot₀ : ∀ s x, FirstInputRotationTimeTrim.sideHomotopy α β R a ha ha1 0 (s, x) ∈
      FirstInputRotationCutCylinder.collar α β R δ)
    (hrot₁ : ∀ s x, FirstInputRotationTimeTrim.sideHomotopy α β R a ha ha1 1 (s, x) ∈
      FirstInputRotationCutCylinder.collar α β R δ)
    (hlength : ∀ z : CompactNearJoinParameters.tube α β R,
      length F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z).val.1 +
      length F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z).val.2 <
        length F (α z.val.1) + length F (β z.val.2) + ε)
    (hadequate : ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ z : CompactNearJoinParameters.tube α β R, length F (α z.val.1) + length F (β z.val.2) < A) →
      FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) ζ p T)
    (hside₀ : ∀ (i : Fin 2) (s : ClosedInterval) (x : (CompactNearJoinParameters.tube α β R)),
      distance (m + 1) (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i.succ ((s, 0), x)) ≤ δ)
    (hside₁ : ∀ (i : Fin 2) (s : ClosedInterval) (x : (CompactNearJoinParameters.tube α β R)),
      distance (m + 1) (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i.succ ((s, 1), x)) ≤ δ) :
    ∃ (hFirst₀ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le (0, x)) ≤ δ)
      (hFirst₁ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le (1, x)) ≤ δ)
      (hSecond₀ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le (0, x)) ≤ δ)
      (hSecond₁ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le (1, x)) ≤ δ),
    ∃ (η₀ : ℝ) (hη₀ : 0 < η₀), η₀ ≤ b ∧
    ∃ (η₁ : ℝ) (hη₁ : 0 < η₁), η₁ ≤ b ∧
    ∃ hW₁ : ∀ center,
      JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₁ center ⊆ JoinedRectangleRefinement.far (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1 ∨
      JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₁ center ⊆ domain (tube (CompactNearJoinParameters.tube α β R)) (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le) (fun _ => r) 1,
    let η := min η₀ η₁
    let hη : 0 < η := lt_min hη₀ hη₁
    ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
    (∀ z : CompactNearJoinParameters.tube α β R, length F (α z.val.1) + length F (β z.val.2) < A) →
    ∃ hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) ζ p T,
    let B := A - L + 5 * ε
    ∃ (d : Fin 3 → ∀ q, (small (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)).X
        ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q)
      (c : ∀ q, (small (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η₁)).X
        ((m + 1) + (p + q)) ⟶ (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B)).X q)
      (f k : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R))) (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p))
      (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
        (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B)) (m + p)),
    (∀ i q, d i q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)).f ((m + 1) + (p + q)) ≫
        (push (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
              AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr.le T hT q) ∧
    (∀ i q, d i (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q =
      (small (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d i q) ∧
    (∀ q, c q ≫ (push (FirstHalfAnnularTimeInputs.projection (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B)).f q =
      (inclusion (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η₁)).f ((m + 1) + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (m + 1) p q
          (FirstHalfAnnularTimeDomain.thom (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 (by omega) h) (FirstHalfAnnularTimeDomain.tested (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le p T)) ∧
    (∀ q, c (q + 1) ≫ (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B)).d (q + 1) q =
      (small (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η₁)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q) ∧
    (∀ q, f.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
      (push (maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 0)).f ((m + p) + q + 1) ≫
        cap (CompactNearJoinParameters.tube α β R) η₀ hη₀ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) (ClosedCapDegreeTransport.align m p (d 0)) q) ∧
    (∀ q, k.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
      (push (maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 4)).f ((m + p) + q + 1) ≫
        cap (CompactNearJoinParameters.tube α β R) η₀ hη₀ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) (ClosedCapDegreeTransport.align m p (d 2)) q) ∧
    (∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
      ClosedCapDegreeTransport.align m p
        (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
          (FirstHalfAnnularTimeInputs.faceCover_open (CompactNearJoinParameters.tube α β R) η) (FirstHalfAnnularTimeInputs.faceCover_univ (CompactNearJoinParameters.tube α β R) η hη)
          (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B)) m p
          (NestedCapRefinement.pre (m + 1) p (FirstHalfFaceRefinement.map (CompactNearJoinParameters.tube α β R) (min_le_right η₀ η₁)) c)) q) ∧
    (∀ q, f.homology q =
      (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F B ζ hζ
        (by linarith [h.1.trans h.2.2]) hgood hT 0).homology q + k.homology q) ∧
    (∀ q, f.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))) q =
      ((AnnularCutComparison.operation m p h (by linarith [h.1.trans h.2.2]) hr.le T hT).pre
        (push (TopCat.ofHom (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))))))).homology q) ∧
    (∀ q, (w.post (push (FirstHalfBoundedCapDeformation.endpoint (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B 1))).homology q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (JoinedFilteredCap.sublevel F B))) q =
      (AnnularTrimHomology.operation m p h (by linarith [h.1.trans h.2.2]) hr.le T hT
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le) hFirst₀ hFirst₁).homology q) ∧
    (∀ q, k.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))) q =
      (AnnularTrimHomology.operation m p h (by linarith [h.1.trans h.2.2]) hr.le T hT
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le) hSecond₀ hSecond₁).homology q) := by
  classical
  have hρr' : ρ < r := by linarith [h.1.trans h.2.2]
  obtain ⟨hFirst₀, hFirst₁, hSecond₀, hSecond₁⟩ := JoinedNativeTimeModels.trimmed_endpoints (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le δ hside₀ hside₁
  obtain ⟨η₀, hη₀, hη₀b, hop₀⟩ := JoinedAnnularFiltered.exists_closed_filtered_output m F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le
    h hρr hr.le hε hb hradius
  obtain ⟨η₁, hη₁, hη₁b, hW₁, hop₁⟩ := FirstHalfAnnularTimeDomain.exists_native_time_domain m F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1
    h hρr hr.le hFirst₀ hFirst₁ hε hb hradius
  refine ⟨hFirst₀, hFirst₁, hSecond₀, hSecond₁, η₀, hη₀, hη₀b, η₁, hη₁, hη₁b, hW₁, ?_⟩
  dsimp only
  intro p L A T hT hshort hA
  let η := min η₀ η₁
  have hη : 0 < η := lt_min hη₀ hη₁
  let B := A - L + 5 * ε
  let Z := chains (TopCat.of (JoinedFilteredCap.sublevel F B))
  let hgoodActual := hadequate p L A T hshort hA
  have hA' : ∀ z : CompactNearJoinParameters.tube α β R,
      length F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z).val.1 +
      length F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)) z).val.2 < A + 2 * ε := by
    intro z
    have hl := hlength z
    have hAz := hA z
    linarith
  have hbudget : (A + 2 * ε) - L + 3 * ε = A - L + 5 * ε := by ring
  have houter := fun i : Fin 3 => hop₀ i p L (A + 2 * ε) T hT hshort hA'
  rw [hbudget] at houter
  choose d hd using houter
  have hnative := hop₁ p L (A + 2 * ε) T hT hshort hA'
  dsimp only at hnative
  rw [hbudget] at hnative
  obtain ⟨c, hc, w₁, hiC, hw₁, hnC, hew₁, hbw₁⟩ := hnative
  let v : Fin 3 → ∀ q, (small (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)).X
      ((m + p) + q + 1) ⟶ Z.X q := fun i => ClosedCapDegreeTransport.align m p (d i)
  have hvc (i : Fin 3) (q : ℕ) : v i (q + 1) ≫ Z.d (q + 1) q =
      (small (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)).d
        ((m + p) + q + 2) ((m + p) + q + 1) ≫ v i q :=
    ClosedCapDegreeTransport.align_comm m p (d i) (fun q => (hd i q).2) q
  have hvi (i : Fin 3) (q : ℕ) : v i q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)).f ((m + p) + q + 1) ≫
        (push (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i)).f ((m + p) + q + 1) ≫
          AnnularCutComparison.cut m p h hρr' hr.le T hT q := by
    simpa only [HomologicalComplex.comp_f, Category.assoc] using ClosedCapDegreeTransport.align_inclusion m p (d i)
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B)))
      (inclusion (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀) ≫ push (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i))
      (fun q => AnnularCutComparison.cut m p h hρr' hr.le T hT q)
      (fun q => by simpa only [HomologicalComplex.comp_f, Category.assoc] using (hd i q).1) q
  obtain ⟨f, g, k, hf, hg, hk, hsplit⟩ := JoinedFilteredHomologySplit.homology_split m p h hρr' hr.le T hT
    (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le η₀ hη₀ (JoinedFilteredCap.sublevel F B) v hvi hvc hside₀ hside₁
  have hmap₄ : maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 4 = planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1 := rfl
  have hRet : JoinedSimultaneousPrisms.retraction (CompactNearJoinParameters.tube α β R) η₀ hη₀ =
      TauCeti.smallSingularRetraction (X := TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) coeff (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)
        (rectangles_open (CompactNearJoinParameters.tube α β R) η₀) (rectangles_univ (CompactNearJoinParameters.tube α β R) η₀ hη₀) := rfl
  have hg' (q : ℕ) : g.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
      (push (planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1) ≫ TauCeti.smallSingularRetraction (X := TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) coeff
        (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀) (rectangles_open (CompactNearJoinParameters.tube α β R) η₀)
          (rectangles_univ (CompactNearJoinParameters.tube α β R) η₀ (hη.trans_le (min_le_left η₀ η₁)))).f ((m + p) + q + 1) ≫
            ClosedCapDegreeTransport.align m p (d 1) q := by
    simpa only [hmap₄, cap, hRet, HomologicalComplex.comp_f, Category.assoc, v] using hg q
  obtain ⟨w, hw, heRet, heDef⟩ := FirstHalfRefinedTimeAgreement.exists_operation_and_eq m p h hρr' hr.le T hT F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1
    η η₀ η₁ B hη (min_le_left η₀ η₁) (min_le_right η₀ η₁) hFirst₀ hFirst₁ hW₁ c hc hiC hnC
    (d 1) (fun q => (hd 1 q).1) (fun q => (hd 1 q).2) g hg'
  let D : Fin 3 → ∀ q, (chains (TopCat.of (Outer (CompactNearJoinParameters.tube α β R)))).X ((m + p) + q + 1) ⟶ Z.X q :=
    fun i => cap (CompactNearJoinParameters.tube α β R) η₀ hη₀ Z (m + p) (v i)
  have hDi (i : Fin 3) (q : ℕ) : D i q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (TauCeti.singularSmallApprox (X := TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) coeff (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)).f ((m + p) + q + 1) ≫
        (push (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i)).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr' hr.le T hT q :=
    cap_inclusion (P := parameters (m + 1)) (L := TopCat.of (SphereLoop (m + 1))) (CompactNearJoinParameters.tube α β R) η₀ hη₀ (m + p)
      (JoinedFilteredCap.sublevel F B) (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le i)
      (fun q => AnnularCutComparison.cut m p h hρr' hr.le T hT q) (v i) (hvi i) q
  have hFull₀ (x : (CompactNearJoinParameters.tube α β R)) : distance (m + 1) (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 0 (maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 0 (0, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) (0, x) ≤ δ
    rw [UniformSelfCutCollar.distance_zero]
    exact h.1.le
  have hFull₁ (x : (CompactNearJoinParameters.tube α β R)) : distance (m + 1) (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 0 (maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 0 (1, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) (1, x) ≤ δ
    rw [UniformSelfCutCollar.distance_one]
    exact h.1.le
  have hgNative (q : ℕ) : g.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))) q =
      (AnnularTrimHomology.operation m p h hρr' hr.le T hT
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le) hFirst₀ hFirst₁).homology q := by
    apply FilteredModelNativeComparison.identified_inclusion m p h hρr' hr.le T hT
      (TopCat.of (CompactNearJoinParameters.tube α β R)) (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)
      (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 1) (maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 4)
      (fun x => hside₀ 0 1 x) (fun x => hside₁ 0 1 x) (JoinedFilteredCap.sublevel F B) (D 1) (hDi 1) g hg
      _ ?_ hFirst₀ hFirst₁ q
    change planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1 ≫ JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 1 = _
    exact JoinedEndpointMaps.first_end (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le
  refine ⟨hgoodActual, d, c, f, k, w, (fun i q => (hd i q).1), (fun i q => (hd i q).2), hiC, hc, hf, hk, hw, ?_, ?_, ?_, ?_⟩
  · intro q
    let cf := NestedCapRefinement.pre (m + 1) p
      (FirstHalfFaceRefinement.map (CompactNearJoinParameters.tube α β R) (min_le_right η₀ η₁)) c
    have hcf := NestedCapRefinement.pre_comm (m + 1) p
      (FirstHalfFaceRefinement.map (CompactNearJoinParameters.tube α β R) (min_le_right η₀ η₁)) c hc
    have hif := NestedCapRefinement.pre_inclusion
      (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η₁)
      (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
      (FirstHalfFaceRefinement.map (CompactNearJoinParameters.tube α β R) (min_le_right η₀ η₁))
      (FirstHalfFaceRefinement.map_inclusion (CompactNearJoinParameters.tube α β R) (min_le_right η₀ η₁))
      (chains (FirstHalfBoundedCapDeformation.boundedCut
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B))
      (push (FirstHalfAnnularTimeInputs.projection
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B))
      (m + 1) p
      (FirstHalfAnnularTimeDomain.thom
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 (by omega) h)
      (FirstHalfAnnularTimeDomain.tested
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le p T) c hiC
    have hWf : ∀ center,
        JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
          JoinedRectangleRefinement.far (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1 ∨
        JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
          domain (tube (CompactNearJoinParameters.tube α β R))
            (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le) (fun _ => r) 1 := by
      intro center
      rcases hW₁ center with hfar | hnear
      · exact Or.inl ((JoinedRectangleRefinement.rectangleCover_mono (min_le_right η₀ η₁) center).trans hfar)
      · exact Or.inr ((JoinedRectangleRefinement.rectangleCover_mono (min_le_right η₀ η₁) center).trans hnear)
    have he := FirstInputRotationNativeTimeComparison.retained_homology_eq α β R r r hR hr hr.le le_rfl
      a ha ha1 F B η ζ hη hζ p T h hρr' hrot₀ hrot₁ hWf hgoodActual hT cf hcf hif w hw q
    rw [FirstHalfAnnularTimeDomain.post_homology_eq
      (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr.le F B w q] at he
    have hfull := FirstInputRotationTrimmedEndpoints.full_trim_homology_eq α β R r hR hr p T h F B
      ζ hζ hρr' hgoodActual hT a ha ha1 hrot₀ hrot₁ 1 q
    have hrot := FirstInputRotationTimeEndpoints.homology_eq α β R r hR hr p T h F B ζ hζ hρr' hgoodActual hT q
    exact (hsplit q).trans (congrArg (fun z => z + k.homology q)
      ((heDef q).trans ((he.trans hfull.symm).trans hrot.symm)))
  · intro q
    apply FilteredModelNativeComparison.full_inclusion m p h hρr' hr.le T hT
      (TopCat.of (CompactNearJoinParameters.tube α β R)) (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)
      (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 0) (maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 0)
      hFull₀ hFull₁ (JoinedFilteredCap.sublevel F B) (D 0) (hDi 0) f hf (JoinedTimeSplit.loopFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) ?_ q
    ext z : 1
    rfl
  · intro q
    rw [← heDef q]
    exact hgNative q
  · intro q
    apply FilteredModelNativeComparison.identified_inclusion m p h hρr' hr.le T hT
      (TopCat.of (CompactNearJoinParameters.tube α β R)) (TopCat.of (Outer (CompactNearJoinParameters.tube α β R))) (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η₀)
      (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 2) (maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 4)
      (fun x => hside₀ 1 1 x) (fun x => hside₁ 1 1 x) (JoinedFilteredCap.sublevel F B) (D 2) (hDi 2) k hk
      _ ?_ hSecond₀ hSecond₁ q
    change planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1 ≫ JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le 2 = _
    exact JoinedEndpointMaps.second_end (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le

end
end Finsler.JoinedRotationFilteredSplit
