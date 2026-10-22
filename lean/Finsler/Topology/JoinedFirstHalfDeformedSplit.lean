module

public import Finsler.Topology.FirstHalfRefinedTimeAgreement
public import Finsler.Topology.JoinedNativeTimePackage

/-! Before all tested data choose the actual interior time and both
genuine cap scales. Their minimum refines only the source. Replace the
first term in the actual filtered full-time split by the original
first-half cap followed by its length-preserving retained deformation.
The original full and both native interior time images are retained. -/

@[expose] public section
namespace Finsler.JoinedFirstHalfDeformedSplit

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.JoinedCommonInputRefinement Finsler.JoinedSimultaneousPrisms Finsler.JoinedSmallCapExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem exists_uniform_deformed_split {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) (F : ReversibleMetric (m + 1)) (u : C(X, H1JoinContinuity.composable (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
    ∃ (hFirst₀ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (0, x)) ≤ δ)
      (hFirst₁ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (1, x)) ≤ δ)
      (hSecond₀ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (0, x)) ≤ δ)
      (hSecond₁ : ∀ x, distance (m + 1)
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (1, x)) ≤ δ),
    ∃ (η₀ : ℝ) (hη₀ : 0 < η₀), η₀ ≤ b ∧
    ∃ (η₁ : ℝ) (hη₁ : 0 < η₁), η₁ ≤ b ∧
    let η := min η₀ η₁
    let hη : 0 < η := lt_min hη₀ hη₁
    ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
    cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
    (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
    let B := A - L + 3 * ε
    ∃ (d : Fin 3 → ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).X
        ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q)
      (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η₁)).X
        ((m + 1) + (p + q)) ⟶ (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)).X q)
      (f k : DegreeLoweringHomology.Map (chains (TopCat.of X)) (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p))
      (w : DegreeLoweringHomology.Map (chains (TopCat.of X))
        (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) (m + p)),
    (∀ i q, d i q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).f ((m + 1) + (p + q)) ≫
        (push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
              AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q) ∧
    (∀ i q, d i (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d i q) ∧
    (∀ q, c q ≫ (push (FirstHalfAnnularTimeInputs.projection u a ha ha1 hr F B)).f q =
      (inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η₁)).f ((m + 1) + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (ClosedInterval × X)) (m + 1) p q
          (FirstHalfAnnularTimeDomain.thom u a ha ha1 (by omega) h) (FirstHalfAnnularTimeDomain.tested u a ha ha1 hr p T)) ∧
    (∀ q, c (q + 1) ≫ (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)).d (q + 1) q =
      (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η₁)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q) ∧
    (∀ q, f.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
      (push (maps (TopCat.of X) 0)).f ((m + p) + q + 1) ≫
        cap X η₀ hη₀ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) (ClosedCapDegreeTransport.align m p (d 0)) q) ∧
    (∀ q, k.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
      (push (maps (TopCat.of X) 4)).f ((m + p) + q + 1) ≫
        cap X η₀ hη₀ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p) (ClosedCapDegreeTransport.align m p (d 2)) q) ∧
    (∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
      ClosedCapDegreeTransport.align m p
        (CutDomainTimePrism.retracted (TopCat.of X) (FirstHalfInteriorCapDomain.faceCover X η)
          (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
          (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) m p
          (NestedCapRefinement.pre (m + 1) p (FirstHalfFaceRefinement.map X (min_le_right η₀ η₁)) c)) q) ∧
    (∀ q, f.homology q =
      (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F B 1))).homology q + k.homology q) ∧
    (∀ q, f.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))) q =
      ((AnnularCutComparison.operation m p h (by linarith [h.1.trans h.2.2]) hr T hT).pre
        (push (TopCat.ofHom (JoinedTimeSplit.loopFamily u)))).homology q) ∧
    (∀ q, (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F B 1))).homology q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (JoinedFilteredCap.sublevel F B))) q =
      (AnnularTrimHomology.operation m p h (by linarith [h.1.trans h.2.2]) hr T hT
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) hFirst₀ hFirst₁).homology q) ∧
    (∀ q, k.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))) q =
      (AnnularTrimHomology.operation m p h (by linarith [h.1.trans h.2.2]) hr T hT
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le) hSecond₀ hSecond₁).homology q) := by
  classical
  have hρr' : ρ < r := by linarith [h.1.trans h.2.2]
  obtain ⟨a, ha, ha1, hf₀, hf₁, hs₀, hs₁⟩ := JoinedHalfTrim.family_slide_sides_small u h.1
  have hside₀ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i.succ ((s, 0), x)) ≤ δ := by
    intro i
    fin_cases i
    · exact hf₀
    · exact hs₀
  have hside₁ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i.succ ((s, 1), x)) ≤ δ := by
    intro i
    fin_cases i
    · exact hf₁
    · exact hs₁
  obtain ⟨hFirst₀, hFirst₁, hSecond₀, hSecond₁⟩ := JoinedNativeTimeModels.trimmed_endpoints u a ha.le ha1.le δ hside₀ hside₁
  obtain ⟨η₀, hη₀, hη₀b, hop₀⟩ := JoinedAnnularFiltered.exists_closed_filtered_output m F u a ha.le ha1.le
    h hρr hr hε hb hradius
  obtain ⟨η₁, hη₁, hη₁b, hW₁, hop₁⟩ := FirstHalfAnnularTimeDomain.exists_native_time_domain m F u a ha ha1
    h hρr hr hFirst₀ hFirst₁ hε hb hradius
  refine ⟨a, ha, ha1, hFirst₀, hFirst₁, hSecond₀, hSecond₁, η₀, hη₀, hη₀b, η₁, hη₁, hη₁b, ?_⟩
  dsimp only
  intro p L A T hT hshort hA
  let η := min η₀ η₁
  have hη : 0 < η := lt_min hη₀ hη₁
  let B := A - L + 3 * ε
  let Z := chains (TopCat.of (JoinedFilteredCap.sublevel F B))
  choose d hd using (fun i : Fin 3 => hop₀ i p L A T hT hshort hA)
  obtain ⟨c, hc, w₁, hiC, hw₁, hnC, hew₁, hbw₁⟩ := hop₁ p L A T hT hshort hA
  let v : Fin 3 → ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).X
      ((m + p) + q + 1) ⟶ Z.X q := fun i => ClosedCapDegreeTransport.align m p (d i)
  have hvc (i : Fin 3) (q : ℕ) : v i (q + 1) ≫ Z.d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).d
        ((m + p) + q + 2) ((m + p) + q + 1) ≫ v i q :=
    ClosedCapDegreeTransport.align_comm m p (d i) (fun q => (hd i q).2) q
  have hvi (i : Fin 3) (q : ℕ) : v i q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).f ((m + p) + q + 1) ≫
        (push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i)).f ((m + p) + q + 1) ≫
          AnnularCutComparison.cut m p h hρr' hr T hT q := by
    simpa only [HomologicalComplex.comp_f, Category.assoc] using ClosedCapDegreeTransport.align_inclusion m p (d i)
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B)))
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀) ≫ push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i))
      (fun q => AnnularCutComparison.cut m p h hρr' hr T hT q)
      (fun q => by simpa only [HomologicalComplex.comp_f, Category.assoc] using (hd i q).1) q
  obtain ⟨f, g, k, hf, hg, hk, hsplit⟩ := JoinedFilteredHomologySplit.homology_split m p h hρr' hr T hT
    u a ha.le ha1.le η₀ hη₀ (JoinedFilteredCap.sublevel F B) v hvi hvc hside₀ hside₁
  have hmap₄ : maps (TopCat.of X) 4 = planeFace (TopCat.of X) 1 := rfl
  have hR : JoinedSimultaneousPrisms.retraction X η₀ hη₀ =
      TauCeti.smallSingularRetraction (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η₀)
        (rectangles_open X η₀) (rectangles_univ X η₀ hη₀) := rfl
  have hg' (q : ℕ) : g.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
      (push (planeFace (TopCat.of X) 1) ≫ TauCeti.smallSingularRetraction (X := TopCat.of (Outer X)) coeff
        (JoinedFilteredCap.rectangleCover X η₀) (rectangles_open X η₀)
          (rectangles_univ X η₀ (hη.trans_le (min_le_left η₀ η₁)))).f ((m + p) + q + 1) ≫
            ClosedCapDegreeTransport.align m p (d 1) q := by
    simpa only [hmap₄, cap, hR, HomologicalComplex.comp_f, Category.assoc, v] using hg q
  obtain ⟨w, hw, heRet, heDef⟩ := FirstHalfRefinedTimeAgreement.exists_operation_and_eq m p h hρr' hr T hT F u a ha ha1
    η η₀ η₁ B hη (min_le_left η₀ η₁) (min_le_right η₀ η₁) hFirst₀ hFirst₁ hW₁ c hc hiC hnC
    (d 1) (fun q => (hd 1 q).1) (fun q => (hd 1 q).2) g hg'
  let D : Fin 3 → ∀ q, (chains (TopCat.of (Outer X))).X ((m + p) + q + 1) ⟶ Z.X q :=
    fun i => cap X η₀ hη₀ Z (m + p) (v i)
  have hDi (i : Fin 3) (q : ℕ) : D i q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (TauCeti.singularSmallApprox (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η₀)).f ((m + p) + q + 1) ≫
        (push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i)).f ((m + p) + q + 1) ≫ AnnularCutComparison.cut m p h hρr' hr T hT q :=
    cap_inclusion (P := parameters (m + 1)) (L := TopCat.of (SphereLoop (m + 1))) X η₀ hη₀ (m + p)
      (JoinedFilteredCap.sublevel F B) (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i)
      (fun q => AnnularCutComparison.cut m p h hρr' hr T hT q) (v i) (hvi i) q
  have hFull₀ (x : X) : distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha.le ha1.le 0 (maps (TopCat.of X) 0 (0, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily u) (0, x) ≤ δ
    rw [UniformSelfCutCollar.distance_zero]
    exact h.1.le
  have hFull₁ (x : X) : distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha.le ha1.le 0 (maps (TopCat.of X) 0 (1, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily u) (1, x) ≤ δ
    rw [UniformSelfCutCollar.distance_one]
    exact h.1.le
  have hgNative (q : ℕ) : g.homology q ≫ HomologicalComplex.homologyMap
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))) q =
      (AnnularTrimHomology.operation m p h hρr' hr T hT
        (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) hFirst₀ hFirst₁).homology q := by
    apply FilteredModelNativeComparison.identified_inclusion m p h hρr' hr T hT
      (TopCat.of X) (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)
      (JoinedFamilyNaturality.globalMap u a ha.le ha1.le 1) (maps (TopCat.of X) 4)
      (fun x => hside₀ 0 1 x) (fun x => hside₁ 0 1 x) (JoinedFilteredCap.sublevel F B) (D 1) (hDi 1) g hg
      _ ?_ hFirst₀ hFirst₁ q
    change planeFace (TopCat.of X) 1 ≫ JoinedFamilyNaturality.globalMap u a ha.le ha1.le 1 = _
    exact JoinedEndpointMaps.first_end u a ha.le ha1.le
  refine ⟨d, c, f, k, w, (fun i q => (hd i q).1), (fun i q => (hd i q).2), hiC, hc, hf, hk, hw, ?_, ?_, ?_, ?_⟩
  · intro q
    exact (hsplit q).trans (congrArg (fun z => z + k.homology q) (heDef q))
  · intro q
    apply FilteredModelNativeComparison.full_inclusion m p h hρr' hr T hT
      (TopCat.of X) (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)
      (JoinedFamilyNaturality.globalMap u a ha.le ha1.le 0) (maps (TopCat.of X) 0)
      hFull₀ hFull₁ (JoinedFilteredCap.sublevel F B) (D 0) (hDi 0) f hf (JoinedTimeSplit.loopFamily u) ?_ q
    ext z : 1
    rfl
  · intro q
    rw [← heDef q]
    exact hgNative q
  · intro q
    apply FilteredModelNativeComparison.identified_inclusion m p h hρr' hr T hT
      (TopCat.of X) (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)
      (JoinedFamilyNaturality.globalMap u a ha.le ha1.le 2) (maps (TopCat.of X) 4)
      (fun x => hside₀ 1 1 x) (fun x => hside₁ 1 1 x) (JoinedFilteredCap.sublevel F B) (D 2) (hDi 2) k hk
      _ ?_ hSecond₀ hSecond₁ q
    change planeFace (TopCat.of X) 1 ≫ JoinedFamilyNaturality.globalMap u a ha.le ha1.le 2 = _
    exact JoinedEndpointMaps.second_end u a ha.le ha1.le

end
end Finsler.JoinedFirstHalfDeformedSplit
