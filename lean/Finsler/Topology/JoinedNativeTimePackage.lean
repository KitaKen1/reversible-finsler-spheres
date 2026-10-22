module

public import Finsler.Topology.JoinedNativeTimeModels
public import Finsler.Topology.ClosedCapDegreeTransport
public import Finsler.Topology.JoinedHalfTrim

/-! For the original joined family choose one interior time and one
common rectangle/input refinement before every tested cochain, degree
and threshold. The actual full and both original interior time operators have genuine
filtered lifts whose split holds in the same retained-length target;
their native ambient homology images are identified. -/

@[expose] public section
namespace Finsler.JoinedNativeTimePackage

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.JoinedComparisonAdequacy
open Finsler.JoinedCommonInputRefinement Finsler.JoinedSimultaneousPrisms Finsler.JoinedSmallCapExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem exists_native_filtered_split {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (u : C(X, H1JoinContinuity.composable (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2),
      ∃ (hFirst₀ : ∀ x, SupportedSelfCut.distance (m + 1)
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (0, x)) ≤ δ)
        (hFirst₁ : ∀ x, SupportedSelfCut.distance (m + 1)
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (1, x)) ≤ δ)
        (hSecond₀ : ∀ x, SupportedSelfCut.distance (m + 1)
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (0, x)) ≤ δ)
        (hSecond₁ : ∀ x, SupportedSelfCut.distance (m + 1)
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le (1, x)) ≤ δ),
      ∃ (η : ℝ) (hη : 0 < η), η ≤ b ∧
      (∀ c, IsOpen (cover X η c)) ∧ (⋃ c, cover X η c = Set.univ) ∧
      (∀ c, IsOpen (inputCover X η c)) ∧ (⋃ c, inputCover X η c = Set.univ) ∧
      ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      let B := JoinedFilteredCap.sublevel F (A - L + 3 * ε)
      ∃ v : Fin 3 → ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X
          ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q,
      (∀ i q,
        (v i q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
          (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f ((m + p) + q + 1) ≫
          (push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i)).f ((m + p) + q + 1) ≫
          AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q) ∧
        (v i (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
          (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
            ((m + p) + q + 2) ((m + p) + q + 1) ≫ v i q)) ∧
      ∃ f g k : DegreeLoweringHomology.Map (chains (TopCat.of X)) (chains (TopCat.of B)) (m + p),
      (∀ q, f.homology q = g.homology q + k.homology q) ∧
      (∀ q, f.homology q ≫ HomologicalComplex.homologyMap
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
        ((AnnularCutComparison.operation m p h (by linarith [h.1.trans h.2.2]) hr T hT).pre
          (push (TopCat.ofHom (JoinedTimeSplit.loopFamily u)))).homology q) ∧
      (∀ q, g.homology q ≫ HomologicalComplex.homologyMap
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
        (AnnularTrimHomology.operation m p h (by linarith [h.1.trans h.2.2]) hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) hFirst₀ hFirst₁).homology q) ∧
      (∀ q, k.homology q ≫ HomologicalComplex.homologyMap
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
        (AnnularTrimHomology.operation m p h (by linarith [h.1.trans h.2.2]) hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha.le ha1.le) hSecond₀ hSecond₁).homology q) := by
  classical
  obtain ⟨a, ha, ha1, hf₀, hf₁, hs₀, hs₁⟩ := JoinedHalfTrim.family_slide_sides_small u h.1
  have hside₀ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      SupportedSelfCut.distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i.succ ((s, 0), x)) ≤ δ := by
    intro i
    fin_cases i
    · exact hf₀
    · exact hs₀
  have hside₁ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      SupportedSelfCut.distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i.succ ((s, 1), x)) ≤ δ := by
    intro i
    fin_cases i
    · exact hf₁
    · exact hs₁
  obtain ⟨hFirst₀, hFirst₁, hSecond₀, hSecond₁⟩ := JoinedNativeTimeModels.trimmed_endpoints
    u a ha.le ha1.le δ hside₀ hside₁
  obtain ⟨η, hη, hηb, hop⟩ := JoinedAnnularFiltered.exists_closed_filtered_output m F u a ha.le ha1.le
    h hρr hr hε hb hradius
  refine ⟨a, ha, ha1, hFirst₀, hFirst₁, hSecond₀, hSecond₁, η, hη, hηb, cover_open X η, cover_univ X η hη,
    inputCover_open X η, inputCover_univ X η hη, ?_⟩
  intro p L A T hT hshort hA
  let B := JoinedFilteredCap.sublevel F (A - L + 3 * ε)
  choose d hd using (fun i : Fin 3 => hop i p L A T hT hshort hA)
  let v : Fin 3 → ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X
      ((m + p) + q + 1) ⟶ (chains (TopCat.of B)).X q :=
    fun i => ClosedCapDegreeTransport.align m p (d i)
  have hc (i : Fin 3) (q : ℕ) : v i (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d
        ((m + p) + q + 2) ((m + p) + q + 1) ≫ v i q :=
    ClosedCapDegreeTransport.align_comm m p (d i) (fun q => (hd i q).2) q
  have hi (i : Fin 3) (q : ℕ) : v i q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f ((m + p) + q + 1) ≫
      (push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i)).f ((m + p) + q + 1) ≫
      AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q := by
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      ClosedCapDegreeTransport.align_inclusion m p (d i)
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B))
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) ≫
        push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le i))
      (fun q => AnnularCutComparison.cut m p h (by linarith [h.1.trans h.2.2]) hr T hT q)
      (fun q => by simpa only [HomologicalComplex.comp_f, Category.assoc] using (hd i q).1) q
  refine ⟨v, (fun i q => ⟨hi i q, hc i q⟩), ?_⟩
  exact JoinedNativeTimeModels.native_models m p h (by linarith [h.1.trans h.2.2]) hr T hT
    u a ha.le ha1.le η hη B v hi hc hside₀ hside₁ hFirst₀ hFirst₁ hSecond₀ hSecond₁

end
end Finsler.JoinedNativeTimePackage
