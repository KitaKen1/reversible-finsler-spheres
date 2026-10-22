module

public import Finsler.Topology.FilteredModelNativeComparison
public import Finsler.Topology.JoinedFilteredHomologySplit

/-! The actual full and both original trimmed annular time operations
have genuine lifts to one retained-length target. Their split is proved
inside that target, while each lift has its specified original ambient
homology image. No target homology injectivity is assumed. -/

@[expose] public section
namespace Finsler.JoinedNativeTimeModels
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.JoinedComparisonAdequacy
open Finsler.JoinedCommonInputRefinement Finsler.JoinedSimultaneousPrisms Finsler.JoinedSmallCapExtension
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem trimmed_endpoints {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (δ : ℝ)
    (hs₀ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      SupportedSelfCut.distance n (JoinedFamilyNaturality.globalMap u a ha ha1 i.succ ((s, 0), x)) ≤ δ)
    (hs₁ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      SupportedSelfCut.distance n (JoinedFamilyNaturality.globalMap u a ha ha1 i.succ ((s, 1), x)) ≤ δ) :
    (∀ x, SupportedSelfCut.distance n (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1 (0, x)) ≤ δ) ∧
    (∀ x, SupportedSelfCut.distance n (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1 (1, x)) ≤ δ) ∧
    (∀ x, SupportedSelfCut.distance n (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1 (0, x)) ≤ δ) ∧
    (∀ x, SupportedSelfCut.distance n (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1 (1, x)) ≤ δ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    have he := ConcreteCategory.congr_hom (JoinedEndpointMaps.first_end u a ha ha1) (0, x)
    change JoinedFamilyNaturality.globalMap u a ha ha1 1 ((1, 0), x) = _ at he
    rw [← he]
    exact hs₀ 0 1 x
  · intro x
    have he := ConcreteCategory.congr_hom (JoinedEndpointMaps.first_end u a ha ha1) (1, x)
    change JoinedFamilyNaturality.globalMap u a ha ha1 1 ((1, 1), x) = _ at he
    rw [← he]
    exact hs₁ 0 1 x
  · intro x
    have he := ConcreteCategory.congr_hom (JoinedEndpointMaps.second_end u a ha ha1) (0, x)
    change JoinedFamilyNaturality.globalMap u a ha ha1 2 ((1, 0), x) = _ at he
    rw [← he]
    exact hs₀ 1 1 x
  · intro x
    have he := ConcreteCategory.congr_hom (JoinedEndpointMaps.second_end u a ha ha1) (1, x)
    change JoinedFamilyNaturality.globalMap u a ha ha1 2 ((1, 1), x) = _ at he
    rw [← he]
    exact hs₁ 1 1 x

theorem native_models {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m p : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (u : C(X, H1JoinContinuity.composable (m + 1))) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (η : ℝ) (hη : 0 < η) (B : Set (SphereLoop (m + 1)))
    (v : Fin 3 → ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X ((m + p) + q + 1) ⟶
      (chains (TopCat.of B)).X q)
    (hv : ∀ i q, v i q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f ((m + p) + q + 1) ≫
        (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f ((m + p) + q + 1) ≫
        AnnularCutComparison.cut m p h hρr hr T hT q)
    (hc : ∀ i q, v i (q + 1) ≫ (chains (TopCat.of B)).d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).d ((m + p) + q + 2) ((m + p) + q + 1) ≫ v i q)
    (hs₀ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      SupportedSelfCut.distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha ha1 i.succ ((s, 0), x)) ≤ δ)
    (hs₁ : ∀ (i : Fin 2) (s : ClosedInterval) (x : X),
      SupportedSelfCut.distance (m + 1) (JoinedFamilyNaturality.globalMap u a ha ha1 i.succ ((s, 1), x)) ≤ δ)
    (hFirst₀ : ∀ x, SupportedSelfCut.distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1 (0, x)) ≤ δ)
    (hFirst₁ : ∀ x, SupportedSelfCut.distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1 (1, x)) ≤ δ)
    (hSecond₀ : ∀ x, SupportedSelfCut.distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1 (0, x)) ≤ δ)
    (hSecond₁ : ∀ x, SupportedSelfCut.distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1 (1, x)) ≤ δ) :
    ∃ f g k : DegreeLoweringHomology.Map (chains (TopCat.of X)) (chains (TopCat.of B)) (m + p),
      (∀ q, f.homology q = g.homology q + k.homology q) ∧
      (∀ q, f.homology q ≫ HomologicalComplex.homologyMap
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
        ((AnnularCutComparison.operation m p h hρr hr T hT).pre
          (push (TopCat.ofHom (JoinedTimeSplit.loopFamily u)))).homology q) ∧
      (∀ q, g.homology q ≫ HomologicalComplex.homologyMap
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
        (AnnularTrimHomology.operation m p h hρr hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1) hFirst₀ hFirst₁).homology q) ∧
      (∀ q, k.homology q ≫ HomologicalComplex.homologyMap
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)) q =
        (AnnularTrimHomology.operation m p h hρr hr T hT
          (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1) hSecond₀ hSecond₁).homology q) := by
  obtain ⟨f, g, k, hf, hg, hk, hsplit⟩ := JoinedFilteredHomologySplit.homology_split m p h hρr hr T hT
    u a ha ha1 η hη B v hv hc hs₀ hs₁
  let D : Fin 3 → ∀ s, (chains (TopCat.of (Outer X))).X ((m + p) + s + 1) ⟶ (chains (TopCat.of B)).X s :=
    fun i => cap X η hη (chains (TopCat.of B)) (m + p) (v i)
  have hD (i : Fin 3) (s : ℕ) : D i (s + 1) ≫ (chains (TopCat.of B)).d (s + 1) s =
      (chains (TopCat.of (Outer X))).d ((m + p) + s + 2) ((m + p) + s + 1) ≫ D i s :=
    cap_comm X η hη (chains (TopCat.of B)) (m + p) (v i) (hc i) s
  have hDi (i : Fin 3) (s : ℕ) : D i s ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) B)).f s =
      (TauCeti.singularSmallApprox (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η)).f ((m + p) + s + 1) ≫
        (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f ((m + p) + s + 1) ≫
        AnnularCutComparison.cut m p h hρr hr T hT s :=
    cap_inclusion (P := SelfCutThomCocycle.parameters (m + 1)) (L := TopCat.of (SphereLoop (m + 1)))
      X η hη (m + p) B (JoinedFamilyNaturality.globalMap u a ha ha1 i)
      (fun s => AnnularCutComparison.cut m p h hρr hr T hT s) (v i) (hv i) s
  have hFull₀ (x : X) : SupportedSelfCut.distance (m + 1)
      (JoinedFamilyNaturality.globalMap u a ha ha1 0 (maps (TopCat.of X) 0 (0, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily u) (0, x) ≤ δ
    rw [UniformSelfCutCollar.distance_zero]
    exact h.1.le
  have hFull₁ (x : X) : SupportedSelfCut.distance (m + 1)
      (JoinedFamilyNaturality.globalMap u a ha ha1 0 (maps (TopCat.of X) 0 (1, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily u) (1, x) ≤ δ
    rw [UniformSelfCutCollar.distance_one]
    exact h.1.le
  refine ⟨f, g, k, hsplit, ?_, ?_, ?_⟩
  · intro q
    apply FilteredModelNativeComparison.full_inclusion m p h hρr hr T hT
      (TopCat.of X) (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)
      (JoinedFamilyNaturality.globalMap u a ha ha1 0) (maps (TopCat.of X) 0)
      hFull₀ hFull₁ B (D 0) (hDi 0) f hf (JoinedTimeSplit.loopFamily u) ?_ q
    apply TopCat.ext
    intro z
    rfl
  · intro q
    apply FilteredModelNativeComparison.identified_inclusion m p h hρr hr T hT
      (TopCat.of X) (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)
      (JoinedFamilyNaturality.globalMap u a ha ha1 1) (maps (TopCat.of X) 4)
      (fun x => hs₀ 0 1 x) (fun x => hs₁ 0 1 x) B (D 1) (hDi 1) g hg
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1) ?_ hFirst₀ hFirst₁ q
    change JoinedRefinedComparisons.planeFace (TopCat.of X) 1 ≫
      JoinedFamilyNaturality.globalMap u a ha ha1 1 = _
    exact JoinedEndpointMaps.first_end u a ha ha1
  · intro q
    apply FilteredModelNativeComparison.identified_inclusion m p h hρr hr T hT
      (TopCat.of X) (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)
      (JoinedFamilyNaturality.globalMap u a ha ha1 2) (maps (TopCat.of X) 4)
      (fun x => hs₀ 1 1 x) (fun x => hs₁ 1 1 x) B (D 2) (hDi 2) k hk
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1) ?_ hSecond₀ hSecond₁ q
    change JoinedRefinedComparisons.planeFace (TopCat.of X) 1 ≫
      JoinedFamilyNaturality.globalMap u a ha ha1 2 = _
    exact JoinedEndpointMaps.second_end u a ha ha1

end
end Finsler.JoinedNativeTimeModels
