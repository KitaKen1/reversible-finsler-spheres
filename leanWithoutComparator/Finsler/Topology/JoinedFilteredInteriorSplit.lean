module

public import Finsler.Topology.JoinedSmallCapExtension
public import Finsler.Topology.TimeIntervalPrismIdentification

/-! Assemble the actual triangle, both actual double prisms, and both
small-retraction naturality corrections on one common base input cover.
Every correction chain stays in the given genuine filtered loop target. -/

@[expose] public section
namespace Finsler.JoinedFilteredInteriorSplit

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.JoinedComparisonAdequacy
open Finsler.JoinedComparisonSource Finsler.JoinedRefinedComparisons
open Finsler.JoinedCommonInputRefinement Finsler.JoinedSimultaneousPrisms Finsler.JoinedSmallCapExtension

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem cycle_split {X : Type} [PseudoMetricSpace X] [CompactSpace X]
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
    (q : ℕ) :
    ∃ W : (small (TopCat.of X) (inputCover X η)).cycles ((m + p) + q) ⟶ (chains (TopCat.of B)).X (q + 1),
      sourceCycle X η ((m + p) + q) ≫ (push (maps (TopCat.of X) 0)).f ((m + p) + q + 1) ≫
        cap X η hη (chains (TopCat.of B)) (m + p) (v 0) q =
      sourceCycle X η ((m + p) + q) ≫ (push (maps (TopCat.of X) 4)).f ((m + p) + q + 1) ≫
        cap X η hη (chains (TopCat.of B)) (m + p) (v 1) q +
      sourceCycle X η ((m + p) + q) ≫ (push (maps (TopCat.of X) 4)).f ((m + p) + q + 1) ≫
        cap X η hη (chains (TopCat.of B)) (m + p) (v 2) q +
      W ≫ (chains (TopCat.of B)).d (q + 1) q := by
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
  obtain ⟨P, hP⟩ := paired_boundaries u a ha ha1 η hη B (m + p)
    (fun s => AnnularCutComparison.cut m p h hρr hr T hT s) v hv hc
  let I := inclusion (TopCat.of X) (inputCover X η)
  let Z := small (TopCat.of X) (inputCover X η)
  let j := (m + p) + q
  let z := Z.iCycles j ≫ I.f j
  let e := HomologicalComplex.cyclesMap I j
  have he : e ≫ (chains (TopCat.of X)).iCycles j = z := HomologicalComplex.cyclesMap_i I j
  let prism := sourceCycle X η j
  let full := prism ≫ (push (maps (TopCat.of X) 0)).f (j + 1) ≫ D 0 q
  let half₀ := prism ≫ (push (maps (TopCat.of X) 1)).f (j + 1) ≫ D 0 q
  let half₁ := prism ≫ (push (maps (TopCat.of X) 2)).f (j + 1) ≫ D 0 q
  let start₀ := prism ≫ (push (maps (TopCat.of X) 3)).f (j + 1) ≫ D 1 q
  let start₁ := prism ≫ (push (maps (TopCat.of X) 3)).f (j + 1) ≫ D 2 q
  let end₀ := prism ≫ (push (maps (TopCat.of X) 4)).f (j + 1) ≫ D 1 q
  let end₁ := prism ≫ (push (maps (TopCat.of X) 4)).f (j + 1) ≫ D 2 q
  let tri := z ≫ triangleSource (TopCat.of X) j ≫ D 0 (q + 1)
  let sq₀ := z ≫ squareSource (TopCat.of X) j ≫ D 1 (q + 1)
  let sq₁ := z ≫ squareSource (TopCat.of X) j ≫ D 2 (q + 1)
  have ht : full = half₀ + half₁ + tri ≫ (chains (TopCat.of B)).d (q + 1) q := by
    have ht := congrArg (fun f => e ≫ f)
      (CappedTimeSplit.full_split (triangleLift (TopCat.of X)) (m + p) (D 0) (hD 0) q)
    simp only [e, Preadditive.comp_add, Category.assoc, HomologicalComplex.cyclesMap_i_assoc] at ht
    simpa [Category.assoc,
      TimeIntervalPrismIdentification.component_prism,
      CappedTimeSplit.comparison, full, half₀, half₁, tri, prism, sourceCycle,
      z, Z, I, j, maps, JoinedEndpointMaps.firstHalf, JoinedEndpointMaps.secondHalf,
      triangleSource, Category.assoc] using ht
  have hp₀ : half₀ = start₀ + P 0 q ≫ (chains (TopCat.of B)).d (q + 1) q := by
    have hh : half₀ - start₀ = P 0 q ≫ (chains (TopCat.of B)).d (q + 1) q := by
      simpa [Preadditive.comp_sub, Category.assoc, half₀, start₀, prism, D, cap, j, maps, Fin.succ] using hP 0 q
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  have hp₁ : half₁ = start₁ + P 1 q ≫ (chains (TopCat.of B)).d (q + 1) q := by
    have hh : half₁ - start₁ = P 1 q ≫ (chains (TopCat.of B)).d (q + 1) q := by
      simpa [Preadditive.comp_sub, Category.assoc, half₁, start₁, prism, D, cap, j, maps, Fin.succ] using hP 1 q
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  have hsq (i : Fin 2) := congrArg (fun f => e ≫ f)
    (square_boundary m p h hρr hr T hT (TopCat.of X) (JoinedFilteredCap.rectangleCover X η)
      (JoinedFamilyNaturality.globalMap u a ha ha1 i.succ) B (D i.succ) (hDi i.succ)
      (hD i.succ) (hs₀ i) (hs₁ i) q)
  have hs0 : start₀ = end₀ + sq₀ ≫ (chains (TopCat.of B)).d (q + 1) q := by
    have h0 := hsq 0
    simp only [e, Category.assoc, HomologicalComplex.cyclesMap_i_assoc] at h0
    have hh : start₀ - end₀ = sq₀ ≫ (chains (TopCat.of B)).d (q + 1) q := by
      simpa [Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub,
        start₀, end₀, sq₀, prism, sourceCycle, z, Z, I, j, maps, Category.assoc] using h0
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  have hs1 : start₁ = end₁ + sq₁ ≫ (chains (TopCat.of B)).d (q + 1) q := by
    have h1 := hsq 1
    simp only [e, Category.assoc, HomologicalComplex.cyclesMap_i_assoc] at h1
    have hh : start₁ - end₁ = sq₁ ≫ (chains (TopCat.of B)).d (q + 1) q := by
      simpa [Category.assoc, Preadditive.sub_comp, Preadditive.comp_sub,
        start₁, end₁, sq₁, prism, sourceCycle, z, Z, I, j, maps, Category.assoc] using h1
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  refine ⟨tri + P 0 q + P 1 q + sq₀ + sq₁, ?_⟩
  change full = end₀ + end₁ + _
  rw [ht, hp₀, hp₁, hs0, hs1]
  simp only [Preadditive.add_comp]
  abel

end
end Finsler.JoinedFilteredInteriorSplit
