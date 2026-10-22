module

public import Finsler.Topology.JoinedFilteredInteriorSplit
public import Finsler.Topology.FilteredTimePrismOperation
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! The actual full and both interior refined time cuts are genuine
filtered degree-lowering operations. The common-small-cycle split
then descends to every input homology class in the same filtered target.
Identification with the unsubdivided native time operation remains separate. -/

@[expose] public section
namespace Finsler.JoinedFilteredHomologySplit
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.JoinedComparisonAdequacy
open Finsler.JoinedCommonInputRefinement Finsler.JoinedSimultaneousPrisms Finsler.JoinedSmallCapExtension
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem homology_split {X : Type} [PseudoMetricSpace X] [CompactSpace X]
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
    : ∃ f g h : DegreeLoweringHomology.Map (chains (TopCat.of X)) (chains (TopCat.of B)) (m + p),
      (∀ q, f.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
        (push (maps (TopCat.of X) 0)).f ((m + p) + q + 1) ≫
        cap X η hη (chains (TopCat.of B)) (m + p) (v 0) q) ∧
      (∀ q, g.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
        (push (maps (TopCat.of X) 4)).f ((m + p) + q + 1) ≫
        cap X η hη (chains (TopCat.of B)) (m + p) (v 1) q) ∧
      (∀ q, h.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
        (push (maps (TopCat.of X) 4)).f ((m + p) + q + 1) ≫
        cap X η hη (chains (TopCat.of B)) (m + p) (v 2) q) ∧
      ∀ q, f.homology q = g.homology q + h.homology q := by
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
  have hf₀ (x : X) : SupportedSelfCut.distance (m + 1)
      (JoinedFamilyNaturality.globalMap u a ha ha1 0 (maps (TopCat.of X) 0 (0, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily u) (0, x) ≤ δ
    rw [UniformSelfCutCollar.distance_zero]
    exact h.1.le
  have hf₁ (x : X) : SupportedSelfCut.distance (m + 1)
      (JoinedFamilyNaturality.globalMap u a ha ha1 0 (maps (TopCat.of X) 0 (1, x))) ≤ δ := by
    change UniformSelfCutCollar.jointDistance (JoinedTimeSplit.loopFamily u) (1, x) ≤ δ
    rw [UniformSelfCutCollar.distance_one]
    exact h.1.le
  let f := FilteredTimePrismOperation.operation m p h hρr hr T hT (TopCat.of X) (TopCat.of (Outer X))
    (JoinedFilteredCap.rectangleCover X η) (JoinedFamilyNaturality.globalMap u a ha ha1 0) B (D 0) (hDi 0)
    (maps (TopCat.of X) 0) (hD 0) hf₀ hf₁
  let g := FilteredTimePrismOperation.operation m p h hρr hr T hT (TopCat.of X) (TopCat.of (Outer X))
    (JoinedFilteredCap.rectangleCover X η) (JoinedFamilyNaturality.globalMap u a ha ha1 1) B (D 1) (hDi 1)
    (maps (TopCat.of X) 4) (hD 1) (fun x => hs₀ 0 1 x) (fun x => hs₁ 0 1 x)
  let k := FilteredTimePrismOperation.operation m p h hρr hr T hT (TopCat.of X) (TopCat.of (Outer X))
    (JoinedFilteredCap.rectangleCover X η) (JoinedFamilyNaturality.globalMap u a ha ha1 2) B (D 2) (hDi 2)
    (maps (TopCat.of X) 4) (hD 2) (fun x => hs₀ 1 1 x) (fun x => hs₁ 1 1 x)
  refine ⟨f, g, k, (fun q => rfl), (fun q => rfl), (fun q => rfl), ?_⟩
  intro q
  obtain ⟨W, hW⟩ := JoinedFilteredInteriorSplit.cycle_split m p h hρr hr T hT
    u a ha ha1 η hη B v hv hc hs₀ hs₁ q
  apply SmallInclusionHomologyCancellation.split_of_small_boundary (TopCat.of X) (inputCover X η)
    (inputCover_open X η) (inputCover_univ X η hη) (chains (TopCat.of B)) (m + p) f g k q W
  simpa only [f, g, k, FilteredTimePrismOperation.operation, TimePrismDescent.operation,
    TimePrismDescent.component, FilteredTimePrismOperation.along, AnnularTimeTrim.prism,
    sourceCycle, D, Category.assoc] using hW

end
end Finsler.JoinedFilteredHomologySplit
