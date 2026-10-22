module

public import Finsler.Topology.FirstHalfAnnularTimeInputs

/-! Assemble the actual first-half annular time prism in its genuine
length-bounded cut domain. Its specified native two-cap input is retained,
and the fixed-tested-output deformation has a concrete comparison
boundary in the same retained-length target. -/

@[expose] public section
namespace Finsler.FirstHalfAnnularTimeDomain

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

def thom (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) n :=
  cochainPullback (planeFace (TopCat.of X) 1) n
    (SupportedSelfCutAdequacy.extension (tube X) (family u a ha.le ha1.le) 1 n
      (AnnularSelfCut.cocycle n hn h))

def tested {r : ℝ} (hr : r ≤ 1) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    singularCochainGroup (ZMod 2) (TopCat.of (ClosedInterval × X)) p :=
  cochainPullback (planeFace (TopCat.of X) 1) p
    (testedExtension (tube X) (family u a ha.le ha1.le) (fun _ => r) (fun _ => hr) 1 p T)

theorem post_homology_eq {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ)
    {K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (w : DegreeLoweringHomology.Map K (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) d)
    (q : ℕ) :
    (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).homology q =
      (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F B 1))).homology q := by
  have he := ((FirstHalfInteriorPrism.homotopy u a ha ha1 hr F B).toSSet.chainComplexMap coeff).homologyMap_eq q
  rw [← FirstHalfBoundedCapDeformation.retained_zero,
    FirstHalfBoundedCapDeformation.endpoint, FirstHalfBoundedCapDeformation.endpoint,
    push_comp, push_comp, DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
  simpa only [push, JoinedFilteredCap.sublevel] using
    congrArg (fun g => w.homology q ≫
      HomologicalComplex.homologyMap (push (FirstHalfBoundedCapDeformation.toInterior u a ha ha1 hr F B)) q ≫ g) he

theorem exists_native_time_domain {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m : ℕ) (F : ReversibleMetric (m + 1))
    (u : C(X, H1JoinContinuity.composable (m + 1)))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (h₀ : ∀ x, distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (0, x)) ≤ δ)
    (h₁ : ∀ x, distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (1, x)) ≤ δ)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧
      ∃ hW : ∀ center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha.le ha1.le ρ 1 ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1,
      ∀ (p : ℕ) (L A : ℝ)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      let C := TopCat.of (ClosedInterval × X)
      let U := FirstHalfInteriorCapDomain.faceCover X η
      let E := chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F (A - L + 3 * ε))
      ∃ c : ∀ q, (small C U).X ((m + 1) + (p + q)) ⟶ E.X q,
      ∃ hc : ∀ q, c (q + 1) ≫ E.d (q + 1) q =
        (small C U).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q,
      ∃ w : DegreeLoweringHomology.Map (chains (TopCat.of X)) E (m + p),
      (∀ q, c q ≫ (push (FirstHalfAnnularTimeInputs.projection u a ha ha1 hr F (A - L + 3 * ε))).f q =
        (inclusion C U).f ((m + 1) + (p + q)) ≫ PartialDoubleCap.cap C (m + 1) p q
          (thom u a ha ha1 (by omega) h) (tested u a ha ha1 hr p T)) ∧
      (∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
        ClosedCapDegreeTransport.align m p
          (CutDomainTimePrism.retracted (TopCat.of X) U
            (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
            E m p c) q) ∧
      (∀ q, (FirstHalfInteriorCapDomain.faceMap X η ≫
          JoinedLocalizedCutComparison.familySmallMap u a ha.le ha1.le ρ r 1
            (JoinedFilteredCap.rectangleCover X η) hW).f ((m + 1) + (p + q)) ≫
          SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
            (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
            (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
            (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl =
          c q ≫ (push (FirstHalfNativeCapDeformation.nativeCut u a ha ha1 hr F (A - L + 3 * ε))).f q) ∧
      (∀ q, (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F (A - L + 3 * ε)))).homology q =
        (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F (A - L + 3 * ε) 1))).homology q) ∧
      (∀ q, (chains (TopCat.of X)).iCycles ((m + p) + q) ≫
        ((w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F (A - L + 3 * ε)))).component q -
         (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F (A - L + 3 * ε) 1))).component q) =
        ((chains (TopCat.of X)).iCycles ((m + p) + q) ≫ w.component q ≫
          (push (FirstHalfBoundedCapDeformation.toInterior u a ha ha1 hr F (A - L + 3 * ε))).f q ≫
            FirstHalfInteriorPrism.prism u a ha ha1 hr F (A - L + 3 * ε) q) ≫
              (chains (TopCat.of (JoinedFilteredCap.sublevel F (A - L + 3 * ε)))).d (q + 1) q) := by
  have hρ : 0 < ρ := h.1.trans h.2.2
  obtain ⟨η, hη, hηb, hW, hop⟩ := FirstHalfInteriorCapDomain.exists_native_closed_lifts
    F u a ha ha1 hρ hρr hr hε hb hradius
  refine ⟨η, hη, hηb, hW, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨c, he⟩ := hop (m + 1) p L A
    (AnnularSelfCut.cocycle (m + 1) (by omega) h)
    (AnnularSelfCut.cocycle_closed (m + 1) (by omega) h)
    (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h) T hT hshort hA
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let U := FirstHalfInteriorCapDomain.faceCover X η
  let E := chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F (A - L + 3 * ε))
  let c' : ∀ q, (small C U).X ((m + 1) + (p + q)) ⟶ E.X q := c
  have hc : ∀ q, c' (q + 1) ≫ E.d (q + 1) q =
      (small C U).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c' q := fun q => (he q).2.1
  let j := push (FirstHalfAnnularTimeInputs.projection u a ha ha1 hr F (A - L + 3 * ε))
  have hj : ∀ q, Mono (j.f q) := FirstHalfAnnularTimeInputs.projection_mono u a ha ha1 hr F (A - L + 3 * ε)
  have hi : ∀ q, c' q ≫ j.f q = (inclusion C U).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap C (m + 1) p q (thom u a ha ha1 (by omega) h) (tested u a ha ha1 hr p T) := by
    intro q
    simpa only [j, FirstHalfAnnularTimeInputs.projection, push_comp, HomologicalComplex.comp_f,
      Category.assoc, thom, tested, C, U, c', FirstHalfBoundedCapDeformation.boundedSet] using (he q).1
  have hφ := FirstHalfAnnularTimeInputs.annular_inner_zero u a ha ha1 (by omega : 1 ≤ m + 1) h
  let w : DegreeLoweringHomology.Map (chains (TopCat.of X)) E (m + p) :=
    CutDomainTimePrism.operation (TopCat.of X) U
      (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
      E m p c' (FirstHalfAnnularTimeInputs.collar u a ha ha1 δ)
      (thom u a ha ha1 (by omega) h) (tested u a ha ha1 hr p T) hφ j hj hi hc h₀ h₁
  refine ⟨c', hc, w, hi, ?_, ?_, ?_, ?_⟩
  · intro q
    rfl
  · intro q
    simpa only [FirstHalfNativeCapDeformation.nativeCut, push_comp,
      HomologicalComplex.comp_f, Category.assoc, c', FirstHalfBoundedCapDeformation.boundedSet] using (he q).2.2
  · intro q
    exact post_homology_eq u a ha ha1 hr F (A - L + 3 * ε) w q
  · intro q
    exact FirstHalfBoundedCapDeformation.capped_prism_boundary u a ha ha1 hr F (A - L + 3 * ε) w q

end
end Finsler.FirstHalfAnnularTimeDomain
