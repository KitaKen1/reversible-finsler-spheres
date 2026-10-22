module

public import Finsler.Topology.FirstHalfInteriorFaceDomain
public import Finsler.Topology.NestedCapHomology

/-! Postcompose the actual two-stage cap's length-bounded cut-domain
lift with the genuine fixed-tested-output first-half deformation. The
comparison boundary stays in the same retained-length sublevel. -/

@[expose] public section
namespace Finsler.FirstHalfBoundedCapDeformation

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
  {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ)

def boundedSet : Set ((planeFace (TopCat.of X) 1) ⁻¹'
    domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1) :=
  PartialDoubleCapDomainFiltered.boundedDomain
    (TopCat.of (ClosedInterval × X)) (TopCat.of (SphereLoop n))
    ((planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
    (DoubleCapEmbeddingPullback.retained (planeFace (TopCat.of X) 1)
      (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
      (retainedMap (tube X) (family u a ha.le ha1.le) (fun _ => r) (fun _ => hr) 1))
    (JoinedFilteredCap.sublevel F A)

def boundedCut : TopCat.{0} := TopCat.of (boundedSet u a ha ha1 hr F A)

def toInterior : boundedCut u a ha ha1 hr F A ⟶
    TopCat.of (FirstHalfInteriorFamily.filteredDomain u a ha ha1 hr F A) :=
  FirstHalfInteriorFaceDomain.boundedToInterior u a ha ha1 hr F A

def retained : boundedCut u a ha ha1 hr F A ⟶ TopCat.of (JoinedFilteredCap.sublevel F A) :=
  PartialDoubleCapDomainFiltered.retained
    (TopCat.of (ClosedInterval × X)) (TopCat.of (SphereLoop n))
    ((planeFace (TopCat.of X) 1) ⁻¹' domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
    (DoubleCapEmbeddingPullback.retained (planeFace (TopCat.of X) 1)
      (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
      (retainedMap (tube X) (family u a ha.le ha1.le) (fun _ => r) (fun _ => hr) 1))
    (JoinedFilteredCap.sublevel F A)

def endpoint (s : _root_.unitInterval) :
    boundedCut u a ha ha1 hr F A ⟶ TopCat.of (JoinedFilteredCap.sublevel F A) :=
  toInterior u a ha ha1 hr F A ≫ TopCat.ofHom (FirstHalfInteriorPrism.endpoint u a ha ha1 hr F A s)

theorem retained_zero : endpoint u a ha ha1 hr F A 0 = retained u a ha ha1 hr F A := by
  apply TopCat.ext
  intro z
  apply Subtype.ext
  change (FirstHalfInteriorPrism.endpoint u a ha ha1 hr F A 0
    (FirstHalfInteriorFaceDomain.boundedToInterior u a ha ha1 hr F A z)).val = _
  rw [FirstHalfInteriorPrism.zero_original]
  have he := ConcreteCategory.congr_hom (FirstHalfInteriorFaceDomain.retained_native u a ha ha1 hr) z.val
  change _ = FirstHalfInteriorNative.originalRetainedMap u a ha ha1 hr
    (FirstHalfInteriorFaceDomain.toInterior u a ha ha1 r z.val) at he
  exact he.symm

theorem tested_native :
    toInterior u a ha ha1 hr F A ≫ FirstHalfInteriorTestedCap.testedMap u a ha ha1 hr F A =
      SupportedCap.subspaceMap
        (TopCat.of ((planeFace (TopCat.of X) 1) ⁻¹'
          domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1))
        (boundedSet u a ha ha1 hr F A) ≫
      DoubleCapEmbeddingPullback.domainMap (planeFace (TopCat.of X) 1)
        (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1) ≫
      testedMap (tube X) (family u a ha.le ha1.le) (fun _ => r) (fun _ => hr) 1 := by
  apply TopCat.ext
  intro z
  have he := ConcreteCategory.congr_hom (FirstHalfInteriorFaceDomain.toCut_native u a ha ha1 r) z.val
  change toCut (tube X) (family u a ha.le ha1.le) (fun _ => r) 1
      (DoubleCapEmbeddingPullback.domainMap (planeFace (TopCat.of X) 1)
        (domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1) z.val) =
    FirstHalfInteriorNative.toCut u a ha ha1 r (FirstHalfInteriorFaceDomain.toInterior u a ha ha1 r z.val) at he
  have ht := ConcreteCategory.congr_hom (FirstHalfInteriorNative.tested_native u a ha ha1 hr)
    (FirstHalfInteriorFaceDomain.toInterior u a ha ha1 r z.val)
  change FirstHalfInteriorTested.sourceMap u a ha ha1 hr
    (FirstHalfInteriorFaceDomain.toInterior u a ha ha1 r z.val) = _
  exact ht.symm.trans (congrArg (SupportedSelfCut.tested n hr) he.symm)

theorem homology_eq {K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (k p : ℕ)
    (c : ∀ q, K.X (k + (p + q)) ⟶ (chains (boundedCut u a ha ha1 hr F A)).X q)
    (hc : ∀ q, c (q + 1) ≫ (chains (boundedCut u a ha ha1 hr F A)).d (q + 1) q =
      K.d (k + (p + (q + 1))) (k + (p + q)) ≫ c q) (q : ℕ) :
    ((NestedCapHomology.operation k p c hc).post (push (retained u a ha ha1 hr F A))).homology q =
      ((NestedCapHomology.operation k p c hc).post (push (endpoint u a ha ha1 hr F A 1))).homology q := by
  have he := ((FirstHalfInteriorPrism.homotopy u a ha ha1 hr F A).toSSet.chainComplexMap coeff).homologyMap_eq q
  rw [← retained_zero, endpoint, endpoint, push_comp, push_comp,
    DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.post_homology]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
  simpa only [push, JoinedFilteredCap.sublevel] using
    congrArg (fun g => (NestedCapHomology.operation k p c hc).homology q ≫
      HomologicalComplex.homologyMap (push (toInterior u a ha ha1 hr F A)) q ≫ g) he

theorem capped_prism_boundary {K : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {d : ℕ}
    (c : DegreeLoweringHomology.Map K (chains (boundedCut u a ha ha1 hr F A)) d) (q : ℕ) :
    K.iCycles (d + q) ≫
      ((c.post (push (retained u a ha ha1 hr F A))).component q -
       (c.post (push (endpoint u a ha ha1 hr F A 1))).component q) =
      (K.iCycles (d + q) ≫ c.component q ≫ (push (toInterior u a ha ha1 hr F A)).f q ≫
        FirstHalfInteriorPrism.prism u a ha ha1 hr F A q) ≫
          (chains (TopCat.of (JoinedFilteredCap.sublevel F A))).d (q + 1) q := by
  let c' := c.post (push (toInterior u a ha ha1 hr F A))
  have hh := congrArg (fun g => c'.cycles q ≫ g)
    (FirstHalfInteriorPrism.prism_boundary u a ha ha1 hr F A q)
  simp only [← Category.assoc] at hh
  rw [c'.cycles_i] at hh
  rw [← retained_zero]
  simpa only [endpoint, push_comp, HomologicalComplex.comp_f,
    DegreeLoweringHomology.Map.post, Preadditive.comp_sub, Category.assoc, c',
    JoinedFilteredCap.sublevel] using hh.symm

end
end Finsler.FirstHalfBoundedCapDeformation
