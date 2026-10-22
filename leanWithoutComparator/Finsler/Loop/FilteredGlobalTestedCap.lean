module

public import Finsler.Loop.FilteredGlobalThomTime
public import Finsler.Loop.FilteredSelfCutTimeFactor

/-! Actual tested caps commute with the incoming near-space inclusion.
The genuine length-control approximation is removed only in homology. -/

@[expose] public section
namespace Finsler.FilteredGlobalTestedCap
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m p : ℕ) (F : ReversibleMetric (m + 1)) {r ε a L : ℝ}
  (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem absolute_component (q : ℕ) :
    (SupportedCapHomology.absoluteOperation (FilteredTestedCap.space F r a) p
      (FilteredTestedCap.cochain F hr a p T) (FilteredTestedCap.cochain_closed F hr a p T hT)).component q ≫
      (push (FilteredTestedCap.retainedMap F hr a)).f q =
    (push (FilteredTestedCap.inclusion F r a)).f (p + q) ≫
      (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).component q := by
  let i := FilteredTestedCap.inclusion F r a
  let ψ := NormalizedSelfCut.testedCocycle (m + 1) p hr T
  have hn : RelativeCapAssociativity.absoluteChain (FilteredTestedCap.space F r a) p q (p + q) rfl
      (cochainPullback i p ψ) ≫ (push i).f q =
    (push i).f (p + q) ≫ RelativeCapAssociativity.absoluteChain
      (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) p q (p + q) rfl ψ :=
    RelativeCapBoundary.absolute_chain_natural i p q (p + q) rfl ψ
  change RelativeCapAssociativity.absoluteChain (FilteredTestedCap.space F r a) p q (p + q) rfl
    (cochainPullback i p ψ) ≫ (push (i ≫ TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr))).f q =
      (push i).f (p + q) ≫ (RelativeCapAssociativity.absoluteChain
        (TopCat.of (SupportedSelfCut.neighborhood (m + 1) r)) p q (p + q) rfl ψ ≫
          (push (TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr))).f q)
  rw [push_comp, HomologicalComplex.comp_f, ← Category.assoc, hn, Category.assoc]

theorem absolute_homology (q : ℕ) :
    (SupportedCapHomology.absoluteOperation (FilteredTestedCap.space F r a) p
      (FilteredTestedCap.cochain F hr a p T) (FilteredTestedCap.cochain_closed F hr a p T hT)).homology q ≫
      HomologicalComplex.homologyMap (push (FilteredTestedCap.retainedMap F hr a)) q =
    HomologicalComplex.homologyMap (push (FilteredTestedCap.inclusion F r a)) (p + q) ≫
      (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).homology q := by
  have h := DegreeLoweringHomology.Map.homology_eq_of_components
    ((SupportedCapHomology.absoluteOperation (FilteredTestedCap.space F r a) p
      (FilteredTestedCap.cochain F hr a p T) (FilteredTestedCap.cochain_closed F hr a p T hT)).post
        (push (FilteredTestedCap.retainedMap F hr a)))
    ((NormalizedSelfCut.testedOperation (m + 1) p hr T hT).pre (push (FilteredTestedCap.inclusion F r a)))
    (absolute_component m p F hr T hT (a := a)) q
  rw [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.pre_homology] at h
  exact h

theorem homology (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0) (q : ℕ) :
    (FilteredSelfCutTimeFactor.testedMap m p F hr hε hrr T hT hshort (a := a)).homology q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε)))) q =
    HomologicalComplex.homologyMap (push (FilteredGlobalThomTime.nearMap m F a r)) (p + q) ≫
      (NormalizedSelfCut.testedOperation (m + 1) p hr T hT).homology q := by
  rw [FilteredSelfCutTimeFactor.testedMap, DegreeLoweringHomology.Map.pre_homology, Category.assoc,
    FilteredTestedCap.homology_inclusion, absolute_homology m p F hr T hT q]
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, ← push_comp]
  rfl

end
end Finsler.FilteredGlobalTestedCap
