module

public import Finsler.Loop.FilteredGlobalTestedCap
public import Finsler.Loop.GlobalSelfCutTimeFactor
public import Finsler.Loop.FilteredCanonicalCutPairing

/-! The original filtered self-cut, followed by its genuine output
inclusion, agrees on homology with the original GLOBAL prism self-cut
after input inclusion. The length output remains a-L+3epsilon. -/

@[expose] public section
namespace Finsler.FilteredGlobalSelfCut
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

private theorem cast_homology {C D : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⟶ D) {i j : ℕ} (h : i = j) :
    eqToHom (congrArg (fun k => C.homology k) h) ≫ HomologicalComplex.homologyMap f j =
      HomologicalComplex.homologyMap f i ≫ eqToHom (congrArg (fun k => D.homology k) h) := by
  subst j
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem homology (m p : ℕ) (F : ReversibleMetric (m + 1)) {ρ r ε a L : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hε : 0 < ε)
    (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0) (q : ℕ) :
    (FilteredPrismSelfCut.operation m p F hρ hρr hr hε hrr T hT hshort (a := a)).homology q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε)))) q =
    HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F a))) ((m + p) + q) ≫
        (PrismSelfCut.operation m p hρ hρr hr T hT).homology q := by
  rw [← FilteredSelfCutTimeFactor.homology m p F hρ hρr hr hε hrr T hT hshort q,
    FilteredSelfCutTimeFactor.composed, DegreeLoweringComposition.homology]
  simp only [Category.assoc]
  rw [FilteredGlobalTestedCap.homology m p F hr T hT hε hrr hshort q,
    ← Category.assoc ((FilteredThomSupportRadius.operation m F a hρ hρr).homology (p + q)),
    FilteredGlobalThomTime.homology m F a hρ hρr (p + q)]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom _) (HomologicalComplex.homologyMap _ _), cast_homology]
  simp only [Category.assoc]
  rw [← DegreeLoweringComposition.homology,
    ← GlobalSelfCutTimeFactor.composed, GlobalSelfCutTimeFactor.homology]
  omega

theorem canonical_homology (m p : ℕ) (F : ReversibleMetric (m + 1)) {ε a L : ℝ}
    (hε : 0 < ε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0) (q : ℕ) :
    (FilteredCanonicalCutPairing.operation m p F hε T hT hshort (a := a)).homology q =
    HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F a))) ((m + p) + q) ≫
    (PrismSelfCut.operation m p (half_pos (SelfCutLengthControl.radius_spec F hε).1)
      (half_lt_self (SelfCutLengthControl.radius_spec F hε).1)
      (SelfCutLengthControl.radius_spec F hε).2.1 T hT).homology q := by
  rw [FilteredCanonicalCutPairing.operation, DegreeLoweringHomology.Map.post_homology]
  exact homology m p F (half_pos (SelfCutLengthControl.radius_spec F hε).1)
    (half_lt_self (SelfCutLengthControl.radius_spec F hε).1)
    (SelfCutLengthControl.radius_spec F hε).2.1 hε le_rfl T hT hshort q

end
end Finsler.FilteredGlobalSelfCut
