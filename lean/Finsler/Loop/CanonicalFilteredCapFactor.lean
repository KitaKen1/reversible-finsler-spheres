module

public import Finsler.Loop.CanonicalFilteredLocalizedCap
public import Finsler.Topology.DegreeLoweringSuccAlignment
public import Finsler.Loop.LocalizedCapCupComponentSource

/-! The genuine canonical global two-stage cap factors through its
actual first retraction. The real compact-family common small cap
recovers that original cap with exact total-degree transports. -/

@[expose] public section
namespace Finsler.CanonicalFilteredCapFactor

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {m : ℕ} (F : ReversibleMetric (m + 1)) (a ρ R : ℝ)
  (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ 1) (ε : ℝ) (hε : 0 < ε)
  (hRR : R ≤ SelfCutLengthControl.radius F hε) (L : ℝ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

def original := DegreeLoweringComposition.compose
  (FilteredPrismSelfCut.thom (by omega) F a hρ hρR)
  (FilteredTestedCap.operation F hR hε hRR p T hT hshort)

theorem component_original (q : ℕ) :
    (original F a ρ R hρ hρR hR ε hε hRR L p T hT hshort).component q =
    eqToHom (congrArg (chains (FilteredPrismSelfCut.domain F a)).X (Nat.add_assoc (m + 1) p q)) ≫
      FilteredPrismSelfCut.chainCut (by omega) F hρ hρR hR hε hRR p T hT hshort q := rfl

theorem component_retraction (q : ℕ) :
    (original F a ρ R hρ hρR hR ε hε hRR L p T hT hshort).component q =
    (TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff
      (CanonicalFilteredLocalizedCap.cover F a ρ R) (CanonicalFilteredLocalizedCap.cover_open F a ρ R)
      (CanonicalFilteredLocalizedCap.cover_univ F a ρ R hρR)).f (((m + 1) + p) + q) ≫
      (CanonicalFilteredLocalizedCap.operation F a ρ R hρ hR ε hε hRR L p T hT hshort).component q := by
  rw [component_original, CanonicalFilteredLocalizedCap.chainCut_eq,
    CanonicalFilteredLocalizedCap.component_nested]
  have ht := LocalizedCapCupComponentSource.transport_f
    (TauCeti.smallSingularRetraction (X := FilteredPrismSelfCut.domain F a) coeff
      (CanonicalFilteredLocalizedCap.cover F a ρ R) (CanonicalFilteredLocalizedCap.cover_open F a ρ R)
      (CanonicalFilteredLocalizedCap.cover_univ F a ρ R hρR))
    (((m + 1) + p) + q) ((m + 1) + (p + q)) (Nat.add_assoc (m + 1) p q)
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ CanonicalFilteredLocalizedCap.nested F a ρ R hρ hR ε hε hRR L p T hT hshort q) ht

theorem actual_common {P : Type} [PseudoMetricSpace P]
    (α : C(P, SphereLoop (m + 1))) (hA : ∀ x, SobolevLength.length F (α x) < a)
    (r : ℝ) (hrR : r < R) {δ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (q : ℕ) :
    (SingleCutCanonicalTwoStage.operation α r F a R hrR hA hR ε h hε hRR L p T hT hshort).component q =
    (inclusion (TopCat.of (ClosedInterval × P)) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ) ≫
      push (CompactInputShortMaps.cylinder α F a hA)).f (((m + 1) + p) + q) ≫
      (original F a ρ R hρ (hρr.trans hrR) hR ε hε hRR L p T hT hshort).component q := by
  rw [SingleCutCanonicalTwoStage.component_canonical α r F a R hrR hA hR ε h hε hRR L p T hT hshort hρr q,
    component_original]
  have ht := LocalizedCapCupComponentSource.transport_f
    (inclusion (TopCat.of (ClosedInterval × P)) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ) ≫
      push (CompactInputShortMaps.cylinder α F a hA))
    (((m + 1) + p) + q) ((m + 1) + (p + q)) (Nat.add_assoc (m + 1) p q)
  simpa only [HomologicalComplex.comp_f, Category.assoc] using congrArg
    (fun k => k ≫ FilteredPrismSelfCut.chainCut (by omega) F hρ (hρr.trans hrR) hR hε hRR p T hT hshort q) ht

end
end Finsler.CanonicalFilteredCapFactor
