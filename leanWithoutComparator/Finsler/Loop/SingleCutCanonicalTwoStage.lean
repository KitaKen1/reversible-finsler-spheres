module

public import Finsler.Loop.SingleCutCanonicalThomSmallLift
public import Finsler.Loop.SingleCutCanonicalTestedSmall
public import Finsler.Loop.DegreeLoweringComposition

/-! The genuine canonical two-stage filtered cut on an actual common
compact-family small cover. Both canonical subdivisions disappear
literally on these small inputs. The unrestricted canonical family
time operation has its original-cylinder prism formula. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalTwoStage

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.FirstInputSelfCutCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ)
  (F : ReversibleMetric (m + 1)) (a R : ℝ) (hrR : r < R)
  (hA : ∀ x, SobolevLength.length F (α x) < a) (hR : R ≤ 1) (ε : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
  (hε : 0 < ε) (hRR : R ≤ SelfCutLengthControl.radius F hε) (L : ℝ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

def nested (q : ℕ) :=
  (SingleCutCanonicalThomSmallLift.testedSmall α r F a R hrR hA hR ε h).component (p + q) ≫
    (FilteredTestedCap.smallOperation F hR hε hRR p T hT hshort).component q

theorem nested_boundary (q : ℕ) :
    nested α r F a R hrR hA hR ε h hε hRR L p T hT hshort (q + 1) ≫
      (chains (TopCat.of (SelfCutOscillation.short F (a - L + 3 * ε)))).d (q + 1) q =
    (small (ambient α) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)).d
      ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫
      nested α r F a R hrR hA hR ε h hε hRR L p T hT hshort q := by
  dsimp only [nested]
  have hf :
      (SingleCutCanonicalThomSmallLift.testedSmall α r F a R hrR hA hR ε h).component (p + (q + 1)) ≫
        (small (FilteredTestedCap.space F R a) (FilteredTestedCap.cover F hR a ε)).d (p + (q + 1)) (p + q) =
      (small (ambient α) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫
        (SingleCutCanonicalThomSmallLift.testedSmall α r F a R hrR hA hR ε h).component (p + q) := by
    rw [← Nat.add_assoc p q 1]
    exact (SingleCutCanonicalThomSmallLift.testedSmall α r F a R hrR hA hR ε h).comm (p + q)
  rw [Category.assoc, (FilteredTestedCap.smallOperation F hR hε hRR p T hT hshort).comm,
    ← Category.assoc, hf, Category.assoc]

theorem nested_canonical (hρr : ρ < r) (q : ℕ) :
    nested α r F a R hrR hA hR ε h hε hRR L p T hT hshort q =
    (inclusion (ambient α) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)).f ((m + 1) + (p + q)) ≫
      (push (CompactInputShortMaps.cylinder α F a hA)).f ((m + 1) + (p + q)) ≫
      FilteredPrismSelfCut.chainCut (by omega) F (h.1.trans h.2.2) (hρr.trans hrR) hR hε hRR p T hT hshort q := by
  dsimp only [nested]
  rw [← SingleCutCanonicalTestedSmall.restriction F hR hε hRR p T hT hshort q,
    ← Category.assoc, SingleCutCanonicalThomSmallLift.testedSmall_component α r F a R hrR hA hR ε h hρr (p + q)]
  simp only [FilteredPrismSelfCut.chainCut, Category.assoc]

def operation := DegreeLoweringComposition.compose
  (SingleCutCanonicalThomSmallLift.testedSmall α r F a R hrR hA hR ε h)
  (FilteredTestedCap.smallOperation F hR hε hRR p T hT hshort)

theorem component_canonical (hρr : ρ < r) (q : ℕ) :
    (operation α r F a R hrR hA hR ε h hε hRR L p T hT hshort).component q =
    eqToHom (congrArg (small (ambient α)
      (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)).X
      (Nat.add_assoc (m + 1) p q)) ≫
    (inclusion (ambient α) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)).f ((m + 1) + (p + q)) ≫
      (push (CompactInputShortMaps.cylinder α F a hA)).f ((m + 1) + (p + q)) ≫
      FilteredPrismSelfCut.chainCut (by omega) F (h.1.trans h.2.2) (hρr.trans hrR) hR hε hRR p T hT hshort q := by
  have hh := nested_canonical α r F a R hrR hA hR ε h hε hRR L p T hT hshort hρr q
  simpa only [operation, DegreeLoweringComposition.component, nested, Category.assoc] using
    congrArg (fun k => eqToHom (congrArg (small (ambient α)
      (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)).X
      (Nat.add_assoc (m + 1) p q)) ≫ k) hh

def familyOperation (hρr : ρ < R) :=
  (FilteredPrismSelfCut.operation m p F (h.1.trans h.2.2) hρr hR hε hRR T hT hshort).pre
    (push (CompactInputShortMaps.family α F a hA))

theorem family_component (hρr : ρ < R) (q : ℕ) :
    (familyOperation α F a R hA hR ε h hε hRR L p T hT hshort hρr).component q =
    AnnularTimeTrim.prism (TopCat.of P) ((m + p) + q) ≫
      (push (CompactInputShortMaps.cylinder α F a hA)).f (((m + p) + q) + 1) ≫
      FilteredPrismSelfCut.indexedCut m p F (h.1.trans h.2.2) hρr hR hε hRR T hT hshort q := by
  change (push (CompactInputShortMaps.family α F a hA)).f ((m + p) + q) ≫
    (((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom ((m + p) + q) (((m + p) + q) + 1) ≫ _) = _
  rw [← Category.assoc, CompactInputShortMaps.prism_square, Category.assoc]

end
end Finsler.SingleCutCanonicalTwoStage
