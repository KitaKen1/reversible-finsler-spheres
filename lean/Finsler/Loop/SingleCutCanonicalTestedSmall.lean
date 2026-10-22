module

public import Finsler.Loop.SingleCutCanonicalIncoming

/-! The actual canonical tested cap restricts literally to its own
oscillation small chains. On the common proper domain its real short
output has the genuine tested-cap/kept-loop source formula. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalTestedSmall

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {m : ℕ} (F : ReversibleMetric (m + 1)) {R ε a L : ℝ}
  (hR : R ≤ 1) (hε : 0 < ε) (hRR : R ≤ SelfCutLengthControl.radius F hε) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

theorem restriction (q : ℕ) :
    (inclusion (FilteredTestedCap.space F R a) (FilteredTestedCap.cover F hR a ε)).f (p + q) ≫
      (FilteredTestedCap.operation F hR hε hRR p T hT hshort).component q =
    (FilteredTestedCap.smallOperation F hR hε hRR p T hT hshort).component q := by
  dsimp only [FilteredTestedCap.operation, DegreeLoweringHomology.Map.pre]
  rw [← Category.assoc, ← HomologicalComplex.comp_f,
    TauCeti.ι_comp_smallSingularRetraction, HomologicalComplex.id_f, Category.id_comp]

variable {P : Type} [PseudoMetricSpace P]
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (hrR : r < R)
  (hA : ∀ x, SobolevLength.length F (α x) < a)

def operation := (FilteredTestedCap.smallOperation F hR hε hRR p T hT hshort).pre
  (SingleCutCanonicalIncoming.smallMap α r F a R hrR hA hR ε)

theorem component_source (q : ℕ) :
    (operation F hR hε hRR p T hT hshort α r hrR hA).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε)))).f q =
    (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)).f (p + q) ≫
      absoluteChain (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) p q (p + q) rfl
        (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T) ≫
      (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr))).f q := by
  have hs := CapOutputSupport.component_inclusion (FilteredTestedCap.cover F hR a ε)
    (FilteredTestedCap.retainedMap F hR a) (SelfCutOscillation.short F (a - L + 3 * ε)) p
    (FilteredTestedCap.cochain F hR a p T)
    (fun q s => FilteredTestedCap.parent_output F hR hε hRR p q T hshort s) q
  have hn := RelativeCapBoundary.absolute_chain_natural
    (SingleCutCanonicalIncoming.incoming α r F a R hrR hA) p q (p + q) rfl
    (FilteredTestedCap.cochain F hR a p T)
  change absoluteChain _ p q (p + q) rfl (cochainPullback _ p _) ≫
    (push (SingleCutCanonicalIncoming.incoming α r F a R hrR hA)).f q =
    (push (SingleCutCanonicalIncoming.incoming α r F a R hrR hA)).f (p + q) ≫
      absoluteChain _ p q (p + q) rfl _ at hn
  rw [SingleCutCanonicalIncoming.cochain_source α r hr F a R hrR hA hR p T] at hn
  dsimp only [operation, DegreeLoweringHomology.Map.pre, FilteredTestedCap.smallOperation,
    CapOutputSupport.operation]
  rw [Category.assoc, hs, ← Category.assoc,
    ← HomologicalComplex.comp_f, SingleCutCanonicalIncoming.smallMap_source, HomologicalComplex.comp_f]
  simp only [Category.assoc]
  calc
    _ = (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
        (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)).f (p + q) ≫
        absoluteChain (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) p q (p + q) rfl
          (cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T) ≫
        (push (SingleCutCanonicalIncoming.incoming α r F a R hrR hA)).f q ≫
        (push (FilteredTestedCap.retainedMap F hR a)).f q := by
      simpa only [Category.assoc] using congrArg (fun k =>
        (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
          (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)).f (p + q) ≫ k ≫
          (push (FilteredTestedCap.retainedMap F hR a)).f q) hn.symm
    _ = _ := by
      rw [← HomologicalComplex.comp_f, ← push_comp,
        SingleCutCanonicalIncoming.retained_square α r hr F a R hrR hA hR]

end
end Finsler.SingleCutCanonicalTestedSmall
