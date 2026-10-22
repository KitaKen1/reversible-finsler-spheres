module

public import Finsler.Topology.OriginalSecondHalfBoundedFactors
public import Finsler.Topology.SupportedSelfCutAdequacy

/-! Restrict the original literal zero extensions to the actual bounded
second-half cut domain. They are exactly the specified annular Thom and
tested-loop pullbacks used by the normalized shuffle-vanishing component.
No global closure of either extension is assumed. -/

@[expose] public section
namespace Finsler.OriginalSecondHalfExtensions

open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.OriginalSecondHalfBoundedFactors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric n) (A : ℝ)

def toOuter : TopCat.of (bounded α β K hK r hr F A) ⟶ TopCat.of K :=
  TopCat.ofHom ⟨fun z => ⟨z.val.val, z.val.property.1⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

theorem source_outer : source α β K hK r hr F A =
    toOuter α β K hK r hr F A ≫ SupportedCap.subspaceMap (TopCat.of (P × (ClosedInterval × Q))) K := by
  ext z : 1
  rfl

theorem outer_evaluation : toOuter α β K hK r hr F A ≫
    OriginalSecondHalfFamily.family α β K hK ≫ selfEvaluation n = evaluation α β K hK r hr F A := by
  ext z : 1
  rfl

theorem thom_extension_pullback (hn : 1 ≤ n) {δ ρ : ℝ}
    (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) :
    cochainPullback (source α β K hK r hr F A) n
      (SupportedSelfCutAdequacy.extension K
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit n
        (AnnularSelfCut.cocycle n hn h)) =
      cochainPullback (evaluation α β K hK r hr F A) n (AnnularThomCocycle.ambient n hn h) := by
  unfold SupportedSelfCutAdequacy.extension
  rw [source_outer, SupportedCapNaturality.pullback_comp, TubeCochainExtension.restriction]
  simp only [AnnularSelfCut.cocycle, ← SupportedCapNaturality.pullback_comp, Category.assoc]
  rw [outer_evaluation]

theorem tested_extension_pullback (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback (source α β K hK r hr F A) p
      (SelfCutParameterFamily.testedExtension K
        (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
        (fun _ => r) (fun _ => hr) PUnit.unit p T) =
      cochainPullback (domainProjection α β K hK r hr F A ≫
        OriginalSecondHalfFamily.cutMap α β K hK r) p (NormalizedSelfCut.testedCocycle n p hr T) := by
  unfold SelfCutParameterFamily.testedExtension source
  rw [SupportedCapNaturality.pullback_comp]
  unfold OriginalSecondHalfFamily.domain
  rw [TubeCochainExtension.restriction]
  simp only [SelfCutParameterFamily.testedMap, OriginalSecondHalfFamily.cutMap,
    NormalizedSelfCut.testedCocycle, ← SupportedCapNaturality.pullback_comp, Category.assoc]

end
end Finsler.OriginalSecondHalfExtensions
