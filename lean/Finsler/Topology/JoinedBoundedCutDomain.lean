module

public import Finsler.Topology.JoinedCochainBoundary
public import Finsler.Topology.PartialDoubleCapDomainFiltered

/-! One rectangle scale, chosen before all cochain degrees and thresholds,
lifts the actual two successive caps to the length-bounded cut domain.
The local tested-cochain boundary identity suffices; its zero extension
is not assumed to be globally closed. -/

@[expose] public section
namespace Finsler.JoinedBoundedCutDomain

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2200000

theorem exists_closed_domain_operators {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      (∀ (i : Fin 3) center,
        JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ i ∨
        JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i) ∧
      ∀ (i : Fin 3) (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainCoboundary (ZMod 2) (parameters n) k φ = 0)
      (hfar : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
      (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      let Z := TopCat.of (Outer X)
      let D := domain (tube X) (family u a ha ha1) (fun _ => r) i
      let f := retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i
      let B := JoinedFilteredCap.sublevel F (A - L + 3 * ε)
      let E := PartialDoubleCapDomainFiltered.boundedDomain Z (TopCat.of (SphereLoop n)) D f B
      ∃ e : ∀ q, (small Z (JoinedFilteredCap.rectangleCover X η)).X (k + (p + q)) ⟶
          (chains (TopCat.of E)).X q,
      ∀ q,
        (e q ≫ (push (SupportedCap.subspaceMap (TopCat.of D) E)).f q ≫
          (push (SupportedCap.subspaceMap Z D)).f q =
          (inclusion Z (JoinedFilteredCap.rectangleCover X η)).f (k + (p + q)) ≫
            PartialDoubleCap.cap Z k p q
              (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
              (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T)) ∧
        (e (q + 1) ≫ (chains (TopCat.of E)).d (q + 1) q =
          (small Z (JoinedFilteredCap.rectangleCover X η)).d
            (k + (p + (q + 1))) (k + (p + q)) ≫ e q) := by
  have htwo : 2 * ρ < r := by linarith
  obtain ⟨η₀, hη₀, hη₀b, hrefine⟩ := JoinedRectangleRefinement.exists_scale u a ha ha1 hρ htwo hb
  obtain ⟨η, hη, hηη₀, had⟩ := JoinedCapAdequacy.exists_filtered_scale F u a ha ha1
    hρ hρr hr hε hη₀ hradius
  have hW : ∀ (i : Fin 3) center,
      JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha ha1 ρ i ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha ha1) (fun _ => r) i := by
    intro i center
    rcases hrefine i center with hf | hn
    · exact Or.inl ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hf)
    · exact Or.inr ((JoinedRectangleRefinement.rectangleCover_mono hηη₀ center).trans hn)
  refine ⟨η, hη, hηη₀.trans hη₀b, hW, ?_⟩
  intro i k p L A φ hφ hfar T hT hshort hA
  let Z := TopCat.of (Outer X)
  let W := JoinedFilteredCap.rectangleCover X η
  let D := domain (tube X) (family u a ha ha1) (fun _ => r) i
  let f := retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i
  let B := JoinedFilteredCap.sublevel F (A - L + 3 * ε)
  let φ' := SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ
  let ψ' := testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T
  have hgood : ∀ q (σ : (Z.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
      (TopCat.toSSet.obj Z).ιChainComplex σ.val ≫ PartialDoubleCap.cap Z k p q φ' ψ' ≠ 0 →
      ∀ z ∈ Set.range (Z.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ B := by
    intro q σ hcap z hz
    obtain ⟨center, hc⟩ := (TopCat.mem_smallSingularSubcomplex_iff Z W σ.val).mp σ.property
    have hcap' : ((TopCat.toSSet.obj Z).ιChainComplex σ.val ≫
        RelativeCapAssociativity.absoluteChain Z k (p + q) (k + (p + q)) rfl φ') ≫
          RelativeCapAssociativity.absoluteChain Z p q (p + q) rfl ψ' ≠ 0 := by
      simpa only [PartialDoubleCap.cap, Category.assoc] using hcap
    exact had center.1 center.2 (Set.range (Z.toSSetObjEquiv _ σ.val)) hc i k p q L A φ hfar T hshort
      (fun w _ => hA w.2) σ.val Set.Subset.rfl hcap' z hz
  have hcap := JoinedCochainBoundary.boundary u a ha ha1 η ρ r hr i (hW i) k p φ hφ hfar T hT
  have hcomm : ∀ q, ((inclusion Z W).f (k + (p + (q + 1))) ≫
      PartialDoubleCap.cap Z k p (q + 1) φ' ψ') ≫ (chains Z).d (q + 1) q =
        (small Z W).d (k + (p + (q + 1))) (k + (p + q)) ≫
          ((inclusion Z W).f (k + (p + q)) ≫ PartialDoubleCap.cap Z k p q φ' ψ') := by
    intro q
    simpa only [Category.assoc] using hcap q
  refine ⟨PartialDoubleCapDomainFiltered.component Z (TopCat.of (SphereLoop n)) W D f B
    k p φ' ψ' hgood, ?_⟩
  intro q
  exact ⟨PartialDoubleCapDomainFiltered.source_inclusion Z _ W D f B k p φ' ψ' hgood q,
    PartialDoubleCapDomainFiltered.component_boundary Z _ W D f B k p φ' ψ' hgood hcomm q⟩

end
end Finsler.JoinedBoundedCutDomain
