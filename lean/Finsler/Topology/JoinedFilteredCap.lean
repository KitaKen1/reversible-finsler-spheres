module

public import Finsler.Topology.JoinedCapAdequacy
public import Finsler.Topology.PartialDoubleCapFiltered
public import Finsler.Topology.SmallRectangleShuffle

/-! One factorwise scale gives actual linear successive-cap operations
through the actual cut domain and retained-length sublevel for the full
joined cylinder and both trim homotopies. The original supported cut and
its subdivision comparisons still require identification. -/

@[expose] public section
namespace Finsler.JoinedFilteredCap

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def sublevel {n : ℕ} (F : ReversibleMetric n) (B : ℝ) : Set (SphereLoop n) :=
  {w | length F w < B}

def rectangleCover (X : Type) [PseudoMetricSpace X] (η : ℝ) :
    (ClosedInterval × ClosedInterval) × X → Set (Outer X) :=
  SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × ClosedInterval)) (Y := TopCat.of X)
    (PairDistanceCover.cover (id : ClosedInterval × ClosedInterval → ClosedInterval × ClosedInterval) η)
    (PairDistanceCover.cover (id : X → X) η)

theorem exists_filtered_operators {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (F : ReversibleMetric n) (u : C(X, H1JoinContinuity.composable n))
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    {ρ r ε b : ℝ} (hρ : 0 < ρ) (hρr : 4 * ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hb : 0 < b) (hradius : r ≤ SelfCutLengthControl.radius F hε) :
    ∃ η > 0, η ≤ b ∧
      ∀ (i : Fin 3) (k p : ℕ) (L A : ℝ)
      (φ : singularCochainGroup (ZMod 2) (parameters n) k)
      (hφ : cochainPullback (SupportedCap.subspaceMap (parameters n) (exterior n ρ)) k φ = 0)
      (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p),
      cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (SelfCutOscillation.short F L)) p T = 0 →
      (∀ x, length F (u x).val.1 + length F (u x).val.2 < A) →
      ∃ (c : ∀ q, (small (TopCat.of (Outer X))
          (rectangleCover X η)).X
            (k + (p + q)) ⟶ (chains (TopCat.of (domain (tube X) (family u a ha ha1) (fun _ => r) i))).X q)
        (d : ∀ q, (small (TopCat.of (Outer X))
          (rectangleCover X η)).X
            (k + (p + q)) ⟶ (chains (TopCat.of (sublevel F (A - L + 3 * ε)))).X q),
      ∀ q,
        (c q ≫ (push (SupportedCap.subspaceMap (TopCat.of (Outer X))
          (domain (tube X) (family u a ha ha1) (fun _ => r) i))).f q =
          (inclusion (TopCat.of (Outer X))
            (rectangleCover X η)).f
              (k + (p + q)) ≫ PartialDoubleCap.cap (TopCat.of (Outer X)) k p q
                (SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ)
                (testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T)) ∧
        (d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (sublevel F (A - L + 3 * ε)))).f q =
          c q ≫ (push (retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i)).f q) := by
  obtain ⟨η, hη, hηb, had⟩ := JoinedCapAdequacy.exists_filtered_scale F u a ha ha1 hρ hρr hr hε hb hradius
  refine ⟨η, hη, hηb, ?_⟩
  intro i k p L A φ hφ T hT hA
  let Z := TopCat.of (Outer X)
  let W := rectangleCover X η
  let D := domain (tube X) (family u a ha ha1) (fun _ => r) i
  let f := retainedMap (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i
  let φ' := SupportedSelfCutAdequacy.extension (tube X) (family u a ha ha1) i k φ
  let ψ' := testedExtension (tube X) (family u a ha ha1) (fun _ => r) (fun _ => hr) i p T
  have hgood : ∀ q (σ : (Z.smallSingularSubcomplex W : SSet) _⦋k + (p + q)⦌),
      (TopCat.toSSet.obj Z).ιChainComplex σ.val ≫ PartialDoubleCap.cap Z k p q φ' ψ' ≠ 0 →
      ∀ z ∈ Set.range (Z.toSSetObjEquiv _ σ.val), ∃ hz : z ∈ D, f ⟨z, hz⟩ ∈ sublevel F (A - L + 3 * ε) := by
    intro q σ hcap z hz
    obtain ⟨center, hc⟩ := (TopCat.mem_smallSingularSubcomplex_iff Z W σ.val).mp σ.property
    have hcap' : ((TopCat.toSSet.obj Z).ιChainComplex σ.val ≫
        RelativeCapAssociativity.absoluteChain Z k (p + q) (k + (p + q)) rfl φ') ≫
          RelativeCapAssociativity.absoluteChain Z p q (p + q) rfl ψ' ≠ 0 := by
      simpa only [PartialDoubleCap.cap, Category.assoc] using hcap
    exact had center.1 center.2 (Set.range (Z.toSSetObjEquiv _ σ.val)) hc i k p q L A φ hφ T hT
      (fun w _ => hA w.2) σ.val Set.Subset.rfl hcap' z hz
  refine ⟨PartialDoubleCapFiltered.domainComponent Z (TopCat.of (SphereLoop n)) W D f
      (sublevel F (A - L + 3 * ε)) k p φ' ψ' hgood,
    PartialDoubleCapFiltered.outputComponent Z (TopCat.of (SphereLoop n)) W D f
      (sublevel F (A - L + 3 * ε)) k p φ' ψ' hgood, ?_⟩
  intro q
  exact ⟨PartialDoubleCapFiltered.domain_inclusion Z _ W D f _ k p φ' ψ' hgood q,
    PartialDoubleCapFiltered.output_inclusion Z _ W D f _ k p φ' ψ' hgood q⟩

end
end Finsler.JoinedFilteredCap
