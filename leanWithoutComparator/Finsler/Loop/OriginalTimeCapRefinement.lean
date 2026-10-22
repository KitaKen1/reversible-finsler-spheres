module

public import Finsler.Loop.TimeCoverRefinementComparison
public import Finsler.Topology.OriginalSecondHalfTimeOperation
public import Finsler.Topology.SuccAlignmentNaturality
import all Finsler.Topology.OriginalSecondHalfTimeOperation

/-! The actual original bounded time operation is unchanged on homology
when its source cover and bounded three-cap are refined together.
The common endpoint cover controls the relative double-prism term. -/

@[expose] public section
namespace Finsler.OriginalTimeCapRefinement

open CategoryTheory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SelfCutThomCocycle Finsler.ThreeCapBlockVanishing
open Finsler.OriginalSecondHalfBoundedFactors

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {s : ℕ}
  (α : C(P, SphereLoop (s + 1))) (β : C(Q, SphereLoop (s + 1)))
  (K : Set (P × (ClosedInterval × Q)))
  (hK : ∀ z : K, dist (basepoint (α z.val.1)) (basepoint (β z.val.2.2)) < 1)
  (r : ℝ) (hr : r ≤ 1) (F : ReversibleMetric (s + 1)) (B : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (a p : ℕ)
  (J : singularCochainGroup (ZMod 2) (TopCat.of (P × (ClosedInterval × Q))) a)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (s + 1))) p)

def Source {ι : Type*} (W : ι → Set (P × (ClosedInterval × Q)))
    (u : DegreeLoweringHomology.Map (small (TopCat.of (P × (ClosedInterval × Q))) W)
      (chains (TopCat.of (bounded α β K hK r hr F B))) (a + (s + 1) + p)) : Prop :=
  ∀ q, u.component q ≫ (push (source α β K hK r hr F B)).f q =
    (inclusion (TopCat.of (P × (ClosedInterval × Q))) W).f (a + (s + 1) + p + q) ≫
      threeCap (TopCat.of (P × (ClosedInterval × Q))) a (s + 1) p q J
        (SupportedSelfCutAdequacy.extension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK) PUnit.unit (s + 1)
          (AnnularSelfCut.cocycle (s + 1) (by omega) h))
        (SelfCutParameterFamily.testedExtension K
          (fun _ : PUnit.{1} => OriginalSecondHalfFamily.family α β K hK)
          (fun _ => r) (fun _ => hr) PUnit.unit p T)

variable {ι : Type*} (W : ι → Set (P × (ClosedInterval × Q)))
  (hW : ∀ i, IsOpen (W i)) (hcW : ⋃ i, W i = Set.univ)
  (u : DegreeLoweringHomology.Map (small (TopCat.of (P × (ClosedInterval × Q))) W)
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + (s + 1) + p))
  (hu : Source α β K hK r hr F B h a p J T W u)

theorem component_normal (q : ℕ) :
    (OriginalSecondHalfTimeOperation.operation α β K hK r hr F B W hW hcW h a p J T u hu).component q =
      (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom ((a + s + p) + q) ((a + s + p) + q + 1) ≫
        (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff W hW hcW).f
          ((a + s + p) + q + 1) ≫ DegreeLoweringSuccAlignment.align (a + s + p) u (by omega) q := by
  change (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q)).hom _ _ ≫ _ = _
  have he := SuccAlignmentNaturality.nested_pre
    (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff W hW hcW) a s p u q
  rw [show ClosedCapDegreeTransport.align (a + s) p
      (OriginalSecondHalfTimeOperation.nested α β K hK r hr F B W hW hcW a p u) q =
      (smallSingularRetraction (X := TopCat.of (P × (ClosedInterval × Q))) coeff W hW hcW).f
        ((a + s + p) + q + 1) ≫ DegreeLoweringSuccAlignment.align (a + s + p) u (by omega) q from he]

variable {κ : Type*} (U : κ → Set (P × (ClosedInterval × Q))) (t : κ → ι)
  (href : ∀ i, U i ⊆ W (t i))
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)

def refined : DegreeLoweringHomology.Map (small (TopCat.of (P × (ClosedInterval × Q))) U)
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + (s + 1) + p) :=
  u.pre (SmallRefinementComparison.refinement (X := TopCat.of (P × (ClosedInterval × Q))) U W t href)

include hu in
theorem refined_source : Source α β K hK r hr F B h a p J T U
    (refined α β K hK r hr F B a p W u U t href) := by
  intro q
  dsimp only [refined, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, hu q, ← Category.assoc, ← HomologicalComplex.comp_f,
    SmallRefinementComparison.refinement_inclusion]

def fineOperation : DegreeLoweringHomology.Map (chains (TopCat.of (P × Q)))
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + s + p) :=
  OriginalSecondHalfTimeOperation.operation α β K hK r hr F B U hU hcU h a p J T
    (refined α β K hK r hr F B a p W u U t href)
    (refined_source α β K hK r hr F B h a p J T W u hu U t href)

theorem homology_eq (q : ℕ) :
    (OriginalSecondHalfTimeOperation.operation α β K hK r hr F B W hW hcW h a p J T u hu).homology q =
      (fineOperation α β K hK r hr F B h a p J T W u hu U t href hU hcU).homology q := by
  apply TimeCoverRefinementComparison.homology_eq U W t href hU hcU hW hcW
    (TopCat.of (P × Q)) (OriginalSecondHalfEndpointZero.face 0) (OriginalSecondHalfEndpointZero.face 1)
    (OriginalSecondHalfTimeOperation.prism (P := P) (Q := Q))
    (chains (TopCat.of (bounded α β K hK r hr F B))) (a + s + p)
    (DegreeLoweringSuccAlignment.align (a + s + p) u (by omega))
    (DegreeLoweringSuccAlignment.comm (a + s + p) u (by omega))
  · exact component_normal α β K hK r hr F B h a p J T W hW hcW u hu
  · intro q
    have he := component_normal α β K hK r hr F B h a p J T U hU hcU
      (refined α β K hK r hr F B a p W u U t href)
      (refined_source α β K hK r hr F B h a p J T W u hu U t href) q
    dsimp only [refined] at he
    rw [DegreeLoweringSuccAlignment.pre] at he
    simpa only [fineOperation, refined, HomologicalComplex.comp_f, Category.assoc] using he

end
end Finsler.OriginalTimeCapRefinement
