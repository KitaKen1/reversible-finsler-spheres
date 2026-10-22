module

public import Finsler.Topology.TimeShuffleComparison
public import Finsler.Topology.PrismSelfCut
public import Finsler.Topology.FilteredPrismSelfCut

/-! Apply the genuine singular shuffle comparison to both actual self-cut
constructions. These are chain equalities, including coefficient multiplication.
Support-controlled comparison of the remaining cap/refinement choices,
the original join and interchange remain separate. -/

@[expose] public section
namespace Finsler.SelfCutShuffle

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SelfCutOscillation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem prism_eq_shuffle (n q : ℕ) :
    SelfCutTimePrism.prism n q = TimeShuffleComparison.rectangle (SelfCutTimePrism.cylinder n) q :=
  (TimeShuffleComparison.rectangle_eq_prism (SelfCutTimePrism.cylinder n) q).symm

theorem operation_eq_shuffle (m p : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0) (q : ℕ) :
    (PrismSelfCut.operation m p hρ hρr hr T hT).component q =
      TimeShuffleComparison.rectangle (SelfCutTimePrism.cylinder (m + 1)) ((m + p) + q) ≫
        PrismSelfCut.cut m p hρ hρr hr T hT q := by
  change ((SelfCutTimePrism.cylinder (m + 1)).toSSet.chainComplexMap coeff).hom
      ((m + p) + q) ((m + p) + q + 1) ≫ PrismSelfCut.cut m p hρ hρr hr T hT q = _
  rw [TimeShuffleComparison.rectangle_eq_prism]

theorem filtered_prism_eq_shuffle {n : ℕ} (F : ReversibleMetric n) (a : ℝ) (q : ℕ) :
    ((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom q (q + 1) =
      TimeShuffleComparison.rectangle (FilteredPrismSelfCut.cylinder F a) q :=
  (TimeShuffleComparison.rectangle_eq_prism (FilteredPrismSelfCut.cylinder F a) q).symm

theorem filtered_operation_eq_shuffle (m p : ℕ) (F : ReversibleMetric (m + 1)) {ρ r ε a L : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (hε : 0 < ε) (hrr : r ≤ SelfCutLengthControl.radius F hε)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hclosed : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (hT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (short F L)) p T = 0) (q : ℕ) :
    (FilteredPrismSelfCut.operation m p F hρ hρr hr hε hrr T hclosed hT (a := a)).component q =
      TimeShuffleComparison.rectangle (FilteredPrismSelfCut.cylinder F a) ((m + p) + q) ≫
        FilteredPrismSelfCut.indexedCut m p F hρ hρr hr hε hrr T hclosed hT q := by
  change ((FilteredPrismSelfCut.cylinder F a).toSSet.chainComplexMap coeff).hom
      ((m + p) + q) ((m + p) + q + 1) ≫
        FilteredPrismSelfCut.indexedCut m p F hρ hρr hr hε hrr T hclosed hT q = _
  rw [TimeShuffleComparison.rectangle_eq_prism]

end
end Finsler.SelfCutShuffle
