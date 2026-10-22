module

public import Finsler.Topology.FilteredBilinearLoopProduct
public import Finsler.Topology.SphereTopClass

/-! The genuine constant-loop fundamental class and its evaluation normalization.
This constructs and detects the candidate; the loop-product unit law still
requires the cap/external-product calculation and the join homotopy. -/

@[expose] public section

namespace Finsler.SphereUnitCandidate

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.BorelLoop Finsler.BorelEvaluation Finsler.CochainComparison
open Finsler.SphereTopClass Finsler.H1FiberBase

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def fundamental (n : ℕ) (hn : 1 ≤ n) : homologyZMod2 (sphere n) n :=
  (homologyEquiv n hn).symm 1

theorem fundamental_ne_zero (n : ℕ) (hn : 1 ≤ n) : fundamental n hn ≠ 0 := by
  intro h
  have he := congrArg (homologyEquiv n hn) h
  rw [fundamental, LinearEquiv.apply_symm_apply, map_zero] at he
  exact one_ne_zero he

theorem top_evaluation_one (n : ℕ) (hn : 1 ≤ n) :
    (kroneckerMap (sphere n) n).hom (topClass n hn) (fundamental n hn) = 1 := by
  have he := (SphereTopClass.cohomologyEquiv n hn).apply_symm_apply (1 : ZMod 2)
  exact he

def constantMap {n : ℕ} (F : ReversibleMetric n) (p : ℝ) : sphere n ⟶ TopCat.of (lev F p) :=
  TopCat.ofHom ⟨fun x => ⟨constantSphereLoop x, Or.inr ⟨x, rfl⟩⟩,
    (constantSphereLoop_continuous n).subtype_mk _⟩

def evaluation {n : ℕ} (F : ReversibleMetric n) (p : ℝ) : TopCat.of (lev F p) ⟶ sphere n :=
  TopCat.ofHom ⟨fun u => point u.val, continuous_point.comp continuous_subtype_val⟩

theorem constantMap_evaluation {n : ℕ} (F : ReversibleMetric n) (p : ℝ) :
    constantMap F p ≫ evaluation F p = 𝟙 (sphere n) := by
  ext x : 1
  exact eval_constant x

def candidate {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) :
    PoolCap.homology (TopCat.of (lev F p)) n :=
  (homologyPushZMod2 (constantMap F p) n).hom (fundamental n hn)

theorem evaluation_push_candidate {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) :
    (homologyPushZMod2 (evaluation F p) n).hom (candidate hn F p) = fundamental n hn := by
  change ((HomologicalComplex.homologyMap (chainMapZMod2 (constantMap F p)) n ≫
    HomologicalComplex.homologyMap (chainMapZMod2 (evaluation F p)) n).hom
      (fundamental n hn)) = _
  rw [← HomologicalComplex.homologyMap_comp]
  have hid : chainMapZMod2 (constantMap F p) ≫ chainMapZMod2 (evaluation F p) =
      𝟙 (chainCxZMod2 (sphere n)) := by
    change (((singularChainComplexFunctor (ModuleCat (ZMod 2))).obj coeff).map (constantMap F p) ≫
      ((singularChainComplexFunctor (ModuleCat (ZMod 2))).obj coeff).map (evaluation F p)) = _
    rw [← CategoryTheory.Functor.map_comp, constantMap_evaluation]
    exact CategoryTheory.Functor.map_id _ _
  rw [hid, HomologicalComplex.homologyMap_id]
  rfl

theorem candidate_ne_zero {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) :
    candidate hn F p ≠ 0 := by
  intro h
  have he := evaluation_push_candidate hn F p
  rw [h, map_zero] at he
  exact fundamental_ne_zero n hn he.symm

theorem evaluation_pairing_one {n : ℕ} (hn : 1 ≤ n) (F : ReversibleMetric n) (p : ℝ) :
    (kroneckerMap (TopCat.of (lev F p)) n).hom
      ((cohPullback (evaluation F p) n).hom (topClass n hn)) (candidate hn F p) = 1 := by
  rw [kroneckerMap_naturality_apply]
  change (kroneckerMap (sphere n) n).hom (topClass n hn)
    ((homologyPushZMod2 (evaluation F p) n).hom (candidate hn F p)) = 1
  rw [evaluation_push_candidate, top_evaluation_one]


end
end Finsler.SphereUnitCandidate
