module

public import Finsler.Loop.NativeEvaluationOverlapProduct
public import Finsler.Loop.NativeEvaluationPatchGap
public import Finsler.Loop.NativeEvaluationOverlapCriterion

/-! Replace the actual overlap joint test by projection detection
on the REAL product model. The two patch-map zero hypothesis gives
the northern factor zero through the genuine Mayer-Vietoris map,
not through an assumed product decomposition. -/
@[expose] public section
namespace Finsler.NativeEvaluationProductDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.H1LocalFiber (based)
open Finsler.H1PuncturedRelativeChart Finsler.MeridianLoopFamily
open Finsler.NativeEvaluationMayerVietoris Finsler.NativeEvaluationOverlapProduct
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

def homology {n : ℕ} (y : Sphere n) (k : ℕ) :
    homologyZMod2 (overlap y) k ≃ₗ[ZMod 2] homologyZMod2 (model y) k :=
  (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso (iso y)).toLinearEquiv

theorem homology_apply {n : ℕ} (y : Sphere n) (k : ℕ) (z : homologyZMod2 (overlap y) k) :
    homology y k z = (homologyPushZMod2 (iso y).hom k).hom z := rfl

theorem toPatches_fst {n : ℕ} (y : Sphere n) (k : ℕ) :
    toPatches y k ≫ biprod.fst = homologyPushZMod2 (northInclusion y) k :=
  SSet.mayerVietorisToBiprod_fst coeff _ _ k

theorem north_zero_of_toPatches_zero {n : ℕ} (y : Sphere n) (k : ℕ)
    (z : homologyZMod2 (overlap y) k) (hz : (toPatches y k).hom z = 0) :
    (homologyPushZMod2 (northInclusion y) k).hom z = 0 := by
  have he := ConcreteCategory.congr_hom (toPatches_fst y k) z
  change (biprod.fst : patches y k ⟶ homologyZMod2 (TopCat.of (fullDomain y)) k).hom
    ((toPatches y k).hom z) = _ at he
  rw [hz, map_zero] at he
  exact he.symm

theorem base_projection_zero {n : ℕ} (y : Sphere n) (k : ℕ)
    (z : homologyZMod2 (overlap y) k)
    (hz : (homologyPushZMod2 (overlapEvaluation y) k).hom z = 0) :
    (homologyPushZMod2 (baseProjection y) k).hom (homology y k z) = 0 := by
  rw [homology_apply, SplitPairHomologyKernel.push_comp_apply, evaluation_factor]
  exact hz

theorem fiber_projection_zero {n : ℕ} (y : Sphere n) (k : ℕ)
    (z : homologyZMod2 (overlap y) k) (hz : (toPatches y k).hom z = 0) :
    (homologyPushZMod2 (fiberProjection y) k).hom (homology y k z) = 0 := by
  rw [homology_apply, SplitPairHomologyKernel.push_comp_apply, alignment_factor,
    ← SplitPairHomologyKernel.push_comp_apply, north_zero_of_toPatches_zero y k z hz, map_zero]

theorem joint_overlap_of_product_projections {n : ℕ} (y : Sphere n) (k : ℕ)
    (hd : ∀ c : homologyZMod2 (model y) k,
      (homologyPushZMod2 (baseProjection y) k).hom c = 0 →
      (homologyPushZMod2 (fiberProjection y) k).hom c = 0 → c = 0)
    (z : homologyZMod2 (overlap y) k)
    (he : (homologyPushZMod2 (overlapEvaluation y) k).hom z = 0)
    (hp : (toPatches y k).hom z = 0) : z = 0 := by
  apply (homology y k).injective
  exact (hd (homology y k z) (base_projection_zero y k z he) (fiber_projection_zero y k z hp)).trans (map_zero _).symm

theorem original_UNIT_of_based_gap_and_product_detection (m : ℕ) (hm : 2 ≤ m)
    (y : Sphere (m + 1)) (v₀ : equator y)
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1)))
    (hS : IsZero (homologyZMod2 (TopCat.of (based (antipode y))) (m + 1)))
    (hd : ∀ c : homologyZMod2 (model y) m,
      (homologyPushZMod2 (baseProjection y) m).hom c = 0 →
      (homologyPushZMod2 (fiberProjection y) m).hom c = 0 → c = 0) :
    NativeConstantUnitDefect.cutFull m (by omega) y v₀ =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  NativeEvaluationPatchGap.original_UNIT_of_based_gap_and_overlap m hm y v₀ hN hS
    (joint_overlap_of_product_projections y m hd)

end
end Finsler.NativeEvaluationProductDetection
