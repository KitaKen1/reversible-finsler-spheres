module

public import Finsler.Loop.StartingPathRotorHomology
public import Finsler.Loop.StartingPathMVFiberVanishing
public import Finsler.Loop.SpherePathSpaceConnected

/-! Compute ONLY the actual two based-path homology gaps needed
for the original UNIT: H1 first, then H_n for n>=3. Actual MV of the
contractible starting-path space and the actual timed-rotor charts
supply the geometric inputs; no Serre or Kunneth premise remains. -/
@[expose] public section
namespace Finsler.PathSphereHomologyGap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.H1PuncturedEvaluationChart Finsler.StartingPathSphereCover
open Finsler.StartingPathRotorHomology Finsler.MeridianEquatorHomology
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem equator_in_overlap {n : ℕ} (a : Sphere n) (v : equator a) :
    v.val ∈ base a ∩ base (antipode a) := by
  have ha : ‖(a : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp a.property
  have hne : v.val ≠ a := by
    intro h
    have he := v.property
    rw [h, real_inner_self_eq_norm_sq, ha] at he
    norm_num at he
  constructor
  · intro h
    have he := v.property
    rw [h] at he
    change ⟪(a : Ambient n), -(a : Ambient n)⟫ = 0 at he
    rw [inner_neg_right, real_inner_self_eq_norm_sq, ha] at he
    norm_num at he
  · change v.val ≠ antipode (antipode a)
    rw [antipode_antipode]
    exact hne

theorem fiber_surjective_one (m : ℕ) (hm : 2 ≤ m) (x a z : Sphere (m + 1))
    (hz : z ∈ base a ∩ base (antipode a)) :
    Function.Surjective (homologyPushZMod2 (fiberToOverlap x a z hz) 1).hom := by
  have := SpherePathSpaceConnected.pathConnected (by omega : 2 ≤ m + 1) x a
  have hd : Module.finrank ℝ (orthogonalSpace (antipode a)) = (m - 2) + 3 := by
    rw [orthogonal_dimension]
    omega
  have hi := ProductFiberGeneration.second_injective_of_equiv
    (NativeEvaluationConnectedFiber.baseOverlapEquiv a) (TopCat.of (Path x a)) 1
    (SphereProductFirstDegreeDetection.second_one_injective (m - 2) hd _)
  exact fiber_surjective_of_section x a z hz 1
    (ProductFiberGeneration.fiber_surjective (X := NativeEvaluationMayerVietoris.baseOverlap a)
      (Y := TopCat.of (Path x a)) 1 ⟨z, hz⟩ hi)

theorem path_one_zero (m : ℕ) (hm : 2 ≤ m) (x a : Sphere (m + 1)) (v : equator a) :
    IsZero (homologyZMod2 (TopCat.of (Path x a)) 1) := by
  let hz := equator_in_overlap a v
  have h := StartingPathMVFiberVanishing.fiber_zero x a v.val hz 0
    (fiber_surjective_one m hm x a v.val hz) (north_injective x a v.val hz 1) (south_injective x a v.val hz 1)
  exact h.of_iso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) 1).obj coeff).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Path x v.val)) (Y := TopCat.of (Path x a))
      (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨v.val, hz.1⟩))).symm

theorem fiber_surjective_shifted (m : ℕ) (x a z : Sphere (m + 1))
    (hz : z ∈ base a ∩ base (antipode a))
    (hF : IsZero (homologyZMod2 (TopCat.of (Path x a)) 1)) :
    Function.Surjective (homologyPushZMod2 (fiberToOverlap x a z hz) (m + 1)).hom := by
  have hi := ProductFiberGeneration.second_injective_of_equiv
    (NativeEvaluationConnectedFiber.baseOverlapEquiv a) (TopCat.of (Path x a)) (m + 1)
    (SphereProductShiftedDetection.second_shifted_injective m (orthogonal_dimension (antipode a)) _ hF)
  exact fiber_surjective_of_section x a z hz (m + 1)
    (ProductFiberGeneration.fiber_surjective (X := NativeEvaluationMayerVietoris.baseOverlap a)
      (Y := TopCat.of (Path x a)) (m + 1) ⟨z, hz⟩ hi)

theorem path_top_zero (m : ℕ) (hm : 2 ≤ m) (x a : Sphere (m + 1)) (v : equator a) :
    IsZero (homologyZMod2 (TopCat.of (Path x a)) (m + 1)) := by
  let hz := equator_in_overlap a v
  have h := StartingPathMVFiberVanishing.fiber_zero x a v.val hz m
    (fiber_surjective_shifted m x a v.val hz (path_one_zero m hm x a v))
    (north_injective x a v.val hz (m + 1)) (south_injective x a v.val hz (m + 1))
  exact h.of_iso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (m + 1)).obj coeff).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Path x v.val)) (Y := TopCat.of (Path x a))
      (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨v.val, hz.1⟩))).symm

end
end Finsler.PathSphereHomologyGap
