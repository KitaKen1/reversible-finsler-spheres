module

public import Finsler.Loop.SphereProductOffsetDetection
public import Finsler.Loop.PathSphereHomologyGap
public import Finsler.Loop.NativeEvaluationOrdinaryBasedGap
public import Finsler.Loop.NativeThetaPowers

/-! Extend the actual based-path vanishing from degree one to EVERY
degree k*(n-1)+1, hence every original Theta-power degree. The actual
starting-path cover and rotor maps discharge all geometric premises. -/
@[expose] public section
namespace Finsler.PathSphereHomologyTower
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.H1PuncturedEvaluationChart Finsler.StartingPathSphereCover
open Finsler.StartingPathRotorHomology Finsler.MeridianEquatorHomology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem fiber_surjective_offset (m q : ℕ) (x a z : Sphere (m + 1))
    (hz : z ∈ base a ∩ base (antipode a))
    (hF : IsZero (homologyZMod2 (TopCat.of (Path x a)) (q + 1))) :
    Function.Surjective (homologyPushZMod2 (fiberToOverlap x a z hz) (m + (q + 1))).hom := by
  have hi := ProductFiberGeneration.second_injective_of_equiv
    (NativeEvaluationConnectedFiber.baseOverlapEquiv a) (TopCat.of (Path x a)) (m + (q + 1))
    (SphereProductOffsetDetection.second_offset_injective m q (orthogonal_dimension (antipode a)) _ hF)
  exact fiber_surjective_of_section x a z hz (m + (q + 1))
    (ProductFiberGeneration.fiber_surjective (X := NativeEvaluationMayerVietoris.baseOverlap a)
      (Y := TopCat.of (Path x a)) (m + (q + 1)) ⟨z, hz⟩ hi)

theorem path_zero_step (m q : ℕ) (x a : Sphere (m + 1)) (v : equator a)
    (hF : IsZero (homologyZMod2 (TopCat.of (Path x a)) (q + 1))) :
    IsZero (homologyZMod2 (TopCat.of (Path x a)) (m + (q + 1))) := by
  let hz := PathSphereHomologyGap.equator_in_overlap a v
  have hj : Function.Surjective (homologyPushZMod2 (fiberToOverlap x a v.val hz) ((m + q) + 1)).hom := by
    exact (congrArg (fun j => Function.Surjective
      (homologyPushZMod2 (fiberToOverlap x a v.val hz) j).hom) (Nat.add_assoc m q 1)).mpr
        (fiber_surjective_offset m q x a v.val hz hF)
  have h := StartingPathMVFiberVanishing.fiber_zero x a v.val hz (m + q) hj
    (north_injective x a v.val hz ((m + q) + 1)) (south_injective x a v.val hz ((m + q) + 1))
  have he : IsZero (homologyZMod2 (TopCat.of (Path x a)) ((m + q) + 1)) :=
    h.of_iso (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) ((m + q) + 1)).obj coeff).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of (Path x v.val)) (Y := TopCat.of (Path x a))
        (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨v.val, hz.1⟩))).symm
  simpa only [Nat.add_assoc] using he

theorem path_tower_zero (m : ℕ) (hm : 2 ≤ m) (x a : Sphere (m + 1)) (v : equator a) (k : ℕ) :
    IsZero (homologyZMod2 (TopCat.of (Path x a)) (k * m + 1)) := by
  induction k with
  | zero => simpa only [Nat.zero_mul, Nat.zero_add] using PathSphereHomologyGap.path_one_zero m hm x a v
  | succ k ih =>
    have h := path_zero_step m (k * m) x a v ih
    rw [show m + (k * m + 1) = (k + 1) * m + 1 by ring] at h
    exact h

theorem based_tower_zero (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    IsZero (homologyZMod2 (TopCat.of (H1LocalFiber.based P)) (k * m + 1)) :=
  NativeEvaluationOrdinaryBasedGap.based_zero_of_path_zero P (k * m + 1)
    (path_tower_zero m hm P P v₀ k)

theorem based_theta_zero (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    IsZero (homologyZMod2 (TopCat.of (H1LocalFiber.based P)) (NativeThetaPowers.degree m r)) := by
  have hd : NativeThetaPowers.degree m r = (2 * r + 3) * m + 1 := by
    rw [NativeThetaPowers.degree_formula]
    ring
  rw [hd]
  exact based_tower_zero m hm P v₀ (2 * r + 3)

end
end Finsler.PathSphereHomologyTower
