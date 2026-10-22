module

public import Finsler.Loop.OrdinaryLoopRotation
public import Finsler.Analysis.IntervalH1RotationIsometry

/-! Genuine strong-H1 full-period rotation, and compatibility of
its BV map with the ACTUAL ordinary-loop inclusion in every degree. -/
@[expose] public section
namespace Finsler.H1LoopRotation
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction Finsler.SobolevRotation Finsler.SobolevShift
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 300000

def homotopy (n : ℕ) : TopCat.Homotopy (𝟙 (Loops n)) (𝟙 (Loops n)) where
  toFun z := shiftSphere z.2 (z.1 : ℝ)
  continuous_toFun := by
    change Continuous (fun z : _root_.unitInterval × SphereLoop n => shiftSphere z.2 (z.1 : ℝ))
    have ht : Continuous (fun z : _root_.unitInterval × SphereLoop n => (z.2, (z.1 : ℝ))) :=
      continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
    have hc := (shiftSphere_joint_continuous n).comp ht
    exact hc.congr (fun _ => rfl)
  map_zero_left u := by
    change shiftSphere u (0 : ℝ) = u
    exact shiftSphere_zero u
  map_one_left u := by
    change shiftSphere u (1 : ℝ) = u
    have h := shiftSphere_periodic u 0
    simpa only [zero_add, shiftSphere_zero] using h

def chainHomotopy (n : ℕ) := (homotopy n).toSSet.chainComplexMap coeff

def BV (n q : ℕ) : homologyZMod2 (Loops n) q ⟶ homologyZMod2 (Loops n) (q + 1) :=
  SelfHomotopySweep.homology (chainHomotopy n) q

theorem prism_inclusion (n q : ℕ) :
    (push (ContinuousLoopModel.inclusion n)).f q ≫ (OrdinaryLoopRotation.chainHomotopy n).hom q (q + 1) =
      (chainHomotopy n).hom q (q + 1) ≫ (push (ContinuousLoopModel.inclusion n)).f (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (ContinuousLoopModel.inclusion n)) (homotopy n)).h =
      ((OrdinaryLoopRotation.homotopy n).comp (TopCat.Homotopy.refl (ContinuousLoopModel.inclusion n))).h := by
    ext z : 1
    apply ContinuousMap.ext
    intro x
    let t : _root_.unitInterval := z.2.down
    change sphereCircleMap (shiftSphere z.1 (t : ℝ)) x =
      sphereCircleMap z.1 (((t : ℝ) : SobolevCircleRepresentative.Circle) + x)
    rw [circleMap_shiftSphere, shiftedSphereMap_apply]
  calc
    _ = (((OrdinaryLoopRotation.homotopy n).comp
        (TopCat.Homotopy.refl (ContinuousLoopModel.inclusion n))).toSSet.chainComplexMap coeff).hom q (q + 1) :=
      TimePrismNaturality.prism_pre _ _ q
    _ = ((TopCat.Homotopy.comp (TopCat.Homotopy.refl (ContinuousLoopModel.inclusion n))
        (homotopy n)).toSSet.chainComplexMap coeff).hom q (q + 1) :=
      TimePrismNaturality.prism_congr _ _ he.symm q
    _ = _ := (TimePrismNaturality.prism_post _ _ q).symm

theorem BV_inclusion (n q : ℕ) :
    HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) q ≫ OrdinaryLoopRotation.BV n q =
      BV n q ≫ HomologicalComplex.homologyMap (push (ContinuousLoopModel.inclusion n)) (q + 1) :=
  SelfHomotopySweepNaturality.homology (chainHomotopy n) (OrdinaryLoopRotation.chainHomotopy n)
    (push (ContinuousLoopModel.inclusion n)) (push (ContinuousLoopModel.inclusion n)) (prism_inclusion n) q

theorem equivalence_BV (n q : ℕ) (x : homologyZMod2 (Loops n) q) :
    ContinuousLoopHomologyEquivalence.homology n (q + 1) ((BV n q).hom x) =
      (OrdinaryLoopRotation.BV n q).hom (ContinuousLoopHomologyEquivalence.homology n q x) := by
  have h := ConcreteCategory.congr_hom (BV_inclusion n q) x
  exact h.symm

end
end Finsler.H1LoopRotation
