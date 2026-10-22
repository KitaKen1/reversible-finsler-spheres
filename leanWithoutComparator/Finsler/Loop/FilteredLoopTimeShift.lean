module

public import Finsler.Loop.LoopTimeShiftLength
public import Finsler.Loop.StrictLengthEnergyBridge
public import Finsler.Analysis.IntervalH1RotationIsometry

/-! Actual time shifts are homotopic to the identity INSIDE every
strict Finsler length sublevel, with no increase of its bound. -/

@[expose] public section
namespace Finsler.FilteredLoopTimeShift
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction Finsler.SobolevRotation
open Finsler.SobolevShift
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.StrictLengthEnergyBridge
open Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 240000

variable {n : ℕ} (F : ReversibleMetric n) (B a : ℝ)

def shiftMap : lengthSpace F B ⟶ lengthSpace F B := TopCat.ofHom
  ⟨fun u => ⟨Finsler.SobolevShift.shiftSphere u.val a,
    (LoopTimeShiftLength.length_shift F u.val a).trans_lt u.property⟩, by
    have hc := (rotateSphere_joint_continuous n).comp
      (continuous_subtype_val.prodMk (continuous_const : Continuous (fun _ : SelfCutOscillation.short F B => (a : SobolevCircleRepresentative.Circle))))
    exact (hc.congr (fun u => rotateSphere_coe u.val a)).subtype_mk _⟩

def homotopy : TopCat.Homotopy (𝟙 (lengthSpace F B)) (shiftMap F B a) where
  toFun z := ⟨shiftSphere z.2.val ((z.1 : ℝ) * a),
    (LoopTimeShiftLength.length_shift F z.2.val _).trans_lt z.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hu : Continuous (fun z : _root_.unitInterval × SelfCutOscillation.short F B => z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have ht : Continuous (fun z : _root_.unitInterval × SelfCutOscillation.short F B => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hp : Continuous (fun z : _root_.unitInterval × SelfCutOscillation.short F B =>
        (z.2.val, (z.1 : ℝ) * a)) := hu.prodMk (ht.mul continuous_const)
    have hc := (shiftSphere_joint_continuous n).comp hp
    exact hc.congr (fun _ => rfl)
  map_zero_left u := by
    apply Subtype.ext
    change shiftSphere u.val ((0 : ℝ) * a) = u.val
    rw [zero_mul, shiftSphere_zero]
  map_one_left u := by
    apply Subtype.ext
    exact congrArg (shiftSphere u.val) (one_mul a)


theorem homology_eq (q : ℕ) : HomologicalComplex.homologyMap (push (shiftMap F B a)) q =
    𝟙 ((chains (lengthSpace F B)).homology q) := by
  have he := ((homotopy F B a).toSSet.chainComplexMap coeff).homologyMap_eq q
  change HomologicalComplex.homologyMap (push (𝟙 (lengthSpace F B))) q =
    HomologicalComplex.homologyMap (push (shiftMap F B a)) q at he
  have hid : push (𝟙 (lengthSpace F B)) = 𝟙 (chains (lengthSpace F B)) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map (TopCat.toSSet.map (𝟙 _)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [hid, HomologicalComplex.homologyMap_id] at he
  exact he.symm

end
end Finsler.FilteredLoopTimeShift
