module

public import Finsler.Loop.StrictLengthProductCompatibility
public import Finsler.Loop.LengthFilteredLoopRotation
public import Finsler.Loop.FullLoopModel
public import Finsler.Loop.SplitPairHomologyKernel
public import Finsler.Topology.AbsoluteFilteredUnits

/-! The actual constant fundamental class is a unit for the EXISTING
strict-length product, with the literal input-to-output cut inclusion.
The arclength transport is kept; its homotopy is used only in homology. -/
@[expose] public section
namespace Finsler.StrictLengthFilteredUnit
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.StrictLengthEnergyBridge Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)

def candidate (a : ℝ) (ha : 0 < a) : homologyZMod2 (lengthSpace F a) n :=
  (homologyPushZMod2 (toLength F a ha) n).hom (SphereUnitCandidate.candidate hn F a)

theorem constant_cut {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    SphereUnitCandidate.constantMap F a ≫ toLength F a ha ≫ LengthFilteredLoopRotation.cut F hab =
      SphereUnitCandidate.constantMap F b ≫ toLength F b hb := by
  ext x : 1
  rfl

theorem constant_full (a : ℝ) (ha : 0 < a) :
    (SphereUnitCandidate.constantMap F a ≫ toLength F a ha) ≫
      LengthFilteredLoopRotation.full F a ≫ FullLoopModel.insert n =
        AbsoluteFilteredUnits.constant n := by
  ext x : 1
  rfl

theorem candidate_cut {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.cut F hab) n).hom (candidate F hn a ha) =
      candidate F hn b hb := by
  simp only [candidate, SphereUnitCandidate.candidate]
  rw [push_comp_apply, push_comp_apply, constant_cut, ← push_comp_apply]

theorem candidate_full (a : ℝ) (ha : 0 < a) :
    (homologyPushZMod2 (FullLoopModel.insert n) n).hom
      ((homologyPushZMod2 (LengthFilteredLoopRotation.full F a) n).hom (candidate F hn a ha)) =
        AbsoluteFilteredUnits.absoluteCandidate n hn := by
  simp only [candidate, SphereUnitCandidate.candidate]
  rw [push_comp_apply, push_comp_apply, push_comp_apply]
  have h := constant_full F a ha
  rw [Category.assoc] at h
  rw [h]
  rfl

theorem candidate_energy (a : ℝ) (ha : 0 < a) :
    (homologyPushZMod2 (toEnergy F a) n).hom (candidate F hn a ha) =
      SphereUnitCandidate.candidate hn F a :=
  StrictLengthProductCompatibility.energy_inverse_apply F a ha n _

theorem left_square {p q ε : ℝ} (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) :
    toEnergy F q ≫ FilteredLeftUnit.inclusion F hp hq hε ≫
      toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε)) =
    (toEnergy F q ≫ toLength F q hq) ≫
      LengthFilteredLoopRotation.cut F (by linarith : q ≤ p + (q + ε)) := by
  ext x : 1
  rfl

theorem left_unit {p q ε : ℝ} (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε)
    (k : ℕ) (y : homologyZMod2 (lengthSpace F q) k) :
    StrictLengthLoopProduct.product F hn hε n k k rfl (candidate F hn p hp) y =
      (homologyPushZMod2 (LengthFilteredLoopRotation.cut F
        (by linarith : q ≤ p + (q + ε))) k).hom y := by
  rw [StrictLengthLoopProduct.product_pos F hn hp hq hε,
    StrictLengthLoopProduct.positive_apply]
  have hc : (PoolCap.push (toEnergy F p) n).hom (candidate F hn p hp) =
      SphereUnitCandidate.candidate hn F p := candidate_energy F hn p hp
  rw [hc, FilteredLeftUnit.left_unit]
  change (homologyPushZMod2 (toLength F (p + (q + ε)) (add_pos hp (add_pos hq hε))) k).hom
    ((homologyPushZMod2 (FilteredLeftUnit.inclusion F hp hq hε) k).hom
      ((homologyPushZMod2 (toEnergy F q) k).hom y)) = _
  rw [push_comp_apply, push_comp_apply, left_square F hp hq hε, ← push_comp_apply]
  have he := ConcreteCategory.congr_hom (short_homology_inverse F q hq k) y
  change (homologyPushZMod2 (toLength F q hq) k).hom
    ((homologyPushZMod2 (toEnergy F q) k).hom y) = y at he
  rw [push_comp_apply] at he
  rw [he]

end
end Finsler.StrictLengthFilteredUnit
