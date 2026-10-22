module

public import Finsler.Loop.H1LoopRotation
public import Finsler.Loop.FilteredLoopTimeShift

/-! Full-period rotation defines a genuine degree+1 BV map INSIDE
EVERY original strict Finsler length cut, with zero additional length.
Its full inclusion and cut inclusions commute in actual homology. -/
@[expose] public section
namespace Finsler.LengthFilteredLoopRotation
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1000000

def homotopy {n : ℕ} (F : ReversibleMetric n) (B : ℝ) :
    TopCat.Homotopy (𝟙 (lengthSpace F B)) (𝟙 (lengthSpace F B)) where
  toFun := FilteredLoopTimeShift.homotopy F B 1
  continuous_toFun := (FilteredLoopTimeShift.homotopy F B 1).continuous
  map_zero_left u := (FilteredLoopTimeShift.homotopy F B 1).apply_zero u
  map_one_left u := by
    have h := (FilteredLoopTimeShift.homotopy F B 1).apply_one u
    refine h.trans ?_
    apply Subtype.ext
    change shiftSphere u.val 1 = u.val
    have hp := shiftSphere_periodic u.val 0
    simpa only [zero_add, shiftSphere_zero] using hp

def chainHomotopy {n : ℕ} (F : ReversibleMetric n) (B : ℝ) :=
  (homotopy F B).toSSet.chainComplexMap coeff

def BV {n : ℕ} (F : ReversibleMetric n) (B : ℝ) (q : ℕ) :
    homologyZMod2 (lengthSpace F B) q ⟶ homologyZMod2 (lengthSpace F B) (q + 1) :=
  SelfHomotopySweep.homology (chainHomotopy F B) q

def full {n : ℕ} (F : ReversibleMetric n) (B : ℝ) : lengthSpace F B ⟶ Loops n :=
  SupportedCap.subspaceMap (Loops n) (SelfCutOscillation.short F B)

theorem prism_full {n : ℕ} (F : ReversibleMetric n) (B : ℝ) (q : ℕ) :
    (push (full F B)).f q ≫ (H1LoopRotation.chainHomotopy n).hom q (q + 1) =
      (chainHomotopy F B).hom q (q + 1) ≫ (push (full F B)).f (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (full F B)) (homotopy F B)).h =
      ((H1LoopRotation.homotopy n).comp (TopCat.Homotopy.refl (full F B))).h := by
    ext z : 1
    change shiftSphere z.1.val ((z.2.down : ℝ) * 1) = shiftSphere z.1.val (z.2.down : ℝ)
    rw [mul_one]
  exact (TimePrismNaturality.prism_pre _ _ q).trans
    ((TimePrismNaturality.prism_congr _ _ he.symm q).trans (TimePrismNaturality.prism_post _ _ q).symm)

theorem BV_full {n : ℕ} (F : ReversibleMetric n) (B : ℝ) (q : ℕ) :
    HomologicalComplex.homologyMap (push (full F B)) q ≫ H1LoopRotation.BV n q =
      BV F B q ≫ HomologicalComplex.homologyMap (push (full F B)) (q + 1) :=
  SelfHomotopySweepNaturality.homology (chainHomotopy F B) (H1LoopRotation.chainHomotopy n)
    (push (full F B)) (push (full F B)) (prism_full F B) q

def cut {n : ℕ} (F : ReversibleMetric n) {A B : ℝ} (h : A ≤ B) : lengthSpace F A ⟶ lengthSpace F B :=
  TopCat.ofHom ⟨fun u => ⟨u.val, u.property.trans_le h⟩, continuous_subtype_val.subtype_mk _⟩

theorem prism_cut {n : ℕ} (F : ReversibleMetric n) {A B : ℝ} (h : A ≤ B) (q : ℕ) :
    (push (cut F h)).f q ≫ (chainHomotopy F B).hom q (q + 1) =
      (chainHomotopy F A).hom q (q + 1) ≫ (push (cut F h)).f (q + 1) := by
  have he : (TopCat.Homotopy.comp (TopCat.Homotopy.refl (cut F h)) (homotopy F A)).h =
      ((homotopy F B).comp (TopCat.Homotopy.refl (cut F h))).h := by
    ext z : 1
    apply Subtype.ext
    rfl
  exact (TimePrismNaturality.prism_pre _ _ q).trans
    ((TimePrismNaturality.prism_congr _ _ he.symm q).trans (TimePrismNaturality.prism_post _ _ q).symm)

theorem BV_cut {n : ℕ} (F : ReversibleMetric n) {A B : ℝ} (h : A ≤ B) (q : ℕ) :
    HomologicalComplex.homologyMap (push (cut F h)) q ≫ BV F B q =
      BV F A q ≫ HomologicalComplex.homologyMap (push (cut F h)) (q + 1) :=
  SelfHomotopySweepNaturality.homology (chainHomotopy F A) (chainHomotopy F B)
    (push (cut F h)) (push (cut F h)) (prism_cut F h) q

end
end Finsler.LengthFilteredLoopRotation
