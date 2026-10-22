module

public import Finsler.Loop.NeighborhoodComplementCutLoops
public import Finsler.Loop.NativeBVRelativeCochain

/-! On the whole original near-cut space, BOTH complementary outputs
are connected to the opposite original outputs by one explicit strong-H1
homotopy. This uses the actual half-period rotation, including endpoint
cut times and unequal endpoints; no ordinary-loop replacement is made. -/
@[expose] public section
namespace Finsler.NativeH1ComplementOutputs
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.CochainComparison Finsler.SupportedSelfCut
open Finsler.SobolevShift Finsler.SobolevRotation
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

abbrev outputSpace (n : ℕ) := TopCat.of (SphereLoop n × SphereLoop n)

def first (n : ℕ) : outputSpace n ⟶ Loops n := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
def second (n : ℕ) : outputSpace n ⟶ Loops n := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

variable (n : ℕ) {r : ℝ} (hr : r ≤ 1)

def swapped : TopCat.of (neighborhood n r) ⟶ outputSpace n :=
  TopCat.ofHom ⟨fun z => (retained n hr z, tested n hr z),
    (retained n hr).continuous.prodMk (tested n hr).continuous⟩

theorem tested_complement (z : neighborhood n r) :
    tested n hr (WholeSelfCutComplement.neighborhoodMap n r z) = shiftSphere (retained n hr z) (1 / 2) :=
  (NeighborhoodComplementCutLoops.retained_half_shift (toTube n hr z)).symm

theorem retained_complement (z : neighborhood n r) :
    retained n hr (WholeSelfCutComplement.neighborhoodMap n r z) = shiftSphere (tested n hr z) (1 / 2) :=
  (NeighborhoodComplementCutLoops.tested_half_shift (toTube n hr z)).symm

private theorem half_rotation_continuous {X : Type} [TopologicalSpace X] (f : C(X, SphereLoop n)) :
    Continuous (fun z : _root_.unitInterval × X => shiftSphere (f z.2) ((z.1 : ℝ) / 2)) := by
  have ht : Continuous (fun z : _root_.unitInterval × X => (z.1 : ℝ) / 2) := by fun_prop
  have hp : Continuous (fun z : _root_.unitInterval × X => (f z.2, (z.1 : ℝ) / 2)) :=
    (f.continuous.comp continuous_snd).prodMk ht
  exact ((shiftSphere_joint_continuous n).comp hp).congr (fun _ => rfl)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
def homotopy : TopCat.Homotopy (swapped n hr)
    (WholeSelfCutComplement.neighborhoodMap n r ≫ output n hr) where
  toFun z := (shiftSphere (retained n hr z.2) ((z.1 : ℝ) / 2),
    shiftSphere (tested n hr z.2) ((z.1 : ℝ) / 2))
  continuous_toFun := by
    change Continuous (fun z : _root_.unitInterval × neighborhood n r =>
      (shiftSphere (retained n hr z.2) ((z.1 : ℝ) / 2), shiftSphere (tested n hr z.2) ((z.1 : ℝ) / 2)))
    exact (half_rotation_continuous n (retained n hr)).prodMk (half_rotation_continuous n (tested n hr))
  map_zero_left z := by
    change (shiftSphere _ ((0 : ℝ) / 2), shiftSphere _ ((0 : ℝ) / 2)) = _
    rw [zero_div, shiftSphere_zero, shiftSphere_zero]
    rfl
  map_one_left z := by
    change (shiftSphere (retained n hr z) (1 / 2), shiftSphere (tested n hr z) (1 / 2)) =
      (tested n hr (WholeSelfCutComplement.neighborhoodMap n r z),
        retained n hr (WholeSelfCutComplement.neighborhoodMap n r z))
    exact Prod.ext (tested_complement n hr z).symm (retained_complement n hr z).symm

theorem swapped_first : swapped n hr ≫ first n = TopCat.ofHom (retained n hr) := rfl
theorem swapped_second : swapped n hr ≫ second n = TopCat.ofHom (tested n hr) := rfl
theorem output_first : output n hr ≫ first n = TopCat.ofHom (tested n hr) := rfl
theorem output_second : output n hr ≫ second n = TopCat.ofHom (retained n hr) := rfl

end
end Finsler.NativeH1ComplementOutputs
