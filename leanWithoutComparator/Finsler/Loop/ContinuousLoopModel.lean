module

public import Finsler.Loop.FullLoopModel
public import Finsler.Analysis.IntervalH1CircleAction

/-! The actual map from strong H1 sphere loops to ordinary continuous
circle loops, with genuine constant/evaluation squares. No homology
equivalence or ordinary loop-space rank calculation is assumed. -/

@[expose] public section
namespace Finsler.ContinuousLoopModel
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

local notation "Circ" => SobolevCircleRepresentative.Circle

abbrev space (n : ℕ) : TopCat.{0} := TopCat.of C(Circ, Sphere n)

def inclusion (n : ℕ) : Loops n ⟶ space n :=
  TopCat.ofHom ⟨sphereCircleMap, sphereCircleMap_continuous n⟩

theorem inclusion_injective (n : ℕ) : Function.Injective (inclusion n) :=
  sphereCircleMap_injective n

def evaluation (n : ℕ) : space n ⟶ sphere n :=
  TopCat.ofHom ⟨fun u => u 0, continuous_eval_const 0⟩

def constantMap (n : ℕ) : sphere n ⟶ space n :=
  TopCat.ofHom ⟨fun x => ContinuousMap.const Circ x,
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_fst⟩

theorem constant_evaluation (n : ℕ) : constantMap n ≫ evaluation n = 𝟙 (sphere n) := by
  ext x : 1
  rfl

theorem evaluation_square (n : ℕ) : inclusion n ≫ evaluation n =
    FullLoopModel.insert n ≫ fullEval n := by
  ext u : 1
  change sphereCircleMap u (0 : Circ) = sphereRepresentative u (0 : ClosedInterval)
  simpa using sphereCircleMap_coe u (0 : ClosedInterval)

theorem constant_square (n : ℕ) : SphereTopClass.fullSection n ≫ FullLoopModel.forget n ≫ inclusion n =
    constantMap n := by
  ext x : 1
  apply ContinuousMap.ext
  intro t
  change sphereCircleMap (constantSphereLoop x) t = x
  rw [sphereCircleMap_point, sphereRepresentative_constantSphereLoop]

end
end Finsler.ContinuousLoopModel
