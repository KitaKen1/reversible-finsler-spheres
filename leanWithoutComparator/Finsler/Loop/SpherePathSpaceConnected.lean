module

public import Finsler.Loop.BasedContinuousLoopModel

/-! Actual fixed-end path spaces on S^n are path connected for
n>=2, by the pinned genuine sphere simply-connectedness theorem
and jointly continuous evaluation of actual path homotopies. -/
@[expose] public section
namespace Finsler.SpherePathSpaceConnected
open CategoryTheory Topology
open Finsler.SphereGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem pathConnected {n : ℕ} (hn : 2 ≤ n) (x a : Sphere n) : PathConnectedSpace (Path x a) := by
  have hs : SimplyConnectedSpace (Sphere n) := TauCeti.simplyConnectedSpace_sphere_euclideanSpace hn
  have := hs
  refine ⟨⟨PathConnectedSpace.somePath x a⟩, fun p q => ?_⟩
  obtain ⟨H⟩ := (simply_connected_iff_paths_homotopic'.mp hs).2 p q
  exact ⟨{ toFun := H.eval
           continuous_toFun := continuous_induced_rng.mpr
             (ContinuousMap.continuous_of_continuous_uncurry _ H.toHomotopy.continuous)
           source' := H.eval_zero
           target' := H.eval_one }⟩

end
end Finsler.SpherePathSpaceConnected
