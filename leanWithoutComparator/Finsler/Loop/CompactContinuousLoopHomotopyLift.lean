module

public import Finsler.Loop.CompactContinuousLoopApproximation
public import Finsler.Loop.CloseContinuousLoopHomotopy
public import Finsler.Topology.SupportedCapNaturality

/-! An ACTUAL compact ordinary-loop family is homotopic to the image
of a genuine continuous strong-H1 family. Original constant loops and
the entire homotopy over them are preserved. -/

@[expose] public section
namespace Finsler.CompactContinuousLoopHomotopyLift
open CategoryTheory TopologicalSpace Topology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1200000

theorem exists_lift (n : ℕ) (K : Compacts (ContinuousLoopModel.space n)) :
    ∃ e : TopCat.of K ⟶ Loops n,
      ∃ H : TopCat.Homotopy (e ≫ ContinuousLoopModel.inclusion n)
        (SupportedCap.subspaceMap (ContinuousLoopModel.space n) (K : Set (ContinuousLoopModel.space n))),
        ∀ (u : K) (P : Sphere n), u.val = ContinuousLoopModel.constantMap n P →
          e u = constantSphereLoop P ∧ ∀ t : ClosedInterval, H (t, u) = ContinuousLoopModel.constantMap n P := by
  obtain ⟨N, hN, h⟩ := CompactContinuousLoopApproximation.exists_close_replacements n K (by norm_num : 0 < (1 : ℝ))
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨e, he, -, hconst⟩ := h N le_rfl
  let i := SupportedCap.subspaceMap (ContinuousLoopModel.space n) (K : Set (ContinuousLoopModel.space n))
  let H := CloseContinuousLoopHomotopy.homotopy (e ≫ ContinuousLoopModel.inclusion n) i he
  refine ⟨e, H, fun u P hu => ⟨hconst u P hu, ?_⟩⟩
  intro t
  have hP := ConcreteCategory.congr_hom (ContinuousLoopModel.constant_square n) P
  change ContinuousLoopModel.inclusion n (constantSphereLoop P) = ContinuousLoopModel.constantMap n P at hP
  have hx : (e ≫ ContinuousLoopModel.inclusion n) u = i u := by
    change ContinuousLoopModel.inclusion n (e u) = u.val
    rw [hconst u P hu, hP, hu]
  exact (CloseContinuousLoopHomotopy.fixed (e ≫ ContinuousLoopModel.inclusion n) i he u hx t).trans (by
    change ContinuousLoopModel.inclusion n (e u) = ContinuousLoopModel.constantMap n P
    rw [hconst u P hu, hP])

end
end Finsler.CompactContinuousLoopHomotopyLift
