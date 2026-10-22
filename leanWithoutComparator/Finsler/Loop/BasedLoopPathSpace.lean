module

public import Finsler.Loop.BasedContinuousLoopModel
public import Finsler.Topology.CochainComparison

/-! The actual based AddCircle-loop fiber is homeomorphic to
Mathlib's actual endpoint-fixed path loop space. Both directions
retain every interval/circle value, including the endpoint seam. -/
@[expose] public section
namespace Finsler.BasedLoopPathSpace
open CategoryTheory AlgebraicTopology Topology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.BasedContinuousLoopModel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

abbrev space {n : ℕ} (y : Sphere n) : TopCat.{0} := TopCat.of (Path y y)

theorem intervalPath_continuous {n : ℕ} (y : Sphere n) : Continuous (intervalPath y) := by
  apply continuous_induced_rng.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
    ((AddCircle.continuous_mk' 1).comp (continuous_subtype_val.comp continuous_snd)))

theorem intervalPath_ofPath {n : ℕ} (y : Sphere n) (γ : Path y y) :
    intervalPath y (ofPath y γ) = γ := by
  apply Path.ext
  funext t
  exact ClosedPathCircle.circle_coe (ClosedPathCircle.ofPath γ) t

def homeomorph {n : ℕ} (y : Sphere n) : BasedContinuousLoopModel.space y ≃ₜ space y where
  toFun := intervalPath y
  invFun := ofPath y
  left_inv := ofPath_intervalPath y
  right_inv := intervalPath_ofPath y
  continuous_toFun := intervalPath_continuous y
  continuous_invFun := ofPath_continuous y

def homologyIso {n : ℕ} (y : Sphere n) (q : ℕ) :
    homologyZMod2 (BasedContinuousLoopModel.space y) q ≅ homologyZMod2 (space y) q :=
  ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) q).obj coeff).mapIso
    (TopCat.isoOfHomeo (homeomorph y))

end
end Finsler.BasedLoopPathSpace
