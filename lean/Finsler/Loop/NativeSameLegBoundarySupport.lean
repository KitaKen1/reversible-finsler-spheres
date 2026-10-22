module

public import Finsler.Loop.NativeSameLegBoundaryGeometry

/-! The actual primitive-cap correction vanishes separately on the
rotation ends, the opposite cut end, and the true diagonal seam.
These are literal cochain zeros with the original radii and output. -/
@[expose] public section
namespace Finsler.NativeSameLegBoundarySupport
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.SameMeridianTransverseEscape Finsler.NativeSameLegThomPrimitive
open Finsler.NativeSameLegCapSupport Finsler.NativeSameLegBoundaryGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (P : Sphere (m + 1)) (v₀ : equator P)
  (k : Fin 3) (isLong : Bool) {ρ r η : ℝ}
  (hρ : 0 < ρ) (hρr : ρ < r) (hρ1 : ρ ≤ 1) (hr : r ≤ 1) (hη : 0 < η)
  (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) p)

theorem correction_rotation_zero (hη2 : η ≤ 1 / 2) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (rotationEnds P v₀ k)) (m + (p + (m + 1)))
      (NativeSameLegLocalCap.correction m hm P v₀ k isLong hρ hρr hρ1 (p + (m + 1))
        (nearOutput m p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hr hη T)) = 0 := by
  apply correction_carrier_zero m hm p P v₀ k isLong _ hρ hρr hρ1 hr hη T
  intro z hz _
  have hd := NorthMeridianEvaluationPoint.excluded_distance P v₀
    ⟨H1FiberBase.point (family P v₀ k isLong z).2, rotation_start_excluded P v₀ k isLong z hz⟩
  exact hη2.trans ((by norm_num : (1 / 2 : ℝ) ≤ 3 / 5).trans hd)

theorem correction_other_end_zero (hηr : η + r ≤ 3 / 5) :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (otherCutEnd P v₀ k isLong)) (m + (p + (m + 1)))
      (NativeSameLegLocalCap.correction m hm P v₀ k isLong hρ hρr hρ1 (p + (m + 1))
        (nearOutput m p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hr hη T)) = 0 := by
  apply correction_carrier_zero m hm p P v₀ k isLong _ hρ hρr hρ1 hr hη T
  intro z hz hn
  apply first_far_of_either_far _ (family P v₀ k isLong z) hn hηr
  exact Or.inr (NorthMeridianEvaluationPoint.excluded_distance P v₀
    ⟨H1SelfCutNeighborhood.endpoint (family P v₀ k isLong z), other_endpoint_excluded P v₀ k isLong z hz⟩)

theorem correction_seam_zero :
    cochainPullback (SupportedCap.subspaceMap (localSpace P v₀ k) (seam P v₀ k isLong)) (m + (p + (m + 1)))
      (NativeSameLegLocalCap.correction m hm P v₀ k isLong hρ hρr hρ1 (p + (m + 1))
        (nearOutput m p P v₀ k isLong (NorthMeridianEvaluationPoint.target P v₀) hr hη T)) = 0 :=
  NativeSameLegLocalCap.correction_seam_zero m hm P v₀ k isLong hρ hρr hρ1 _ _

end
end Finsler.NativeSameLegBoundarySupport
