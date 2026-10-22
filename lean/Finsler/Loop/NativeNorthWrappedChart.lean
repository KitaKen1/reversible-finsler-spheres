module

public import Finsler.Loop.NativeNorthOrderedCharts

/-! The actual wrapped northern ordered cell is the ACTUAL complement
of the same forward independent cut, including all boundary times.
Prove the shift identity for an arbitrary loop before substituting
any native H1 construction, avoiding expansion of that construction. -/
@[expose] public section
namespace Finsler.NativeNorthWrappedChart
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.NativeMeridianMatchingLoci Finsler.NativeMeridianPairCoordinates
open Finsler.MeridianTripleQuarterClocks Finsler.SobolevShift Finsler.SobolevCircleAction
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem complement_shift {n : ℕ} (U : SphereLoop n) (a c : ℝ) (d : ClosedInterval)
    (hd : (d : ℝ) = c - a) :
    WholeSelfCutComplement.complement n (d, shiftSphere U a) =
      (unitInterval.symm d, shiftSphere U c) := by
  change (unitInterval.symm d, shiftSphere (shiftSphere U a) (d : ℝ)) = _
  have ht : (d : ℝ) + a = c := by rw [hd]; ring
  exact Prod.ext rfl ((shiftSphere_add U (d : ℝ) a).trans (congrArg (shiftSphere U) ht))

theorem north_complement {n : ℕ} (U : SphereLoop n) (b : Fin 3) (s t : ClosedInterval) :
    (unitInterval.symm (pairCutTime b (MeridianQuarterIncidence.northTime s) (MeridianQuarterIncidence.northTime t)),
      shiftSphere U (clock (pairRight b) 0 t)) =
    WholeSelfCutComplement.complement n
      (pairCutTime b (MeridianQuarterIncidence.northTime s) (MeridianQuarterIncidence.northTime t),
        shiftSphere U (legClock (pairLeft b) (MeridianQuarterIncidence.northTime s))) := by
  have he := complement_shift U (legClock (pairLeft b) (MeridianQuarterIncidence.northTime s))
    (legClock (pairRight b) (MeridianQuarterIncidence.northTime t))
    (pairCutTime b (MeridianQuarterIncidence.northTime s) (MeridianQuarterIncidence.northTime t)) rfl
  exact (congrArg (fun c =>
    (unitInterval.symm (pairCutTime b (MeridianQuarterIncidence.northTime s) (MeridianQuarterIncidence.northTime t)),
      shiftSphere U c)) (NativeNorthOrderedCharts.north_clock (pairRight b) t)).trans he.symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
theorem wrapped_intoCut {n : ℕ} (P : Sphere n) (v₀ : equator P) (b : Fin 3) :
    NativeNorthOrderedCharts.wrapped P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (pairRight b) =
      NativeNorthOrderedCharts.northParameters P ≫ NativeMeridianPairCoordinates.intoCut P v₀ b ≫
        WholeSelfCutComplement.complement n := by
  apply TopCat.ext
  intro z
  exact north_complement (NativeH1TripleMeridian.native P v₀ (assembly b z.1.2 z.2.1.2 z.2.2)) b z.1.1 z.2.1.1

end
end Finsler.NativeNorthWrappedChart
