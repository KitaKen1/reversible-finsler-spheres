module

public import Finsler.Loop.NativeSameLegSquarePrimitive
public import Finsler.Loop.NativeOriginalCoefficientResidual

/-! The ACTUAL six same-leg chronological contributions vanish on
the ORIGINAL double-prism input. All original radii, tested cochains,
source cycles, caps and subdivision maps are retained. -/
@[expose] public section
namespace Finsler.NativeSameLegSegmentZero
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.NativeSameLegThomPrimitive Finsler.NativeMovingThirteen Finsler.NativeMovingGlobalDecomposition
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
  {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
  (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8)

include hm hρ hρr hr hη hr8 hη8

theorem segment_zero (k : Fin 3) (isLong : Bool) :
    segmentEvaluation m P v₀ k (cutIndex isLong) hρ hρr hr hη = 0 := by
  rw [NativeMovingSquareChain.segment_square,
    ← NativeSameLegSquarePrimitive.boundary m hm P v₀ k isLong hρ hρr hr hη hr8 hη8]
  exact DoublePrismCochainBoundary.double_boundary_zero (NativeGlobalTimeSquare.source P) (3 * m) _
    (NativeSameLegSquarePrimitive.at_zero_zero m hm P v₀ k isLong hρ hρr hr hη (by linarith))
    (NativeSameLegSquarePrimitive.at_one_zero m hm P v₀ k isLong hρ hρr hr hη (by linarith))
    (NativeSameLegSquarePrimitive.rotation_zero m hm P v₀ k isLong hρ hρr hr hη (by linarith))

theorem segment_scalar_zero (k : Fin 3) (isLong : Bool) :
    segmentScalar m hm P v₀ k (cutIndex isLong) hρ hρr hr hη = 0 := by
  unfold segmentScalar
  rw [segment_zero m hm P v₀ hρ hρr hr hη hr8 hη8 k isLong]
  rfl

theorem sameLegScalar_zero : sameLegScalar m hm P v₀ hρ hρr hr hη = 0 := by
  have h0 (k : Fin 3) : segmentScalar m hm P v₀ k 0 hρ hρr hr hη = 0 :=
    segment_scalar_zero m hm P v₀ hρ hρr hr hη hr8 hη8 k false
  have h12 (k : Fin 3) : segmentScalar m hm P v₀ k 12 hρ hρr hr hη = 0 :=
    segment_scalar_zero m hm P v₀ hρ hρr hr hη hr8 hη8 k true
  simp only [sameLegScalar, h0, h12, add_zero, Finset.sum_const_zero]

theorem coefficient_one_at_radii : MeridianThetaCutCoefficient.coefficient m hm P v₀ = 1 := by
  rw [NativeOriginalCoefficientResidual.original_coefficient_residual m hm P v₀ hρ hρr hr hη hr8 hη8,
    sameLegScalar_zero m hm P v₀ hρ hρr hr hη hr8 hη8, add_zero]

end
end Finsler.NativeSameLegSegmentZero
