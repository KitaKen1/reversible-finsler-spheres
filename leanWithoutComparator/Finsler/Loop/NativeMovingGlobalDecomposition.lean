module

public import Finsler.Loop.NativeMovingOrderedChartAlignment

/-! Exact decomposition of the OLD GLOBAL scalar into the SIX actual
chronological distinct-leg evaluations and the SIX partial same-leg
evaluations. These are the original clock segments, not substituted
cell values. Source/time input transport and same-leg vanishing remain
explicit mathematical tasks after this theorem. -/
@[expose] public section
namespace Finsler.NativeMovingGlobalDecomposition
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.BorelLoop
open Finsler.NativeMovingThirteen Finsler.NativeMovingOrderedChartAlignment
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

def segmentScalar (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) (j : Fin 13)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) : ZMod 2 :=
  (segmentEvaluation m P v₀ k j hρ hρr hr hη).hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)

def sameLegScalar (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) : ZMod 2 :=
  ∑ k : Fin 3, (segmentScalar m hm P v₀ k 0 hρ hρr hr hη + segmentScalar m hm P v₀ k 12 hρ hρr hr hη)

def distinctLegScalar (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) : ZMod 2 :=
  ∑ b : Fin 3,
    (segmentScalar m hm P v₀ (NativeMeridianMatchingLoci.pairLeft b) (forwardSegment b) hρ hρr hr hη +
     segmentScalar m hm P v₀ (NativeMeridianMatchingLoci.pairRight b) (wrappedSegment b) hρ hρr hr hη)

theorem original_coefficient (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (hη2 : η ≤ 1 / 2) (hηr : η + r ≤ 3 / 5) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      distinctLegScalar m hm P v₀ hρ hρr hr hη + sameLegScalar m hm P v₀ hρ hρr hr hη := by
  rw [NativeMovingNonnorthZero.coefficient_twelve m hm P v₀ hρ hρr hr hη hη2 hηr]
  change (∑ k : Fin 3,
    (segmentScalar m hm P v₀ k 0 hρ hρr hr hη + segmentScalar m hm P v₀ k 4 hρ hρr hr hη +
     segmentScalar m hm P v₀ k 8 hρ hρr hr hη + segmentScalar m hm P v₀ k 12 hρ hρr hr hη)) = _
  dsimp only [distinctLegScalar, sameLegScalar]
  simp only [Fin.sum_univ_three]
  norm_num only [forwardSegment, wrappedSegment, NativeMeridianMatchingLoci.pairLeft,
    NativeMeridianMatchingLoci.pairRight, Fin.reduceEq, ite_true, ite_false]
  abel

theorem original_coefficient_eighth (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    {ρ r η : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η)
    (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      distinctLegScalar m hm P v₀ hρ hρr hr hη + sameLegScalar m hm P v₀ hρ hρr hr hη :=
  original_coefficient m hm P v₀ hρ hρr hr hη (by linarith) (by linarith)

end
end Finsler.NativeMovingGlobalDecomposition
