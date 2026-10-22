module

public import Finsler.Loop.NativeNorthWrappedValues

/-! Keep the ACTUAL common global time-square domain and source
permutations in the wrapped-cell evaluation. The real square prism,
followed by the real coordinate cell and original cut-parameter map,
has the proved value1,0,1. This is still no global cell-sum formula. -/
@[expose] public section
namespace Finsler.NativeNorthWrappedSquare
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def cell {n : ℕ} (P : Sphere n) (b : Fin 3) :
    NativeGlobalTimeSquare.squareDomain P ⟶ NativeGlobalTimeSquare.squareDomain P :=
  NativePairDoublePrismSource.reorder P ≫ NativeNorthOrderedCharts.wrapped P b

theorem pullback_cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    cochainPullback (cell P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b))
      (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) =
    cochainPullback (NativePairDoublePrismSource.reorder P) (3 * m + 2)
      (NativeNorthWrappedValues.wrappedCochain m P v₀ b hρ hρr hr hη) :=
  (congrArg (fun f => cochainPullback f (3 * m + 2)
    (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη))
    (Category.assoc (NativePairDoublePrismSource.reorder P) (NativeNorthOrderedCharts.wrapped P b)
      (NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b)))).trans
    (pullback_comp (NativePairDoublePrismSource.reorder P)
      (NativeNorthOrderedCharts.wrapped P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b))
      (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη))

theorem raw_cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    NativeGlobalTimeSquare.squarePrism (NativeGlobalTimeSquare.source P) (3 * m) ≫
      cochainPullback (cell P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b))
        (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) =
    NativePairDoublePrismSource.rawComponent P (3 * m) ≫ NativeNorthWrappedValues.wrappedCochain m P v₀ b hρ hρr hr hη := by
  rw [pullback_cochain]
  change (_ ≫ _) ≫ ((push (NativePairDoublePrismSource.reorder P)).f (3 * m + 2) ≫ _) = _
  simp only [NativePairDoublePrismSource.rawComponent, Category.assoc]

theorem cell_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    ((chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      NativeGlobalTimeSquare.squarePrism (NativeGlobalTimeSquare.source P) (3 * m) ≫
      cochainPullback (cell P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairRight b))
        (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)).hom
      (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) = if b = 1 then 0 else 1 := by
  rw [raw_cochain]
  exact NativeNorthWrappedValues.wrapped_value m hm P v₀ b hρ hρr hr hη hr8 hη8

theorem paired_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativeNorthForwardValues.forwardPairing m hm P v₀ b hρ hρr hr hη +
      NativeNorthWrappedValues.wrappedPairing m hm P v₀ b hρ hρr hr hη = 1 := by
  rw [NativeNorthForwardValues.forward_value m hm P v₀ b hρ hρr hr hη hr8 hη8,
    NativeNorthWrappedValues.wrapped_value m hm P v₀ b hρ hρr hr hη hr8 hη8]
  by_cases hb : b = 1
  · rw [ite_eq_left hb, ite_eq_left hb, add_zero]
  · rw [ite_eq_right hb, ite_eq_right hb, zero_add]

theorem ordered_sum_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (∑ b : Fin 3, (NativeNorthForwardValues.forwardPairing m hm P v₀ b hρ hρr hr hη +
      NativeNorthWrappedValues.wrappedPairing m hm P v₀ b hρ hρr hr hη)) = 1 := by
  rw [Finset.sum_add_distrib, NativeNorthForwardValues.forward_sum_one m hm P v₀ hρ hρr hr hη hr8 hη8,
    NativeNorthWrappedValues.wrapped_sum_zero m hm P v₀ hρ hρr hr hη hr8 hη8, add_zero]

end
end Finsler.NativeNorthWrappedSquare
