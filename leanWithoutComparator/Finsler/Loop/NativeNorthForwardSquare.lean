module

public import Finsler.Loop.NativeNorthForwardValues

/-! Keep the ACTUAL common global time-square domain and source
permutations in the forward-cell evaluation. The real square prism,
followed by the real coordinate cell and original cut-parameter map,
has the proved value0,1,0. This is still no global cell-sum formula. -/
@[expose] public section
namespace Finsler.NativeNorthForwardSquare
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def cell {n : ℕ} (P : Sphere n) (b : Fin 3) :
    NativeGlobalTimeSquare.squareDomain P ⟶ NativeGlobalTimeSquare.squareDomain P :=
  NativePairDoublePrismSource.reorder P ≫ NativeNorthOrderedCharts.forward P b

theorem pullback_cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    cochainPullback (cell P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b))
      (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) =
    cochainPullback (NativePairDoublePrismSource.reorder P) (3 * m + 2)
      (NativeNorthForwardValues.forwardCochain m P v₀ b hρ hρr hr hη) :=
  (congrArg (fun f => cochainPullback f (3 * m + 2)
    (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη))
    (Category.assoc (NativePairDoublePrismSource.reorder P) (NativeNorthOrderedCharts.forward P b)
      (NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b)))).trans
    (pullback_comp (NativePairDoublePrismSource.reorder P)
      (NativeNorthOrderedCharts.forward P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b))
      (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη))

theorem raw_cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    NativeGlobalTimeSquare.squarePrism (NativeGlobalTimeSquare.source P) (3 * m) ≫
      cochainPullback (cell P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b))
        (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη) =
    NativePairDoublePrismSource.rawComponent P (3 * m) ≫ NativeNorthForwardValues.forwardCochain m P v₀ b hρ hρr hr hη := by
  rw [pullback_cochain]
  change (_ ≫ _) ≫ ((push (NativePairDoublePrismSource.reorder P)).f (3 * m + 2) ≫ _) = _
  simp only [NativePairDoublePrismSource.rawComponent, Category.assoc]

theorem cell_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    ((chains (NativeGlobalTimeSquare.source P)).iCycles (3 * m) ≫
      NativeGlobalTimeSquare.squarePrism (NativeGlobalTimeSquare.source P) (3 * m) ≫
      cochainPullback (cell P b ≫ NativeGlobalTimeSquare.intoCut P v₀ (NativeMeridianMatchingLoci.pairLeft b))
        (3 * m + 2) (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)).hom
      (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) = if b = 1 then 1 else 0 := by
  rw [raw_cochain]
  exact NativeNorthForwardValues.forward_value m hm P v₀ b hρ hρr hr hη hr8 hη8

end
end Finsler.NativeNorthForwardSquare
