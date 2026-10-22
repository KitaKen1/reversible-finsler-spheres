module

public import Finsler.Loop.NativeGlobalTimeSquare
public import Finsler.Loop.GlobalCutTimePrismAlignment

/-! The SAME OLD GLOBAL coefficient is evaluated on the actual
ordinary double-time prism and SAME original pre-time cut cochain.
This exposes the precise common source for ordered branch comparison;
no branch decomposition or square-boundary relative lift is assumed. -/
@[expose] public section
namespace Finsler.NativeGlobalDoublePrismCoefficient
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.NativeGlobalTimeSquare
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

def cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    singularCochainGroup (ZMod 2) (source P) (3 * m) :=
  squarePrism (source P) (3 * m) ≫
    cochainPullback (intoCut P v₀ k) (3 * m + 2)
      (GlobalCutTimePrismAlignment.parameterCochain m (NorthMeridianEvaluationPoint.target P v₀) hρ hρr hr hη)

theorem original_north_cochain (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) :
    NorthRotationPrismLocalization.northCochain m P v₀ k hη hρ hρr hr = cochain m P v₀ k hρ hρr hr hη := by
  unfold NorthRotationPrismLocalization.northCochain
  rw [GlobalCutTimePrismAlignment.original_cast_timecup_prism, ← Category.assoc, double_prism]
  rfl

theorem closed (m : ℕ) (P : Sphere (m + 1)) (v₀ : equator P) (k : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    cochainCoboundary (ZMod 2) (source P) (3 * m) (cochain m P v₀ k hρ hρr hr hη) = 0 :=
  (congrArg (cochainCoboundary (ZMod 2) (source P) (3 * m))
    (original_north_cochain m P v₀ k hρ hρr hr hη).symm).trans
      (NorthRotationPrismLocalization.north_closed m P v₀ k hη hη2 hρ hρr hr)

theorem original_coefficient_raw (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      (∑ k : Fin 3, (chains (source P)).iCycles (3 * m) ≫ cochain m P v₀ k hρ hρr hr hη).hom
        (NativeThetaCoefficientSixQuarters.sourceCycle m hm P) := by
  have hs : (∑ k : Fin 3, (chains (source P)).iCycles (3 * m) ≫
      NorthRotationPrismLocalization.northCochain m P v₀ k hη hρ hρr hr) =
      ∑ k : Fin 3, (chains (source P)).iCycles (3 * m) ≫ cochain m P v₀ k hρ hρr hr hη := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg ((chains (source P)).iCycles (3 * m) ≫ ·) (original_north_cochain m P v₀ k hρ hρr hr hη)
  exact (NativeThetaCoefficientThreeNorth.coefficient_three_north_prisms m hm P v₀ hη hη2 hρ hρr hr).trans
    (congrArg (fun f => f.hom (NativeThetaCoefficientSixQuarters.sourceCycle m hm P)) hs)

theorem original_coefficient_pairings (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    MeridianThetaCutCoefficient.coefficient m hm P v₀ =
      ∑ k : Fin 3, (kroneckerMap (source P) (3 * m)).hom
        (cocycleClass _ _ (cochain m P v₀ k hρ hρr hr hη) (closed m P v₀ k hρ hρr hr hη hη2))
        (BasedMeridianProducts.tripleSource m hm P) := by
  have he := NativeThetaCoefficientThreeNorth.coefficient_three_north_pairings m hm P v₀ hη hη2 hρ hρr hr
  apply he.trans
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun a => (kroneckerMap (source P) (3 * m)).hom a (BasedMeridianProducts.tripleSource m hm P))
    (CochainClass.classOf_congr (cochainCxZMod2 (source P)) (3 * m)
      (original_north_cochain m P v₀ k hρ hρr hr hη) _ _)

end
end Finsler.NativeGlobalDoublePrismCoefficient
