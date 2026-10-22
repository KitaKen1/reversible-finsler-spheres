module

public import Finsler.Loop.NativeGraphFundamentalScalar

/-! Numeric values of the SAME ORIGINAL native double-prism branches:
0,1,0 at the SAME original rho<r,r,eta<=1/8. These are actual full
supported-cap pairings, not tested-factor conventions. No OLD GLOBAL
Theta branch-sum/gluing identity is assumed or concluded here. -/
@[expose] public section
namespace Finsler.NativeOriginalBranchValues
open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.NativePairRelativeSphereTransport
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1100000

theorem nonadjacent_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativePairDoublePrismSource.branchPairing m hm P v₀ 1 hρ hρr hr hη (by linarith) (by linarith) = 1 :=
  (NativeGraphBranchPairing.original_branchPairing_fundamental m hm P v₀ 1 hρ hρr hr hη (by linarith) (by linarith)).trans
    ((congrArg (fun a => (kroneckerMap (graphSpace P) (3 * m + 2)).hom a
      (NativeDoubleFundamentalImage.fundamentalImage m hm P))
      (NativeExplicitGraphClass.original_absolute_class m hm P v₀ hρ hρr hr hη hr8 hη8)).trans
        (NativeGraphFundamentalScalar.scalar_one m hm P v₀))

theorem branch_value (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (b : Fin 3) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativePairDoublePrismSource.branchPairing m hm P v₀ b hρ hρr hr hη (by linarith) (by linarith) =
      if b = 1 then 1 else 0 := by
  by_cases hb : b = 1
  · subst b
    exact (nonadjacent_one m hm P v₀ hρ hρr hr hη hr8 hη8).trans (ite_eq_left rfl).symm
  · exact (NativeGraphLocalCapReduction.original_branchPairing_zero m hm P v₀ b hb hρ hρr hr hη hr8 hη8).trans
      (ite_eq_right hb).symm

theorem native_branch_sum_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    (∑ b : Fin 3, NativePairDoublePrismSource.branchPairing m hm P v₀ b hρ hρr hr hη (by linarith) (by linarith)) = 1 := by
  rw [Fin.sum_univ_three,
    NativeGraphLocalCapReduction.original_branchPairing_zero m hm P v₀ 0 (by decide) hρ hρr hr hη hr8 hη8,
    nonadjacent_one m hm P v₀ hρ hρr hr hη hr8 hη8,
    NativeGraphLocalCapReduction.original_branchPairing_zero m hm P v₀ 2 (by decide) hρ hρr hr hη hr8 hη8,
    zero_add, add_zero]

theorem native_input_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativePairDoublePrismSource.inputClass m hm P v₀ ≠ 0 := by
  intro hz
  have he := nonadjacent_one m hm P v₀ (ρ := 1 / 64) (r := 1 / 32) (η := 1 / 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2) _
    (NativePairDoublePrismSource.inputClass m hm P v₀) = 1 at he
  rw [hz, map_zero] at he
  exact zero_ne_one he

theorem graph_input_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    graphInputClass m hm P v₀ ≠ 0 := by
  intro hz
  have he := NativeGraphBranchPairing.original_branchPairing_graph m hm P v₀ 1
    (ρ := 1 / 64) (r := 1 / 32) (η := 1 / 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hv := nonadjacent_one m hm P v₀ (ρ := 1 / 64) (r := 1 / 32) (η := 1 / 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h := hv.symm.trans he
  rw [hz, map_zero] at h
  exact one_ne_zero h

theorem native_primitive_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) {ρ r η : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hη : 0 < η) (hr8 : r ≤ 1 / 8) (hη8 : η ≤ 1 / 8) :
    NativePairDoublePrismSource.primitiveClass m P v₀ 1 hρ hρr hr hη (by linarith) (by linarith) ≠ 0 := by
  intro hz
  have he := nonadjacent_one m hm P v₀ hρ hρr hr hη hr8 hη8
  change RelativeKronecker.comparison (NativePairBoundaryRelativeCut.pair P v₀) (3 * m + 2)
    (NativePairDoublePrismSource.primitiveClass m P v₀ 1 hρ hρr hr hη (by linarith) (by linarith)) _ = 1 at he
  rw [hz, map_zero, LinearMap.zero_apply] at he
  exact zero_ne_one he

end
end Finsler.NativeOriginalBranchValues
