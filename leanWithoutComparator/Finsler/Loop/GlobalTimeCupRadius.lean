module

public import Finsler.Loop.GlobalTimeCupNearRadius
public import Finsler.Loop.GlobalTimeCupSupportRadius

/-! Remove BOTH auxiliary radii of the actual global and high-degree
relative time cup. Use a common smaller support radius and compare
both near spaces inside their actual maximum-radius near space. -/

@[expose] public section
namespace Finsler.GlobalTimeCupRadius
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem product_eq (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ₀ ρ₁ r₀ r₁ : ℝ}
    (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀r : ρ₀ < r₀) (h₁r : ρ₁ < r₁)
    (hr₀ : r₀ ≤ 1) (hr₁ : r₁ ≤ 1)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    GlobalTimeCupCohomology.product m h₀ h₀r hr₀ p q a b =
      GlobalTimeCupCohomology.product m h₁ h₁r hr₁ p q a b := by
  let ρ := min ρ₀ ρ₁
  let r := max r₀ r₁
  have hρ : 0 < ρ := lt_min h₀ h₁
  have hρ₀ : ρ < r₀ := (min_le_left _ _).trans_lt h₀r
  have hρ₁ : ρ < r₁ := (min_le_right _ _).trans_lt h₁r
  have hr : r ≤ 1 := max_le hr₀ hr₁
  calc
    _ = GlobalTimeCupCohomology.product m hρ hρ₀ hr₀ p q a b :=
      GlobalTimeCupSupportRadius.product_eq m hm h₀ hρ h₀r hρ₀ hr₀ p q a b
    _ = GlobalTimeCupCohomology.product m hρ (hρ₀.trans_le (le_max_left _ _)) hr p q a b :=
      GlobalTimeCupNearRadius.product_eq m p q hρ hρ₀ (le_max_left _ _) hr₀ hr a b
    _ = GlobalTimeCupCohomology.product m hρ hρ₁ hr₁ p q a b :=
      (GlobalTimeCupNearRadius.product_eq m p q hρ hρ₁ (le_max_right _ _) hr₁ hr a b).symm
    _ = _ := GlobalTimeCupSupportRadius.product_eq m hm hρ h₁ hρ₁ h₁r hr₁ p q a b

theorem relative_ofAbsolute_eq (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ₀ ρ₁ r₀ r₁ : ℝ}
    (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀r : ρ₀ < r₀) (h₁r : ρ₁ < r₁)
    (hr₀ : r₀ ≤ 1) (hr₁ : r₁ ≤ 1) (hk : (m + 1) + 1 < (m + p) + q)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    RelativeTimeCup.ofAbsolute m p q h₀ h₀r hr₀ hk a b =
      RelativeTimeCup.ofAbsolute m p q h₁ h₁r hr₁ hk a b := by
  rw [RelativeTimeCup.ofAbsolute, RelativeTimeCup.ofAbsolute,
    product_eq m hm p q h₀ h₁ h₀r h₁r hr₀ hr₁ a b]

theorem relative_product_eq (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ₀ ρ₁ r₀ r₁ : ℝ}
    (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁) (h₀r : ρ₀ < r₀) (h₁r : ρ₁ < r₁)
    (hr₀ : r₀ ≤ 1) (hr₁ : r₁ ≤ 1) (hk : (m + 1) + 1 < (m + p) + q)
    (a : RelativeCup.cohomology (fullPair (m + 1)) p)
    (b : RelativeCup.cohomology (fullPair (m + 1)) q) :
    RelativeTimeCup.product m p q h₀ h₀r hr₀ hk a b =
      RelativeTimeCup.product m p q h₁ h₁r hr₁ hk a b :=
  relative_ofAbsolute_eq m hm p q h₀ h₁ h₀r h₁r hr₀ hr₁ hk _ _

end
end Finsler.GlobalTimeCupRadius
