module

public import Finsler.Loop.GlobalTimeCupRadius

/-! A single actual global time-cup operation with fixed auxiliary
choices rho=1/4,r=1/2. Comparison with EVERY admissible original pair
is proved. The definition contains neither a metric nor epsilon. -/

@[expose] public section
namespace Finsler.CanonicalGlobalTimeCup
open CategoryTheory SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.BorelLoop Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def product (m p q : ℕ) (a : cohomologyZMod2 (Loops (m + 1)) p)
    (b : cohomologyZMod2 (Loops (m + 1)) q) : cohomologyZMod2 (Loops (m + 1)) ((m + p) + q) :=
  GlobalTimeCupCohomology.product m (by norm_num : 0 < (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) p q a b

theorem product_compare (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    GlobalTimeCupCohomology.product m hρ hρr hr p q a b = product m p q a b :=
  GlobalTimeCupRadius.product_eq m hm p q hρ (by norm_num) hρr (by norm_num) hr (by norm_num) a b

def relative (m p q : ℕ) (hk : (m + 1) + 1 < (m + p) + q)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    RelativeCup.cohomology (fullPair (m + 1)) ((m + p) + q) :=
  ConstantRelativeLift.lift (m + 1) ((m + p) + q) hk (product m p q a b)

theorem relative_compare (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hk : (m + 1) + 1 < (m + p) + q)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    RelativeTimeCup.ofAbsolute m p q hρ hρr hr hk a b = relative m p q hk a b := by
  rw [RelativeTimeCup.ofAbsolute, product_compare m hm p q hρ hρr hr a b]
  rfl

def relativeProduct (m p q : ℕ) (hk : (m + 1) + 1 < (m + p) + q)
    (a : RelativeCup.cohomology (fullPair (m + 1)) p)
    (b : RelativeCup.cohomology (fullPair (m + 1)) q) :
    RelativeCup.cohomology (fullPair (m + 1)) ((m + p) + q) :=
  relative m p q hk (RelativeTimeCup.absolute (m + 1) p a) (RelativeTimeCup.absolute (m + 1) q b)

theorem relative_product_compare (m : ℕ) (hm : 1 ≤ m) (p q : ℕ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ < r) (hr : r ≤ 1) (hk : (m + 1) + 1 < (m + p) + q)
    (a : RelativeCup.cohomology (fullPair (m + 1)) p)
    (b : RelativeCup.cohomology (fullPair (m + 1)) q) :
    RelativeTimeCup.product m p q hρ hρr hr hk a b = relativeProduct m p q hk a b :=
  relative_compare m hm p q hρ hρr hr hk _ _

theorem relative_absolute (m p q : ℕ) (hk : (m + 1) + 1 < (m + p) + q)
    (a : cohomologyZMod2 (Loops (m + 1)) p) (b : cohomologyZMod2 (Loops (m + 1)) q) :
    RelativeTimeCup.absolute (m + 1) ((m + p) + q) (relative m p q hk a b) = product m p q a b := by
  change ConstantRelativeLift.equiv (m + 1) ((m + p) + q) hk
    ((ConstantRelativeLift.equiv (m + 1) ((m + p) + q) hk).symm _) = _
  exact (ConstantRelativeLift.equiv (m + 1) ((m + p) + q) hk).apply_symm_apply _

end
end Finsler.CanonicalGlobalTimeCup
