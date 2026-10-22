module

public import Finsler.Loop.NativeGHPowerMultiplication
public import Finsler.Loop.NativeGHPowerSharpSupport

/-! Optimize support using any actual support of a fixed GH block, retaining
all original powers. The remainder uses the primitive support without halving.
No regrouping or associativity of Theta products is needed. -/
@[expose] public section
namespace Finsler.NativeGHBlockSupport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

theorem support_transport (m : ℕ) (F : ReversibleMetric (m + 1)) (R : ℝ)
    (i j : ℕ) (h : i = j)
    (hi : (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m i)).hom
      (NativeGHPowers.power m i) = 0) :
    (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m j)).hom
      (NativeGHPowers.power m j) = 0 := by subst j; exact hi

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (b : ℕ) {B L : ℝ}
  (hB : (cohPullback (LengthFilteredLoopRotation.full F B) (NativeGHPowers.degree m b)).hom
    (NativeGHPowers.power m b) = 0)
  (hL : (cohPullback (LengthFilteredLoopRotation.full F L) m).hom
    (MeridianLoopClass.H1TransgressionClass m) = 0)
include hm hB hL

theorem blocks_below (k t : ℕ) {R : ℝ}
    (hR : R < (k : ℝ) * B + ((t : ℝ) + 1) * L) :
    (cohPullback (LengthFilteredLoopRotation.full F R)
      (NativeGHPowers.degree m (k * (b + 1) + t))).hom
      (NativeGHPowers.power m (k * (b + 1) + t)) = 0 := by
  induction k generalizing R with
  | zero =>
    have hbase := NativeGHPowerSharpSupport.power_below m hm F hL t (R := R) (by simpa using hR)
    exact support_transport m F R t (0 * (b + 1) + t) (by omega) hbase
  | succ k ih =>
    let M := (R - B + ((k : ℝ) * B + ((t : ℝ) + 1) * L)) / 2
    have hM : M < (k : ℝ) * B + ((t : ℝ) + 1) * L := by
      dsimp [M]; push_cast at hR; nlinarith
    have hRM : R < B + M := by dsimp [M]; push_cast at hR; nlinarith
    have h := NativeGHPowerMultiplication.support_add m hm F b (k * (b + 1) + t) hB (ih hM) hRM
    have hi : b + (k * (b + 1) + t) + 1 = (k + 1) * (b + 1) + t := by ring
    exact support_transport m F R _ _ hi h

/-- Every original GH power is covered, including the nondivisible tail. -/
theorem quotient_below (r : ℕ) {R : ℝ}
    (hR : R < (r / (b + 1) : ℕ) * B + ((r % (b + 1) : ℕ) + 1 : ℝ) * L) :
    (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r) = 0 := by
  have h := blocks_below m hm F b hB hL (r / (b + 1)) (r % (b + 1)) hR
  have hi : r / (b + 1) * (b + 1) + r % (b + 1) = r := Nat.div_add_mod' r (b + 1)
  exact support_transport m F R _ _ hi h

end
end Finsler.NativeGHBlockSupport
