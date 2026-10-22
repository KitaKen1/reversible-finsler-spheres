module

public import Finsler.Loop.NativeGHPowerTimeCupAssociativity
public import Finsler.Loop.CanonicalGHLengthSupport

/-! Multiply the SAME original GH powers into the SAME original power.
Restricted actual associativity suffices; all degree casts are explicit.
This permits block support estimates WITHOUT regrouping Theta products. -/
@[expose] public section
namespace Finsler.NativeGHPowerMultiplication
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.NativeGHPowerTimeCupAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem degree_add (m a b : ℕ) : (m + NativeGHPowers.degree m a) + NativeGHPowers.degree m b =
    NativeGHPowers.degree m (a + b + 1) := by
  simp only [NativeGHPowers.degree_formula]
  ring

theorem cast_zero (X : TopCat.{0}) {i j : ℕ} (h : i = j) :
    CupUnit.absoluteCast X h (0 : cohomologyZMod2 X i) = 0 := by subst j; rfl

theorem pullback_cast {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (A : cohomologyZMod2 Y i) :
    (cohPullback f j).hom (CupUnit.absoluteCast Y h A) =
      CupUnit.absoluteCast X h ((cohPullback f i).hom A) := by subst j; rfl

theorem power_cast (m i j : ℕ) (h : i = j) :
    CupUnit.absoluteCast (Loops (m + 1)) (congrArg (NativeGHPowers.degree m) h)
      (NativeGHPowers.power m i) = NativeGHPowers.power m j := by subst j; rfl

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
include hm F

theorem power_product (a b : ℕ) :
    CupUnit.absoluteCast (Loops (m + 1)) (degree_add m a b)
      (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m a) (NativeGHPowers.degree m b)
        (NativeGHPowers.power m a) (NativeGHPowers.power m b)) = NativeGHPowers.power m (a + b + 1) := by
  induction a with
  | zero =>
    exact power_cast m (b + 1) (0 + b + 1) (by omega)
  | succ a ih =>
    have hi : a + 1 + b + 1 = (a + b + 1) + 1 := by omega
    have hk : 1 ≤ NativeGHPowers.degree m b := by
      have h := NativeGHPowers.degree_ge m b
      omega
    have hL : NativeNestedTimeCupAlignment.leftDegree m 0 a (NativeGHPowers.degree m b) =
        NativeGHPowers.degree m (a + 1 + b + 1) := by
      change (m + ((m + m) + NativeGHPowers.degree m a)) + NativeGHPowers.degree m b = _
      simp only [NativeGHPowers.degree_formula]
      ring
    have hR : NativeNestedTimeCupAlignment.rightDegree m 0 a (NativeGHPowers.degree m b) =
        NativeGHPowers.degree m (a + 1 + b + 1) := by
      change (m + m) + ((m + NativeGHPowers.degree m a) + NativeGHPowers.degree m b) = _
      simp only [NativeGHPowers.degree_formula]
      ring
    have hassoc := associativity_at_degree m hm F 0 a (NativeGHPowers.degree m b) hk
      (NativeGHPowers.power m b) (NativeGHPowers.degree m (a + 1 + b + 1)) hL hR
    change CupUnit.absoluteCast (Loops (m + 1)) (degree_add m (a + 1) b)
      (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m (a + 1)) (NativeGHPowers.degree m b)
        (NativeGHPowers.power m (a + 1)) (NativeGHPowers.power m b)) = _ at hassoc
    rw [hassoc]
    have he := congrArg (fun B => CanonicalGlobalTimeCup.product m m (NativeGHPowers.degree m (a + b + 1))
      (MeridianLoopClass.H1TransgressionClass m) B) ih
    rw [product_cast_right] at he
    have ht := congrArg (NativeGHPowers.degree m) hi.symm
    have he' := congrArg (CupUnit.absoluteCast (Loops (m + 1)) ht) he
    rw [cast_trans] at he'
    exact he'.trans (power_cast m ((a + b + 1) + 1) (a + 1 + b + 1) hi.symm)

theorem support_add (a b : ℕ) {L M R : ℝ}
    (hL : (cohPullback (LengthFilteredLoopRotation.full F L) (NativeGHPowers.degree m a)).hom
      (NativeGHPowers.power m a) = 0)
    (hM : (cohPullback (LengthFilteredLoopRotation.full F M) (NativeGHPowers.degree m b)).hom
      (NativeGHPowers.power m b) = 0) (hR : R < L + M) :
    (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m (a + b + 1))).hom
      (NativeGHPowers.power m (a + b + 1)) = 0 := by
  rw [← power_product m hm F a b, pullback_cast]
  rw [CanonicalGHLengthSupport.product_restriction_zero (by omega) F _ _ _ _ hL hM hR, cast_zero]

end
end Finsler.NativeGHPowerMultiplication
