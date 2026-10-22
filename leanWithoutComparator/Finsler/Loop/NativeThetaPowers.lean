module

public import Finsler.Loop.NativePrimitiveCutSurjective
public import Finsler.Loop.NativeDegreeNLoopHomology

/-! Genuine RIGHT-ASSOCIATED positive powers of the SAME original
Theta under the EXISTING strict-length loop product. Index r means
r+1 factors. Actual D_omega removes one factor, so all powers are
nonzero. No loop-product associativity or high-power UNIT is assumed. -/
@[expose] public section
namespace Finsler.NativeThetaPowers
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def degree (m : ℕ) : ℕ → ℕ
  | 0 => (m + m) + (m + 1)
  | r + 1 => (m + m) + degree m r

theorem degree_formula (m r : ℕ) : degree m r = (m + 1) + (r + 1) * (m + m) := by
  induction r with
  | zero => simp [degree]; omega
  | succ r ih => simp only [degree, ih]; ring

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def bound : ℕ → ℝ
  | 0 => NativeThetaLengthCut.bound F P v₀
  | r + 1 => NativeThetaLengthCut.bound F P v₀ + (bound r + 1)

theorem bound_positive (r : ℕ) : 0 < bound m F P v₀ r := by
  induction r with
  | zero => exact NativeThetaLengthCut.bound_positive F P v₀
  | succ r ih =>
    change 0 < NativeThetaLengthCut.bound F P v₀ + (bound m F P v₀ r + 1)
    linarith [NativeThetaLengthCut.bound_positive F P v₀]

theorem bound_formula (r : ℕ) : bound m F P v₀ r =
    NativeThetaLengthCut.bound F P v₀ + (r : ℝ) * (NativeThetaLengthCut.bound F P v₀ + 1) := by
  induction r with
  | zero => simp [bound]
  | succ r ih => simp only [bound, ih, Nat.cast_add, Nat.cast_one]; ring

def filteredPower : (r : ℕ) → homologyZMod2 (lengthSpace F (bound m F P v₀ r)) (degree m r)
  | 0 => NativeThetaLengthCut.input m (by omega) F P v₀
  | r + 1 => NativePrimitiveCutSurjective.raised m hm F P v₀ (bound m F P v₀ r)
      (by norm_num : (0 : ℝ) < 1) (degree m r) (filteredPower r)

def fullPower (r : ℕ) : homologyZMod2 (Loops (m + 1)) (degree m r) :=
  (homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound m F P v₀ r)) (degree m r)).hom
    (filteredPower m hm F P v₀ r)

theorem full_zero : fullPower m hm F P v₀ 0 = MeridianThetaCutCoefficient.thetaInput m (by omega) P v₀ :=
  NativeThetaLengthCut.input_full m (by omega) F P v₀

theorem full_succ_cut (r : ℕ) :
    (CanonicalGlobalSelfCut.map m m (degree m r) (MeridianLoopClass.H1TransgressionClass m)).hom
      (fullPower m hm F P v₀ (r + 1)) = fullPower m hm F P v₀ r :=
  NativePrimitiveCutSurjective.raised_cut_full m hm F P v₀ (bound m F P v₀ r)
    (bound_positive m F P v₀ r) (by norm_num) (degree m r) (filteredPower m hm F P v₀ r)

theorem full_zero_cut_unit :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
      ((CanonicalGlobalSelfCut.map m m (m + 1) (MeridianLoopClass.H1TransgressionClass m)).hom
        (fullPower m hm F P v₀ 0)) = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  rw [full_zero]
  exact NativeConstantUnitFromPathMV.original_UNIT m hm P v₀

theorem fullPower_ne_zero (r : ℕ) : fullPower m hm F P v₀ r ≠ 0 := by
  induction r with
  | zero =>
    rw [full_zero]
    exact NativeThetaCoefficientOne.thetaInput_ne_zero m (by omega) P v₀
  | succ r ih =>
    intro hz
    have he := full_succ_cut m hm F P v₀ r
    rw [hz, map_zero] at he
    exact ih he.symm

theorem filteredPower_ne_zero (r : ℕ) : filteredPower m hm F P v₀ r ≠ 0 := by
  intro hz
  apply fullPower_ne_zero m hm F P v₀ r
  change (homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound m F P v₀ r)) (degree m r)).hom
    (filteredPower m hm F P v₀ r) = 0
  rw [hz, map_zero]

end
end Finsler.NativeThetaPowers
