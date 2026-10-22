module

public import Finsler.Loop.NativePrimitiveCutSurjective
public import Finsler.Loop.MeridianPrimitiveNonzero

/-! Genuine RIGHT-ASSOCIATED positive powers of the actual primitive
under the EXISTING geometric time-cup/GH operation. Index r means r+1
factors. Their degrees are (2r+1)(n-1). Actual global D_omega
surjectivity proves actual left multiplication injective, so every
power and its genuine constant-relative lift are nonzero. No global
associativity or high-power UNIT identity is asserted. -/
@[expose] public section
namespace Finsler.NativeGHPowers
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def degree (m : ℕ) : ℕ → ℕ
  | 0 => m
  | r + 1 => (m + m) + degree m r

theorem degree_formula (m r : ℕ) : degree m r = (2 * r + 1) * m := by
  induction r with
  | zero => simp [degree]
  | succ r ih => simp only [degree, ih]; ring

theorem degree_ge (m r : ℕ) : m ≤ degree m r := by
  induction r with
  | zero => exact le_rfl
  | succ r ih => change m ≤ (m + m) + degree m r; omega

theorem degree_strictMono (m : ℕ) (hm : 2 ≤ m) : StrictMono (degree m) := by
  apply strictMono_nat_of_lt_succ
  intro r
  change degree m r < (m + m) + degree m r
  omega

def power (m : ℕ) : (r : ℕ) → cohomologyZMod2 (Loops (m + 1)) (degree m r)
  | 0 => MeridianLoopClass.H1TransgressionClass m
  | r + 1 => CanonicalGlobalTimeCup.product m m (degree m r)
      (MeridianLoopClass.H1TransgressionClass m) (power m r)

def relativePower (m : ℕ) (hm : 2 ≤ m) :
    (r : ℕ) → RelativeCup.cohomology (fullPair (m + 1)) (degree m r)
  | 0 => MeridianLoopClass.relativeTransgressionClass m
  | r + 1 => CanonicalGlobalTimeCup.relativeProduct m m (degree m r)
      (by have hd := degree_ge m r; omega)
      (MeridianLoopClass.relativeTransgressionClass m) (relativePower m hm r)

theorem relativePower_absolute (m : ℕ) (hm : 2 ≤ m) (r : ℕ) :
    RelativeTimeCup.absolute (m + 1) (degree m r) (relativePower m hm r) = power m r := by
  have hω : RelativeTimeCup.absolute (m + 1) m (MeridianLoopClass.relativeTransgressionClass m) =
      MeridianLoopClass.H1TransgressionClass m := MeridianLoopClass.relative_absolute m (by omega)
  induction r with
  | zero => exact hω
  | succ r ih =>
    change RelativeTimeCup.absolute (m + 1) ((m + m) + degree m r)
      (CanonicalGlobalTimeCup.relativeProduct m m (degree m r)
        (by have hd := degree_ge m r; omega)
        (MeridianLoopClass.relativeTransgressionClass m) (relativePower m hm r)) =
      CanonicalGlobalTimeCup.product m m (degree m r)
        (MeridianLoopClass.H1TransgressionClass m) (power m r)
    rw [CanonicalGlobalTimeCup.relativeProduct, CanonicalGlobalTimeCup.relative_absolute, hω, ih]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)
include hm F P v₀

theorem multiply_injective (q : ℕ) :
    Function.Injective (fun b : cohomologyZMod2 (Loops (m + 1)) q =>
      CanonicalGlobalTimeCup.product m m q (MeridianLoopClass.H1TransgressionClass m) b) := by
  intro a b hab
  apply (kroneckerMap_bijective (Loops (m + 1)) q).1
  apply LinearMap.ext
  intro z
  obtain ⟨w, hw⟩ := NativePrimitiveCutSurjective.map_surjective m hm F P v₀ q z
  rw [← hw]
  exact (CanonicalGlobalSelfCut.pairing m m q _ a w).trans
    ((congrArg (fun c => (kroneckerMap (Loops (m + 1)) ((m + m) + q)).hom c w) hab).trans
      (CanonicalGlobalSelfCut.pairing m m q _ b w).symm)

theorem power_ne_zero (r : ℕ) : power m r ≠ 0 := by
  induction r with
  | zero => exact MeridianPrimitiveNonzero.H1_transgression_ne_zero m (by omega) P v₀
  | succ r ih =>
    intro hz
    have hzero : CanonicalGlobalTimeCup.product m m (degree m r)
        (MeridianLoopClass.H1TransgressionClass m) 0 = 0 := by
      rw [← CanonicalTimeCupBilinear.bilinear_apply]
      exact map_zero _
    apply ih
    apply multiply_injective m hm F P v₀ (degree m r)
    exact hz.trans hzero.symm

theorem relativePower_ne_zero (r : ℕ) : relativePower m hm r ≠ 0 := by
  intro hz
  have he := relativePower_absolute m hm r
  rw [hz, map_zero] at he
  exact power_ne_zero m hm F P v₀ r he.symm

end
end Finsler.NativeGHPowers
