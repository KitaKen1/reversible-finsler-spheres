module

public import Finsler.Loop.StrictLengthProductFullCongruence
public import Finsler.Loop.NativeThetaPowers

/-! Arbitrarily small TOTAL product slack for the SAME original Theta
powers, starting from ANY positive-length representative of the SAME
original Theta. Actual full product congruence identifies every new lift
with the old right-associated fullPower; a new detected class is not used. -/
@[expose] public section
namespace Finsler.NativeThetaTightRepresentatives
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def bound (a ε : ℝ) : ℕ → ℝ
  | 0 => a
  | r + 1 => a + (bound a ε r + ε)

theorem bound_positive {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (r : ℕ) :
    0 < bound a ε r := by
  induction r with
  | zero => exact ha
  | succ r ih => exact add_pos ha (add_pos ih hε)

theorem bound_formula (a ε : ℝ) (r : ℕ) :
    bound a ε r = ((r : ℝ) + 1) * a + (r : ℝ) * ε := by
  induction r with
  | zero => simp [bound]
  | succ r ih => simp only [bound, ih, Nat.cast_add, Nat.cast_one]; ring

variable (m : ℕ) (F : ReversibleMetric (m + 1)) {a ε : ℝ}
  (hε : 0 < ε) (z : homologyZMod2 (lengthSpace F a) (NativeThetaPowers.degree m 0))

def power : (r : ℕ) → homologyZMod2 (lengthSpace F (bound a ε r)) (NativeThetaPowers.degree m r)
  | 0 => z
  | r + 1 => StrictLengthLoopProduct.product F (by omega) hε
      (NativeThetaPowers.degree m 0) (NativeThetaPowers.degree m r) (NativeThetaPowers.degree m (r + 1))
      (by change ((m + m) + (m + 1)) + NativeThetaPowers.degree m r =
        (m + 1) + ((m + m) + NativeThetaPowers.degree m r); omega)
      z (power r)

variable (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (ha : 0 < a)
  (hz : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
    (NativeThetaPowers.degree m 0)).hom z = NativeThetaPowers.fullPower m hm F P v₀ 0)
include ha hz

theorem power_full (r : ℕ) :
    (homologyPushZMod2 (LengthFilteredLoopRotation.full F (bound a ε r))
      (NativeThetaPowers.degree m r)).hom (power m F hε z r) =
      NativeThetaPowers.fullPower m hm F P v₀ r := by
  induction r with
  | zero => exact hz
  | succ r ih =>
    have hx : (homologyPushZMod2 (LengthFilteredLoopRotation.full F a)
        (NativeThetaPowers.degree m 0)).hom z =
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F (NativeThetaLengthCut.bound F P v₀))
        (NativeThetaPowers.degree m 0)).hom (NativeThetaLengthCut.input m (by omega) F P v₀) := hz
    exact StrictLengthProductFullCongruence.product_full_congr F (by omega)
      ha (bound_positive ha hε r) (NativeThetaLengthCut.bound_positive F P v₀)
      (NativeThetaPowers.bound_positive m F P v₀ r) hε (by norm_num : (0 : ℝ) < 1)
      (NativeThetaPowers.degree m 0) (NativeThetaPowers.degree m r) (NativeThetaPowers.degree m (r + 1))
      (by change ((m + m) + (m + 1)) + NativeThetaPowers.degree m r =
        (m + 1) + ((m + m) + NativeThetaPowers.degree m r); omega)
      z (NativeThetaLengthCut.input m (by omega) F P v₀)
      (power m F hε z r) (NativeThetaPowers.filteredPower m hm F P v₀ r) hx ih

omit hε in
theorem exists_tight_lift (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : homologyZMod2 (lengthSpace F (((r : ℝ) + 1) * a + δ)) (NativeThetaPowers.degree m r),
      (homologyPushZMod2 (LengthFilteredLoopRotation.full F (((r : ℝ) + 1) * a + δ))
        (NativeThetaPowers.degree m r)).hom w = NativeThetaPowers.fullPower m hm F P v₀ r := by
  let η := δ / ((r : ℝ) + 1)
  have hr : 0 < (r : ℝ) + 1 := by positivity
  have hη : 0 < η := div_pos hδ hr
  have he : ((r : ℝ) + 1) * η = δ := by dsimp [η]; field_simp
  have hb : bound a η r ≤ ((r : ℝ) + 1) * a + δ := by
    rw [bound_formula]
    nlinarith
  refine ⟨(homologyPushZMod2 (LengthFilteredLoopRotation.cut F hb)
    (NativeThetaPowers.degree m r)).hom (power m F hη z r), ?_⟩
  rw [NativePrimitiveCutSurjective.cut_full_apply]
  exact power_full m F hη z hm P v₀ ha hz r

end
end Finsler.NativeThetaTightRepresentatives
