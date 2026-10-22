module

public import Finsler.Loop.NativeThetaSpectralLength

/-! Two-sided one-step control of the ACTUAL critical lengths of the
SAME right-associated Theta powers. The lower bound uses the ORIGINAL
primitive filtered cut; the upper bound uses full product congruence.
No associativity or fixed-sublevel injectivity is assumed. -/
@[expose] public section
namespace Finsler.NativeThetaSpectralStep
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge
open Finsler.NativeThetaSpectralLength
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem cut_lift (r : ℕ) {a L ε : ℝ}
    (ha : a ∈ lifts m hm F P v₀ (r + 1))
    (hL : L ∈ NativeGHSpectralSupport.supports m F 0) (hε : 0 < ε) :
    a - L + 3 * ε ∈ lifts m hm F P v₀ r := by
  obtain ⟨z, hz⟩ := ha
  let T := NativeHighPowerFilteredCut.supportedCochain m F 0 hL
  have hT := NativeHighPowerFilteredCut.supported_closed m F 0 hL
  have hs := NativeHighPowerFilteredCut.supported_zero m F 0 hL
  let w := ((FilteredPrismSelfCut.canonicalOperation m m F hε T hT hs (a := a)).homology
    (NativeThetaPowers.degree m r)).hom z
  refine ⟨w, ?_⟩
  have he := CanonicalGlobalSelfCutFiltered.original_filtered m (by omega) m F hε
    T hT hs (NativeThetaPowers.degree m r) z
  have hc : cocycleClass (Loops (m + 1)) m T hT = MeridianLoopClass.H1TransgressionClass m :=
    NativeHighPowerFilteredCut.supported_class m F 0 hL
  rw [hc] at he
  exact he.trans ((congrArg (CanonicalGlobalSelfCut.map m m (NativeThetaPowers.degree m r)
    (MeridianLoopClass.H1TransgressionClass m)).hom hz).trans
      (NativeThetaPowers.full_succ_cut m hm F P v₀ r))

theorem support_step_le (r : ℕ) {a L : ℝ}
    (ha : a ∈ lifts m hm F P v₀ (r + 1))
    (hL : L ∈ NativeGHSpectralSupport.supports m F 0) :
    level m hm F P v₀ r + L ≤ a := by
  by_contra h
  let ε := (level m hm F P v₀ r + L - a) / 6
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hl := level_le_lift m hm F P v₀ r (cut_lift m hm F P v₀ r ha hL hε)
  dsimp [ε] at hl
  linarith

theorem level_succ_lower (r : ℕ) :
    level m hm F P v₀ r + NativeGHSpectralSupport.level m F 0 ≤ level m hm F P v₀ (r + 1) := by
  apply le_csInf (lifts_nonempty m hm F P v₀ (r + 1))
  intro a ha
  have h : NativeGHSpectralSupport.level m F 0 ≤ a - level m hm F P v₀ r := by
    apply csSup_le (NativeGHSpectralSupport.supports_nonempty m hm F 0)
    intro L hL
    linarith [support_step_le m hm F P v₀ r ha hL]
  linarith

theorem product_lift (r : ℕ) {a b ε : ℝ}
    (ha : a ∈ lifts m hm F P v₀ 0) (hb : b ∈ lifts m hm F P v₀ r) (hε : 0 < ε) :
    a + (b + ε) ∈ lifts m hm F P v₀ (r + 1) := by
  have hapos := (level_positive m hm F P v₀ 0).trans_le (level_le_lift m hm F P v₀ 0 ha)
  have hbpos := (level_positive m hm F P v₀ r).trans_le (level_le_lift m hm F P v₀ r hb)
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  have hd : NativeThetaPowers.degree m 0 + NativeThetaPowers.degree m r =
      (m + 1) + NativeThetaPowers.degree m (r + 1) := by
    change ((m + m) + (m + 1)) + NativeThetaPowers.degree m r =
      (m + 1) + ((m + m) + NativeThetaPowers.degree m r)
    omega
  refine ⟨StrictLengthLoopProduct.product F (by omega) hε
    (NativeThetaPowers.degree m 0) (NativeThetaPowers.degree m r)
    (NativeThetaPowers.degree m (r + 1)) hd x y, ?_⟩
  exact StrictLengthProductFullCongruence.product_full_congr F (by omega)
    hapos hbpos (NativeThetaLengthCut.bound_positive F P v₀)
    (NativeThetaPowers.bound_positive m F P v₀ r) hε (by norm_num : (0 : ℝ) < 1)
    (NativeThetaPowers.degree m 0) (NativeThetaPowers.degree m r)
    (NativeThetaPowers.degree m (r + 1)) hd x (NativeThetaLengthCut.input m (by omega) F P v₀)
    y (NativeThetaPowers.filteredPower m hm F P v₀ r) hx hy

theorem level_succ_upper (r : ℕ) :
    level m hm F P v₀ (r + 1) ≤ level m hm F P v₀ 0 + level m hm F P v₀ r := by
  by_contra h
  let ε := (level m hm F P v₀ (r + 1) -
    (level m hm F P v₀ 0 + level m hm F P v₀ r)) / 6
  have hε : 0 < ε := by dsimp [ε]; linarith
  have ha := lift_above m hm F P v₀ 0 (by linarith :
    level m hm F P v₀ 0 < level m hm F P v₀ 0 + ε)
  have hb := lift_above m hm F P v₀ r (by linarith :
    level m hm F P v₀ r < level m hm F P v₀ r + ε)
  have hl := level_le_lift m hm F P v₀ (r + 1) (product_lift m hm F P v₀ r ha hb hε)
  dsimp [ε] at hl
  linarith

theorem primitive_gap_lower (r : ℕ) :
    level m hm F P v₀ 0 + (r : ℝ) * NativeGHSpectralSupport.level m F 0 ≤
      level m hm F P v₀ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h := level_succ_lower m hm F P v₀ r
    push_cast
    linarith

end
end Finsler.NativeThetaSpectralStep
