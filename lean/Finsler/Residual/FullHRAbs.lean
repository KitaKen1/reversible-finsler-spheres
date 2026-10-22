module

public import Finsler.Residual.ThetaRaise
public import Finsler.Residual.GHLower
public import Finsler.Residual.HRClasses
public import Finsler.Residual.GHSlope

/-! Resonance bands of every loop space class with finitely many prime closed geodesics
(Claude, full-HR prototype, absolute singular cohomology and length sublevels).

Fix a residue with a nonzero base class y of degree k (`HRClasses.base_classes`) and a homology
class Y pairing to one with y, carried at length b. In the degree q = (m + deg GH_r) + k
* the nonzero class is GH_r ⊛ y (`GHLower.power_mul_injective`, `HRClasses.coh_unique`), which
  vanishes below the GH level ℓ_r ≥ (r+1)β − C (`GHLower.power_mul_vanish`, `GHSlope.gh_exact_rate`);
* the loop product of a lift of Θ_r at length a > t_r with Y is a nonzero homology class carried
  at a + b + ε (`ThetaRaise.theta_raise_ne_zero`), so the class does not vanish above
  t_r + b, and t_r ≤ (r+2)β (`NativeThetaGHCommonRate.theta_level_upper`).
Hence every nonzero class of degree q ≥ 8m vanishes on the length sublevels below qβ/(2m) − C and
not on those above qβ/(2m) + D (`band`). -/

@[expose] public section

namespace Finsler.FullHRAbs

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.StrictLengthEnergyBridge

noncomputable section
set_option autoImplicit false

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1))
  (v₀ : equator P)

/-- Restriction of an absolute class to a length sublevel. -/
abbrev resL {q : ℕ} (L : ℝ) (x : cohomologyZMod2 (Loops (m + 1)) q) :
    cohomologyZMod2 (lengthSpace F L) q :=
  (cohPullback (LengthFilteredLoopRotation.full F L) q).hom x

include hm P v₀ in
/-- A class pairing to one with a carried homology class does not vanish there. -/
theorem res_ne_of_carried {q : ℕ} {L : ℝ} {x : cohomologyZMod2 (Loops (m + 1)) q}
    (hx : x ≠ 0) (hq : m ≤ q) (hres : q % m = 0 ∨ q % m = 1)
    (Z : homologyZMod2 (lengthSpace F L) q)
    (hZ : (homologyPushZMod2 (LengthFilteredLoopRotation.full F L) q).hom Z ≠ 0) :
    resL m F L x ≠ 0 := by
  intro h0
  have h1 := HRClasses.pair_one m hm P v₀ q hq hres hx hZ
  have hn := kroneckerMap_naturality_apply (LengthFilteredLoopRotation.full F L) q x
  have h2 := congrArg (fun φ => φ Z) hn
  simp only [LinearMap.comp_apply] at h2
  have h3 : (kroneckerMap (lengthSpace F L) q).hom (resL m F L x) Z = 0 := by
    rw [h0, map_zero, LinearMap.zero_apply]
  rw [h1] at h2
  exact zero_ne_one (h3.symm.trans h2)

include hm P v₀ in
/-- **The band of one residue.** -/
theorem residue_band (hfin : (Finsler.Geodesics.primeImages F).Finite) (k : ℕ) (hk : 1 ≤ k)
    (hres : k % m = 0 ∨ k % m = 1) {y : cohomologyZMod2 (Loops (m + 1)) k} (hy : y ≠ 0) :
    ∃ C D : ℝ, ∀ (r : ℕ) (x : cohomologyZMod2 (Loops (m + 1)) ((m + NativeGHPowers.degree m r) + k)),
      x ≠ 0 →
      (∀ R : ℝ, R < ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C → resL m F R x = 0) ∧
      (∀ L : ℝ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + D < L → resL m F L x ≠ 0) := by
  obtain ⟨C, hC⟩ := GHSlope.gh_exact_rate m hm F P v₀ hfin
  obtain ⟨Y, hY⟩ := HRClasses.exists_dual (Loops (m + 1)) k hy
  obtain ⟨b, hb, Yb, hYb⟩ := NativePrimitiveCutSurjective.exists_positive_length_lift F k Y
  have hY0 : Y ≠ 0 := fun h => by rw [h, map_zero] at hY; exact zero_ne_one hY
  have hYb0 : (homologyPushZMod2 (LengthFilteredLoopRotation.full F b) k).hom Yb ≠ 0 := by
    rw [hYb]; exact hY0
  refine ⟨C, NativeGHOptimalRate.rate m F + b, fun r x hx => ⟨fun R hR => ?_, fun L hL => ?_⟩⟩
  · -- the class is GH_r ⊛ y, which vanishes below the GH level
    have hprod : CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m r) k
        (NativeGHPowers.power m r) y ≠ 0 := by
      intro h0
      apply hy
      apply GHLower.power_mul_injective m hm F P v₀ r k hk
      show CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m r) k (NativeGHPowers.power m r) y =
        CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m r) k (NativeGHPowers.power m r) 0
      rw [h0, ← CanonicalTimeCupBilinear.bilinear_apply, map_zero]
    have hxe : x = CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m r) k
        (NativeGHPowers.power m r) y := HRClasses.coh_unique m hm P v₀ _ (by omega) hx hprod
    rw [hxe]
    exact GHLower.power_mul_vanish m hm F r k y (by linarith [(hC r).1])
  · -- a near-optimal Theta lift times the carried dual class
    have ht := NativeThetaGHCommonRate.theta_level_upper m hm F P v₀ r
    set t := NativeThetaSpectralLength.level m hm F P v₀ r with htdef
    have hδ : 0 < (L - b - t) / 3 := by
      have : (r : ℝ) + 1 = ((r : ℝ) + 1) := rfl
      linarith
    set δ := (L - b - t) / 3 with hδdef
    have ha : t < t + δ := by linarith
    obtain ⟨Z, hZ, -⟩ := ThetaRaise.theta_raise_ne_zero m hm F P v₀ r ha b hb hδ k Yb hYb0
    have hres' : ((m + NativeGHPowers.degree m r) + k) % m = 0 ∨
        ((m + NativeGHPowers.degree m r) + k) % m = 1 := by
      have he : m + NativeGHPowers.degree m r + k = k + (2 * r + 2) * m := by
        rw [NativeGHPowers.degree_formula]; ring
      rw [he, Nat.add_mul_mod_self_right]
      exact hres
    have hne := res_ne_of_carried m hm F P v₀ hx (by omega) hres' Z hZ
    intro h0
    apply hne
    exact CanonicalGHLengthSupport.restriction_zero_mono F _ x (by linarith) h0

theorem band_of_eq {k : ℕ} {C' D' : ℝ}
    (hband : ∀ (r : ℕ) (x : cohomologyZMod2 (Loops (m + 1)) ((m + NativeGHPowers.degree m r) + k)),
      x ≠ 0 →
      (∀ R : ℝ, R < ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C' → resL m F R x = 0) ∧
      (∀ L : ℝ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + D' < L → resL m F L x ≠ 0))
    (q r : ℕ) (hq : q = (m + NativeGHPowers.degree m r) + k)
    (x : cohomologyZMod2 (Loops (m + 1)) q) (hx : x ≠ 0) :
    (∀ R : ℝ, R < ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C' → resL m F R x = 0) ∧
      (∀ L : ℝ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + D' < L → resL m F L x ≠ 0) := by
  subst hq
  exact hband r x hx

theorem mod_one (c : ℕ) (hm2 : 2 ≤ m) : (c * m + 1) % m = 1 := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

include hm P v₀ in
/-- **Resonance band of every nonzero class** of degree q ≥ 8m, in length sublevels. -/
theorem band (hfin : (Finsler.Geodesics.primeImages F).Finite) :
    ∃ C D : ℝ, ∀ q : ℕ, 8 * m ≤ q → ∀ x : cohomologyZMod2 (Loops (m + 1)) q, x ≠ 0 →
      (∀ R : ℝ, R < (q : ℝ) * NativeGHOptimalRate.rate m F / (2 * m) - C → resL m F R x = 0) ∧
      (∀ L : ℝ, (q : ℝ) * NativeGHOptimalRate.rate m F / (2 * m) + D < L → resL m F L x ≠ 0) := by
  obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, ⟨y₃, hy₃⟩, ⟨y₄, hy₄⟩⟩ := HRClasses.base_classes m hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hβ := NativeGHOptimalRate.rate_positive m hm F P v₀
  set β := NativeGHOptimalRate.rate m F with hβdef
  obtain ⟨C₁, D₁, h₁⟩ := residue_band m hm F P v₀ hfin (3 * m) (by omega)
    (Or.inl (Nat.mul_mod_left 3 m)) hy₁
  obtain ⟨C₂, D₂, h₂⟩ := residue_band m hm F P v₀ hfin (4 * m) (by omega)
    (Or.inl (Nat.mul_mod_left 4 m)) hy₂
  obtain ⟨C₃, D₃, h₃⟩ := residue_band m hm F P v₀ hfin (4 * m + 1) (by omega)
    (Or.inr (mod_one m 4 hm)) hy₃
  obtain ⟨C₄, D₄, h₄⟩ := residue_band m hm F P v₀ hfin (5 * m + 1) (by omega)
    (Or.inr (mod_one m 5 hm)) hy₄
  set Cm := max (max C₁ C₂) (max C₃ C₄) with hCm
  set Dm := max (max D₁ D₂) (max D₃ D₄) with hDm
  refine ⟨Cm + ((5 * m + 1 : ℕ) : ℝ) * β / (2 * m), Dm, fun q hq x hx => ?_⟩
  -- the band in terms of r for the base degree k
  have conv : ∀ (k r : ℕ) (C' D' : ℝ), k ≤ 5 * m + 1 → C' ≤ Cm → D' ≤ Dm →
      q = (m + NativeGHPowers.degree m r) + k →
      ((∀ R : ℝ, R < ((r : ℝ) + 1) * β - C' → resL m F R x = 0) ∧
        (∀ L : ℝ, ((r : ℝ) + 1) * β + D' < L → resL m F L x ≠ 0)) →
      (∀ R : ℝ, R < (q : ℝ) * β / (2 * m) - (Cm + ((5 * m + 1 : ℕ) : ℝ) * β / (2 * m)) →
          resL m F R x = 0) ∧
        (∀ L : ℝ, (q : ℝ) * β / (2 * m) + Dm < L → resL m F L x ≠ 0) := by
    intro k r C' D' hk hC hD hqe h
    have hqR : (q : ℝ) * β / (2 * m) = ((r : ℝ) + 1) * β + (k : ℝ) * β / (2 * m) := by
      rw [hqe, NativeGHPowers.degree_formula]
      push_cast
      field_simp
      ring
    have hk1 : (k : ℝ) * β / (2 * m) ≤ ((5 * m + 1 : ℕ) : ℝ) * β / (2 * m) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hβ.le
      exact_mod_cast hk
    have hk0 : 0 ≤ (k : ℝ) * β / (2 * m) := by positivity
    refine ⟨fun R hR => h.1 R ?_, fun L hL => h.2 L ?_⟩
    · rw [hqR] at hR; linarith
    · rw [hqR] at hL; linarith
  by_cases hres : q % m = 0 ∨ q % m = 1
  swap
  · exact absurd (HRClasses.coh_eq_zero_of_res m P v₀ q hm hres x) hx
  have hd := Nat.mod_add_div q m
  have hj8 : 8 ≤ q / m := (Nat.le_div_iff_mul_le (by omega)).mpr hq
  have hqj : q = q / m * m + q % m := by rw [Nat.mul_comm]; omega
  have hC1 : C₁ ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C₂ ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3 : C₃ ≤ Cm := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC4 : C₄ ≤ Cm := le_trans (le_max_right _ _) (le_max_right _ _)
  have hD1 : D₁ ≤ Dm := le_trans (le_max_left _ _) (le_max_left _ _)
  have hD2 : D₂ ≤ Dm := le_trans (le_max_right _ _) (le_max_left _ _)
  have hD3 : D₃ ≤ Dm := le_trans (le_max_left _ _) (le_max_right _ _)
  have hD4 : D₄ ≤ Dm := le_trans (le_max_right _ _) (le_max_right _ _)
  rcases hres with hs | hs <;> rcases Nat.even_or_odd (q / m) with ⟨t, ht⟩ | ⟨t, ht⟩
  · -- residue 0, even block index: base 4m
    have he : q = (m + NativeGHPowers.degree m (t - 3)) + 4 * m := by
      rw [NativeGHPowers.degree_formula, hqj, hs, ht]
      have : t - 3 + 3 = t := by omega
      nlinarith [this]
    exact conv _ _ _ _ (by omega) hC2 hD2 he (band_of_eq m F h₂ q _ he x hx)
  · -- residue 0, odd block index: base 3m
    have he : q = (m + NativeGHPowers.degree m (t - 2)) + 3 * m := by
      rw [NativeGHPowers.degree_formula, hqj, hs, ht]
      have : t - 2 + 2 = t := by omega
      nlinarith [this]
    exact conv _ _ _ _ (by omega) hC1 hD1 he (band_of_eq m F h₁ q _ he x hx)
  · -- residue 1, even block index: base 4m + 1
    have he : q = (m + NativeGHPowers.degree m (t - 3)) + (4 * m + 1) := by
      rw [NativeGHPowers.degree_formula, hqj, hs, ht]
      have : t - 3 + 3 = t := by omega
      nlinarith [this]
    exact conv _ _ _ _ (by omega) hC3 hD3 he (band_of_eq m F h₃ q _ he x hx)
  · -- residue 1, odd block index: base 5m + 1
    have he : q = (m + NativeGHPowers.degree m (t - 3)) + (5 * m + 1) := by
      rw [NativeGHPowers.degree_formula, hqj, hs, ht]
      have : t - 3 + 3 = t := by omega
      nlinarith [this]
    exact conv _ _ _ _ (by omega) hC4 hD4 he (band_of_eq m F h₄ q _ he x hx)

end

end Finsler.FullHRAbs
