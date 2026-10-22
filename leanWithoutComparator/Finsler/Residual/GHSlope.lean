module

public import Finsler.Loop.NativeThetaGHRateDeficit
public import Finsler.Loop.NativeGHRateConvergence
public import Finsler.Loop.StrictLengthEnergyBridge
public import Finsler.Topology.CrossingSlopes
public import Finsler.Topology.RelativeKronecker
public import Finsler.Topology.RelativeDual
public import Finsler.Topology.CircleLabel
public import Mathlib.Analysis.SpecificLimits.Basic

/-! The exact rate of the GH tower with finitely many prime closed geodesics (Claude, HR
shortcut prototype).

With finitely many prime closed geodesic images every single crossing of the energy filtration
has its ordinary cohomology near finitely many lines of slopes s (`CrossingSlopes`). The level of
the r-th GH power (the supremum of the lengths below which it restricts to zero) lies inside an
isolated band around itself; below it the power vanishes on the energy sublevel, above it it
does not (arclength normalization), so the crossing of the band is nonzero in the degree
(2r+1)m of the power (Kronecker duality and the dual homology sequence of the pair). Hence each
level lies near a line of a slope from the finite set, and with the average rate of the levels
(`NativeGHRateConvergence.average_tendsto`) the slopes are eventually constant: the levels have
bounded deviation from the exact rate (`gh_exact_rate`), which is the exact-rate lower deficit. -/

open Filter Topology

@[expose] public section

namespace Finsler.SlopeRate

/-- A sequence with values in a finite set converging to σ is eventually σ. -/
theorem eventually_eq_of_tendsto_finset {S : Finset ℝ} {s : ℕ → ℝ} (hs : ∀ r, s r ∈ S)
    {σ : ℝ} (h : Tendsto s atTop (𝓝 σ)) : ∀ᶠ r in atTop, s r = σ := by
  classical
  set T := S.filter (fun t => t ≠ σ) with hT
  by_cases hTe : T.Nonempty
  · obtain ⟨t₀, ht₀, hmin⟩ := T.exists_min_image (fun t => |t - σ|) hTe
    have hpos : 0 < |t₀ - σ| := by
      have : t₀ ≠ σ := (Finset.mem_filter.mp ht₀).2
      exact abs_pos.mpr (sub_ne_zero.mpr this)
    have hev := (Metric.tendsto_nhds.mp h) _ hpos
    filter_upwards [hev] with r hr
    by_contra hne
    have hmem : s r ∈ T := Finset.mem_filter.mpr ⟨hs r, hne⟩
    have := hmin _ hmem
    rw [Real.dist_eq] at hr
    linarith
  · refine Eventually.of_forall fun r => ?_
    by_contra hne
    exact hTe ⟨s r, Finset.mem_filter.mpr ⟨hs r, hne⟩⟩

/-- **Exact rate from finitely many slopes.** -/
theorem exact_rate {S : Finset ℝ} {β d A : ℝ} (hβ : 0 < β) (hd : 0 < d) {L : ℕ → ℝ}
    (hL : Tendsto (fun r : ℕ => L r / ((r : ℝ) + 1)) atTop (𝓝 β))
    (hS : ∀ r : ℕ, ∃ s ∈ S, |(2 * (r : ℝ) + 1) * d - s * L r| ≤ A) :
    ∃ C : ℝ, ∀ r : ℕ, ((r : ℝ) + 1) * β - C ≤ L r ∧ L r ≤ ((r : ℝ) + 1) * β + C := by
  classical
  choose s hsS hsA using hS
  have hA : 0 ≤ A := (abs_nonneg _).trans (hsA 0)
  have hlow : ∀ᶠ r : ℕ in atTop, ((r : ℝ) + 1) * (β / 2) ≤ L r := by
    have hev := (Metric.tendsto_nhds.mp hL) (β / 2) (by positivity)
    filter_upwards [hev] with r hr
    rw [Real.dist_eq] at hr
    have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have h1 : β / 2 < L r / ((r : ℝ) + 1) := by
      have := (abs_lt.mp hr).1
      linarith
    rw [lt_div_iff₀ hr1] at h1
    linarith
  have hq : Tendsto (fun r : ℕ => (2 * (r : ℝ) + 1) * d / ((r : ℝ) + 1)) atTop (𝓝 (2 * d)) := by
    have h1 : Tendsto (fun r : ℕ => 1 / ((r : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun r : ℕ => 2 * d - d * (1 / ((r : ℝ) + 1))) atTop (𝓝 (2 * d - d * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul h1)
    rw [mul_zero, sub_zero] at h2
    refine h2.congr' (Eventually.of_forall fun r => ?_)
    have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hratio : Tendsto (fun r : ℕ => (2 * (r : ℝ) + 1) * d / L r) atTop (𝓝 (2 * d / β)) := by
    have h := hq.div hL hβ.ne'
    refine h.congr' ?_
    filter_upwards [hlow] with r hr
    have hr1 : (r : ℝ) + 1 ≠ 0 := by positivity
    have hLr : L r ≠ 0 := by
      have : 0 < ((r : ℝ) + 1) * (β / 2) := by positivity
      exact (this.trans_le hr).ne'
    simp only [Pi.div_apply]
    field_simp
  have hslope : Tendsto s atTop (𝓝 (2 * d / β)) := by
    have herr : Tendsto (fun r : ℕ => A / L r) atTop (𝓝 0) := by
      have hLtop : Tendsto L atTop atTop := by
        refine tendsto_atTop_mono' atTop hlow ?_
        exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const (by positivity)
      exact tendsto_const_nhds.div_atTop hLtop
    rw [Metric.tendsto_nhds] at hratio ⊢
    intro ε hε
    have h1 := hratio (ε / 2) (by positivity)
    have h2 := (Metric.tendsto_nhds.mp herr) (ε / 2) (by positivity)
    filter_upwards [h1, h2, hlow] with r hr1 hr2 hr3
    have hLpos : 0 < L r := lt_of_lt_of_le (by positivity) hr3
    rw [Real.dist_eq] at hr1 hr2 ⊢
    have hdiv : |(2 * (r : ℝ) + 1) * d / L r - s r| ≤ A / L r := by
      rw [show (2 * (r : ℝ) + 1) * d / L r - s r = ((2 * (r : ℝ) + 1) * d - s r * L r) / L r by
        field_simp, abs_div, abs_of_pos hLpos]
      exact div_le_div_of_nonneg_right (hsA r) hLpos.le
    rw [sub_zero, abs_of_nonneg (div_nonneg hA hLpos.le)] at hr2
    calc |s r - 2 * d / β| ≤ |s r - (2 * (r : ℝ) + 1) * d / L r| +
          |(2 * (r : ℝ) + 1) * d / L r - 2 * d / β| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := by
          rw [abs_sub_comm (s r)]
          exact add_lt_add_of_le_of_lt (hdiv.trans hr2.le) hr1
      _ = ε := by ring
  have hev := eventually_eq_of_tendsto_finset hsS hslope
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.mp hev
  have hlate : ∀ r, r₀ ≤ r → |L r - ((r : ℝ) + 1) * β| ≤ A * β / (2 * d) + β / 2 := by
    intro r hr
    have h := hsA r
    rw [hr₀ r hr] at h
    have key : L r - ((r : ℝ) + 1) * β =
        -(β / (2 * d)) * ((2 * (r : ℝ) + 1) * d - 2 * d / β * L r) - β / 2 := by
      field_simp
      ring
    rw [key]
    calc |-(β / (2 * d)) * ((2 * (r : ℝ) + 1) * d - 2 * d / β * L r) - β / 2|
        ≤ |-(β / (2 * d)) * ((2 * (r : ℝ) + 1) * d - 2 * d / β * L r)| + |β / 2| := abs_sub _ _
      _ = β / (2 * d) * |(2 * (r : ℝ) + 1) * d - 2 * d / β * L r| + β / 2 := by
          rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < β / (2 * d)),
            abs_of_pos (by positivity : 0 < β / 2)]
      _ ≤ β / (2 * d) * A + β / 2 := by
          gcongr
      _ = A * β / (2 * d) + β / 2 := by ring
  set C₁ : ℝ := ∑ r ∈ Finset.range r₀, |L r - ((r : ℝ) + 1) * β| with hC₁
  refine ⟨max (A * β / (2 * d) + β / 2) C₁, fun r => ?_⟩
  have hdev : |L r - ((r : ℝ) + 1) * β| ≤ max (A * β / (2 * d) + β / 2) C₁ := by
    rcases le_or_gt r₀ r with hr | hr
    · exact (hlate r hr).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      exact Finset.single_le_sum (f := fun r => |L r - ((r : ℝ) + 1) * β|)
        (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hr)
  constructor
  · linarith [neg_abs_le (L r - ((r : ℝ) + 1) * β)]
  · linarith [le_abs_self (L r - ((r : ℝ) + 1) * β)]

end Finsler.SlopeRate

namespace Finsler.GHSlope

open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.CriticalLevels Finsler.MeridianLoopFamily
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- **A class vanishing on the lower sublevel but not on the upper one gives a nonzero class of
the crossing pair** (Kronecker duality and the dual homology sequence of the pair). -/
theorem cross_ne_zero {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b) {q : ℕ}
    (yb : cohomologyZMod2 (crossPair F hab).fst q) (hyb : yb ≠ 0)
    (hya : (cohPullback (crossPair F hab).map q).hom yb = 0) :
    ∃ z : H (crossComplex F hab) q, z ≠ 0 := by
  have hφ : (kroneckerMap (crossPair F hab).fst q).hom yb ≠ 0 := by
    intro h
    apply hyb
    apply (kroneckerMap_bijective (crossPair F hab).fst q).1
    rw [h, LinearMap.map_zero]
  have hres : RelativeDual.restrict (ZMod 2) (crossPair F hab) q
      ((kroneckerMap (crossPair F hab).fst q).hom yb) = 0 := by
    have h := kroneckerMap_naturality_apply (crossPair F hab).map q yb
    rw [hya, LinearMap.map_zero] at h
    exact h.symm
  obtain ⟨ψ, hψ⟩ := RelativeDual.lift_of_restriction_zero (ZMod 2) (crossPair F hab) q _ hres
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    apply hφ
    rw [← hψ, LinearMap.map_zero]
  refine ⟨(ordinaryEquiv (crossPair F hab) (revCross F hab) (revCross_sq F hab) q).symm
    ((RelativeKronecker.equiv (crossPair F hab) q).symm ψ), fun h0 => hψ0 ?_⟩
  have h1 := congrArg (ordinaryEquiv (crossPair F hab) (revCross F hab) (revCross_sq F hab) q) h0
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at h1
  have h2 := congrArg (RelativeKronecker.equiv (crossPair F hab) q) h1
  rwa [LinearEquiv.apply_symm_apply, LinearEquiv.map_zero] at h2

/-- The finite set of slopes. -/
abbrev slopes {n : ℕ} (F : ReversibleMetric n) (hfin : (primeImages F).Finite) : Finset ℝ :=
  insert (0 : ℝ) ((CriticalCircles.labels F hfin).image (CrossingSlopes.slope F))

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1))
  (v₀ : equator P)

/-- The inclusion of an energy sublevel into the loop space. -/
abbrev inclE (a : ℝ) : TopCat.of (lev F a) ⟶ Loops (m + 1) :=
  SupportedCap.subspaceMap (Loops (m + 1)) (lev F a)

/-- The restriction of the r-th GH power to an energy sublevel. -/
abbrev resE (r : ℕ) (a : ℝ) : cohomologyZMod2 (TopCat.of (lev F a)) (NativeGHPowers.degree m r) :=
  (cohPullback (inclE m F a) (NativeGHPowers.degree m r)).hom (NativeGHPowers.power m r)

include hm in
/-- Below the level the power vanishes on the energy sublevel. -/
theorem vanish_below (r : ℕ) {a : ℝ} (ha : 0 < a)
    (hlt : a < NativeGHSpectralSupport.level m F r) : resE m F r a = 0 := by
  obtain ⟨R, hR, haR⟩ := exists_lt_of_lt_csSup (NativeGHSpectralSupport.supports_nonempty m hm F r) hlt
  -- the inclusion lev a → Λ factors through the length sublevel of R
  let ι : TopCat.of (lev F a) ⟶ TopCat.of (SelfCutOscillation.short F R) :=
    TopCat.ofHom ⟨fun u => ⟨u.1, lt_trans (StrictLengthEnergyBridge.toLength F a ha u).2 haR⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hfac : ι ≫ LengthFilteredLoopRotation.full F R = inclE m F a := rfl
  unfold resE
  rw [← hfac, Finsler.Cup.pullback_comp]
  change (cohPullback ι _).hom ((cohPullback (LengthFilteredLoopRotation.full F R) _).hom
    (NativeGHPowers.power m r)) = 0
  rw [show (cohPullback (LengthFilteredLoopRotation.full F R) (NativeGHPowers.degree m r)).hom
    (NativeGHPowers.power m r) = 0 from hR, map_zero]

include hm P v₀ in
/-- Above the level the power does not vanish on the energy sublevel. -/
theorem nonvanish_above (r : ℕ) {b : ℝ} (hb : 0 < b)
    (hlt : NativeGHSpectralSupport.level m F r < b) : resE m F r b ≠ 0 := by
  have hnot : b ∉ NativeGHSpectralSupport.supports m F r := fun hmem =>
    absurd (le_csSup (NativeGHSpectralSupport.supports_bddAbove m hm F P v₀ r) hmem) (not_le.mpr hlt)
  have hL : (cohPullback (LengthFilteredLoopRotation.full F b) (NativeGHPowers.degree m r)).hom
      (NativeGHPowers.power m r) ≠ 0 := hnot
  intro h0
  apply hL
  -- the inclusion of the energy sublevel is toLength followed by the length inclusion
  have hfac : StrictLengthEnergyBridge.toLength F b hb ≫ LengthFilteredLoopRotation.full F b =
      inclE m F b := rfl
  have h1 : (cohPullback (StrictLengthEnergyBridge.toLength F b hb) _).hom
      ((cohPullback (LengthFilteredLoopRotation.full F b) _).hom (NativeGHPowers.power m r)) = 0 := by
    rw [← Finsler.Cup.pullback_comp, hfac]
    exact h0
  -- toLength is injective on cohomology (homotopy inverse toEnergy)
  have hinv := Finsler.DiagonalCohomology.homotopy_pullback
    (StrictLengthEnergyBridge.shortHomotopy F b hb) (NativeGHPowers.degree m r)
    ((cohPullback (LengthFilteredLoopRotation.full F b) _).hom (NativeGHPowers.power m r))
  rw [Finsler.DiagonalCohomology.pullback_id, Finsler.Cup.pullback_comp, h1, map_zero] at hinv
  exact hinv

include hm P v₀ in
/-- **Every GH level lies near a line of a slope from the finite set.** -/
theorem level_slope (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, ∀ r : ℕ, ∃ s ∈ slopes F hfin,
      |(2 * (r : ℝ) + 1) * (m : ℝ) - s * NativeGHSpectralSupport.level m F r| ≤ A := by
  obtain ⟨A, hA⟩ := CrossingSlopes.exists_single_support F (by omega) hfin
  refine ⟨A, fun r => ?_⟩
  set c := NativeGHSpectralSupport.level m F r with hcdef
  have hc : 0 < c := NativeThetaGHRateDeficit.gh_level_positive m hm F P v₀ r
  obtain ⟨a₁, b₁, ha₁, ha₁c, hcb₁, hiso⟩ := CircleLabel.exists_isolated_level F hfin hc
  set a' := (a₁ + c) / 2 with ha'
  set b' := (c + b₁) / 2 with hb'
  have h1 : a₁ < a' := by rw [ha']; linarith
  have h2 : a' < c := by rw [ha']; linarith
  have h3 : c < b' := by rw [hb']; linarith
  have h4 : b' < b₁ := by rw [hb']; linarith
  have hab' : a' ≤ b' := (h2.trans h3).le
  have ha'0 : 0 < a' := ha₁.trans h1
  have hacrit : a' ∉ crit F := fun hcr => by
    have := hiso a' hcr h1.le (h2.trans (h3.trans h4)).le
    linarith
  have hbcrit : b' ∉ crit F := fun hcr => by
    have := hiso b' hcr (h1.trans (h2.trans h3)).le h4.le
    linarith
  have hsub : (crit F ∩ Icc a' b').Subsingleton := by
    intro x hx y hy
    rw [hiso x hx.1 (h1.le.trans hx.2.1) (hx.2.2.trans h4.le),
      hiso y hy.1 (h1.le.trans hy.2.1) (hy.2.2.trans h4.le)]
  -- the nonzero crossing class in the degree of the power
  have hz : ∃ z : H (crossComplex F hab') (NativeGHPowers.degree m r), z ≠ 0 := by
    refine cross_ne_zero F hab' (resE m F r b') (nonvanish_above m hm F P v₀ r (ha'0.trans_le hab') h3) ?_
    have hfac : (crossPair F hab').map ≫ inclE m F b' = inclE m F a' := rfl
    have hc := Finsler.Cup.pullback_comp (crossPair F hab').map (inclE m F b')
      (NativeGHPowers.degree m r) (NativeGHPowers.power m r)
    rw [hfac] at hc
    exact hc.symm.trans (vanish_below m hm F r ha'0 h2)
  obtain ⟨c₀, ⟨hc₀, hc₀a, hc₀b⟩, s, hs, hbound⟩ :=
    hA a' b' hab' ha'0 hacrit hbcrit hsub (NativeGHPowers.degree m r) hz
  have hc₀c : c₀ = c := hiso c₀ hc₀ (h1.le.trans hc₀a) (hc₀b.trans h4.le)
  refine ⟨s, hs, ?_⟩
  rw [hc₀c, NativeGHPowers.degree_formula] at hbound
  push_cast at hbound
  exact hbound

include hm P v₀ in
/-- **The exact rate of the GH tower** with finitely many prime closed geodesic images: the
levels have bounded deviation from (r+1)β. This discharges the exact-rate lower deficit. -/
theorem gh_exact_rate (hfin : (primeImages F).Finite) :
    ∃ C : ℝ, ∀ r : ℕ, ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F - C ≤
      NativeGHSpectralSupport.level m F r ∧
      NativeGHSpectralSupport.level m F r ≤ ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F + C := by
  obtain ⟨A, hA⟩ := level_slope m hm F P v₀ hfin
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  exact SlopeRate.exact_rate (NativeGHOptimalRate.rate_positive m hm F P v₀) hm0
    (NativeGHRateConvergence.average_tendsto m hm F P v₀) hA

include hm P v₀ in
/-- **Uniform deviation of both towers** (GH and Theta) from the common exact rate, with finitely
many prime closed geodesic images. -/
theorem common_uniform_deviation (hfin : (primeImages F).Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℕ,
      |NativeGHSpectralSupport.level m F r - ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F| ≤ D ∧
      |NativeThetaSpectralLength.level m hm F P v₀ r -
        ((r : ℝ) + 1) * NativeGHOptimalRate.rate m F| ≤ D := by
  obtain ⟨C, hC⟩ := gh_exact_rate m hm F P v₀ hfin
  have hC0 : 0 ≤ C := by linarith [(hC 0).1, (hC 0).2]
  refine ⟨max C (NativeGHOptimalRate.rate m F), hC0.trans (le_max_left _ _), fun r => ?_⟩
  have h := NativeThetaGHRateDeficit.common_deviation_of_critical_band m hm F P v₀
    (fun r => (hC r).1) r
  exact ⟨h.1.trans (le_max_left _ _), h.2⟩

end

end Finsler.GHSlope
