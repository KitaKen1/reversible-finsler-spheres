module

public import Finsler.Topology.CrossingSlopes
public import Finsler.Topology.RelativeKronecker
public import Finsler.Topology.RelativeDual
public import Finsler.Topology.CircleLabel
public import Finsler.Topology.GlobalCutData
public import Mathlib.Analysis.SpecificLimits.Basic

/-! Vanishing levels of loop space classes lie near finitely many slope lines, and exact rates.

With finitely many prime closed geodesic images, the ordinary cohomology of every single crossing
of the energy filtration lives near the lines s·c₀ of finitely many slopes s
(`CrossingSlopes.exists_single_support`). Let y be a class of the loop space and c > 0 a level
such that y restricts to zero on the energy sublevels below c and not on those above c. Inside an
isolated band around c the crossing pair has a nonzero class in the degree of y (Kronecker duality
and the dual homology sequence of the pair, `cross_ne_zero`), so the degree of y lies within a
uniform distance A of s·c for a slope s of the finite set (`slope_of_level`).

For a sequence of such levels L_r in the degrees (2r+1)d with average rate L_r/(r+1) → β > 0,
the slopes are eventually 2d/β and the levels have bounded deviation from the exact rate
(`exact_rate`): this is how finiteness of the prime closed geodesics turns an average rate into
an exact one. -/

@[expose] public section

open Filter Topology

namespace Finsler.LevelSlopes

open CategoryTheory SphereOddDegree Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelComparison Finsler.CriticalLevels
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! ### Exact rates from finitely many slopes -/

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

/-- **Exact rate from finitely many slopes.** If the levels L_r have average rate β > 0 and for
every r the degree (2r+1)d lies within A of s·L_r for a slope s of a finite set, then the levels
have bounded deviation from (r+1)β. -/
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

/-! ### Vanishing levels near the slope lines -/

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

/-- The inclusion of an energy sublevel into the loop space. -/
abbrev inclE {n : ℕ} (F : ReversibleMetric n) (a : ℝ) : TopCat.of (lev F a) ⟶ Loops n :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The finite set of slopes: zero and the slopes of the labels. -/
abbrev slopes {n : ℕ} (F : ReversibleMetric n) (hfin : (primeImages F).Finite) : Finset ℝ :=
  insert (0 : ℝ) ((CriticalCircles.labels F hfin).image (CrossingSlopes.slope F))

/-- An isolated band around a positive level with regular ends. -/
theorem exists_band {n : ℕ} (F : ReversibleMetric n) (hfin : (primeImages F).Finite) {c : ℝ}
    (hc : 0 < c) : ∃ a' b' : ℝ, 0 < a' ∧ a' < c ∧ c < b' ∧ a' ∉ crit F ∧ b' ∉ crit F ∧
      (crit F ∩ Icc a' b').Subsingleton ∧ ∀ c' ∈ crit F, a' ≤ c' → c' ≤ b' → c' = c := by
  obtain ⟨a₁, b₁, ha₁, ha₁c, hcb₁, hiso⟩ := CircleLabel.exists_isolated_level F hfin hc
  refine ⟨(a₁ + c) / 2, (c + b₁) / 2, by linarith, by linarith, by linarith, fun hcr => ?_,
    fun hcr => ?_, fun x hx z hz => ?_, fun c' hc' h1 h2 => hiso c' hc' (by linarith) (by linarith)⟩
  · have := hiso _ hcr (by linarith) (by linarith)
    linarith
  · have := hiso _ hcr (by linarith) (by linarith)
    linarith
  · rw [hiso x hx.1 (by linarith [hx.2.1]) (by linarith [hx.2.2]),
      hiso z hz.1 (by linarith [hz.2.1]) (by linarith [hz.2.2])]

/-- **The vanishing level of a class lies near a slope line.** With finitely many prime closed
geodesic images there is A such that for every class y of the loop space and every level c > 0
below which y vanishes on the energy sublevels and above which it does not, the degree of y lies
within A of s·c for a slope s of the finite set. -/
theorem slope_of_level {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, ∀ (q : ℕ) (y : cohomologyZMod2 (Loops n) q) (c : ℝ), 0 < c →
      (∀ a : ℝ, 0 < a → a < c → (cohPullback (inclE F a) q).hom y = 0) →
      (∀ b : ℝ, c < b → (cohPullback (inclE F b) q).hom y ≠ 0) →
      ∃ s ∈ slopes F hfin, |(q : ℝ) - s * c| ≤ A := by
  obtain ⟨A, hA⟩ := CrossingSlopes.exists_single_support F hn hfin
  refine ⟨A, fun q y c hc hbelow habove => ?_⟩
  obtain ⟨a', b', ha'0, h2, h3, hacrit, hbcrit, hsub, hiso⟩ := exists_band F hfin hc
  have hab' : a' ≤ b' := (h2.trans h3).le
  have hz : ∃ z : H (crossComplex F hab') q, z ≠ 0 := by
    refine cross_ne_zero F hab' ((cohPullback (inclE F b') q).hom y) (habove b' h3) ?_
    have hfac : (crossPair F hab').map ≫ inclE F b' = inclE F a' := rfl
    have hcomp := Finsler.Cup.pullback_comp (crossPair F hab').map (inclE F b') q y
    rw [hfac] at hcomp
    exact hcomp.symm.trans (hbelow a' ha'0 h2)
  obtain ⟨c₀, ⟨hc₀, hc₀a, hc₀b⟩, s, hs, hbound⟩ :=
    hA a' b' hab' ha'0 hacrit hbcrit hsub q hz
  exact ⟨s, hs, by rw [← hiso c₀ hc₀ hc₀a hc₀b]; exact hbound⟩

/-- **The vanishing level of a class of (Λ, M) lies near a slope line** (ordinary cohomology
relative to the constant loops, restricted to the sublevel pairs). -/
theorem slope_of_level_rel {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ A : ℕ, ∀ (q : ℕ) (x : H (fullComplex n) q) (c : ℝ), 0 < c →
      (∀ a : ℝ, 0 < a → a < c → Hmap (resHom F a) q x = 0) →
      (∀ b : ℝ, c < b → Hmap (resHom F b) q x ≠ 0) →
      ∃ s ∈ slopes F hfin, |(q : ℝ) - s * c| ≤ A := by
  obtain ⟨A, hA⟩ := CrossingSlopes.exists_single_support F hn hfin
  refine ⟨A, fun q x c hc hbelow habove => ?_⟩
  obtain ⟨a', b', ha'0, h2, h3, hacrit, hbcrit, hsub, hiso⟩ := exists_band F hfin hc
  have hab' : a' ≤ b' := (h2.trans h3).le
  have hz : ∃ z : H (crossComplex F hab') q, z ≠ 0 := by
    obtain ⟨z, hz⟩ := exact_crossing_ordinary F hab' q (Hmap (resHom F b') q x)
      (by rw [GlobalCutData.cut_res]; exact hbelow a' ha'0 h2)
    refine ⟨z, fun h0 => habove b' h3 ?_⟩
    rw [← hz, h0, LinearMap.map_zero]
  obtain ⟨c₀, ⟨hc₀, hc₀a, hc₀b⟩, s, hs, hbound⟩ :=
    hA a' b' hab' ha'0 hacrit hbcrit hsub q hz
  exact ⟨s, hs, by rw [← hiso c₀ hc₀ hc₀a hc₀b]; exact hbound⟩

/-- **Exact rate of a tower of classes** with finitely many prime closed geodesic images: if the
classes y_r of degrees (2r+1)d have vanishing levels L_r (in the sense of `slope_of_level`) with
average rate β > 0, the levels have bounded deviation from (r+1)β. -/
theorem tower_exact_rate {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) {d : ℕ} (hd : 0 < d) (y : ∀ r : ℕ,
      cohomologyZMod2 (Loops n) ((2 * r + 1) * d)) {L : ℕ → ℝ} (hL0 : ∀ r, 0 < L r)
    (hbelow : ∀ r (a : ℝ), 0 < a → a < L r →
      (cohPullback (inclE F a) ((2 * r + 1) * d)).hom (y r) = 0)
    (habove : ∀ r (b : ℝ), L r < b → (cohPullback (inclE F b) ((2 * r + 1) * d)).hom (y r) ≠ 0)
    {β : ℝ} (hβ : 0 < β) (hrate : Tendsto (fun r : ℕ => L r / ((r : ℝ) + 1)) atTop (𝓝 β)) :
    ∃ C : ℝ, ∀ r : ℕ, ((r : ℝ) + 1) * β - C ≤ L r ∧ L r ≤ ((r : ℝ) + 1) * β + C := by
  obtain ⟨A, hA⟩ := slope_of_level F hn hfin
  refine exact_rate (S := slopes F hfin) (A := (A : ℝ)) hβ (by exact_mod_cast hd : (0 : ℝ) < d)
    hrate (fun r => ?_)
  obtain ⟨s, hs, hb⟩ := hA _ (y r) (L r) (hL0 r) (hbelow r) (habove r)
  refine ⟨s, hs, ?_⟩
  push_cast at hb
  exact hb

end

end Finsler.LevelSlopes
