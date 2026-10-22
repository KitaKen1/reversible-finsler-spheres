module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Order.Compact

/-! Substitution along the primitive of a nonnegative density. If φ is a primitive of an
integrable density ρ ≥ 0 on [a,b], the measure ρ dx on (a,b] is pushed forward by φ to
Lebesgue measure on (φ a, φ b]: both give the half lines the same mass by the definition of the
primitive. Hence ∫_a^b ρ(x) g(φ(x)) dx = ∫_{φ a}^{φ b} g, for Bochner and lower integrals.
For a primitive from 0 to 1 the largest point below a value is a monotone right inverse; it is a
left inverse ρ dx-almost everywhere, since the values of φ on its flat pieces are values at
rationals and so form a Lebesgue-null set. -/

@[expose] public section

namespace Finsler.MonotoneSubst

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-- The measure with density ρ on (a, b]. -/
def densityMeasure (ρ : ℝ → ℝ) (a b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc a b)).withDensity (fun x => ENNReal.ofReal (ρ x))

/-- φ is a primitive of the nonnegative integrable density ρ on [a, b]. -/
structure IsPrimitive (ρ φ : ℝ → ℝ) (a b : ℝ) : Prop where
  le : a ≤ b
  nonneg : ∀ x, 0 ≤ ρ x
  integrable : IntegrableOn ρ (Ioc a b)
  eq : ∀ x ∈ Icc a b, φ x = φ a + ∫ y in a..x, ρ y

section Substitution

variable {ρ φ : ℝ → ℝ} {a b : ℝ}

theorem primitive_intervalIntegrable (h : IsPrimitive ρ φ a b) {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) : IntervalIntegrable ρ volume x y := by
  constructor
  · exact h.integrable.mono_set (Ioc_subset_Ioc hx.1 hy.2)
  · exact h.integrable.mono_set (Ioc_subset_Ioc hy.1 hx.2)

theorem primitive_sub_eq (h : IsPrimitive ρ φ a b) {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) : φ y - φ x = ∫ t in x..y, ρ t := by
  have ha : a ∈ Icc a b := ⟨le_rfl, h.le⟩
  rw [h.eq y hy, h.eq x hx, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left ((primitive_intervalIntegrable h) ha hy)
      ((primitive_intervalIntegrable h) ha hx)]

theorem primitive_monotoneOn (h : IsPrimitive ρ φ a b) : MonotoneOn φ (Icc a b) := by
  intro x hx y hy hxy
  have h1 := (primitive_sub_eq h) hx hy
  have h2 : 0 ≤ ∫ t in x..y, ρ t := intervalIntegral.integral_nonneg hxy fun t _ => h.nonneg t
  linarith

theorem primitive_continuousOn (h : IsPrimitive ρ φ a b) : ContinuousOn φ (Icc a b) := by
  have hint : IntegrableOn ρ (uIcc a b) volume := by
    rw [uIcc_of_le h.le]
    exact (integrableOn_Icc_iff_integrableOn_Ioc).mpr h.integrable
  have hc := intervalIntegral.continuousOn_primitive_interval (μ := volume) hint
  rw [uIcc_of_le h.le] at hc
  exact (continuousOn_const.add hc).congr fun x hx => h.eq x hx

theorem primitive_mono (h : IsPrimitive ρ φ a b) {c : ℝ} (hc : c ∈ Icc a b) :
    IsPrimitive ρ φ a c where
  le := hc.1
  nonneg := h.nonneg
  integrable := h.integrable.mono_set (Ioc_subset_Ioc le_rfl hc.2)
  eq x hx := h.eq x ⟨hx.1, hx.2.trans hc.2⟩

theorem primitive_aemeasurable (h : IsPrimitive ρ φ a b) :
    AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (volume.restrict (Ioc a b)) :=
  h.integrable.aestronglyMeasurable.aemeasurable.ennreal_ofReal

theorem densityMeasure_Ioc (h : IsPrimitive ρ φ a b) {x : ℝ} (hx : x ∈ Icc a b) :
    densityMeasure ρ a b (Ioc a x) = ENNReal.ofReal (φ x - φ a) := by
  have hsub : Ioc a x ⊆ Ioc a b := Ioc_subset_Ioc le_rfl hx.2
  unfold densityMeasure
  rw [withDensity_apply _ measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hsub]
  have hint : IntegrableOn ρ (Ioc a x) volume := h.integrable.mono_set hsub
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a x)] ρ := Eventually.of_forall fun y => h.nonneg y
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hx.1,
    (primitive_sub_eq h) ⟨le_rfl, h.le⟩ hx]

theorem densityMeasure_eq_restrict :
    densityMeasure ρ a b =
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict (Ioc a b) := by
  unfold densityMeasure
  rw [restrict_withDensity measurableSet_Ioc]

theorem densityMeasure_inter (s : Set ℝ) :
    densityMeasure ρ a b s = densityMeasure ρ a b (s ∩ Ioc a b) := by
  rw [densityMeasure_eq_restrict, Measure.restrict_apply' measurableSet_Ioc,
    Measure.restrict_apply' measurableSet_Ioc, inter_assoc, inter_self]

/-- Below a value strictly between φ a and φ b, the preimage in (a, b] is an initial interval. -/
theorem preimage_Iic_eq (hab : a ≤ b) (hc : ContinuousOn φ (Icc a b))
    (hm : MonotoneOn φ (Icc a b)) {y : ℝ} (hya : φ a ≤ y) (hyb : y < φ b) :
    ∃ x ∈ Icc a b, φ x = y ∧ φ ⁻¹' Iic y ∩ Ioc a b = Ioc a x := by
  have hK : IsCompact (Icc a b ∩ φ ⁻¹' Iic y) :=
    isCompact_Icc.of_isClosed_subset (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
      inter_subset_left
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isGreatest ⟨a, ⟨le_rfl, hab⟩, hya⟩
  have hxI : x ∈ Icc a b := hxK.1
  have hxy : φ x ≤ y := hxK.2
  have hφx : φ x = y := by
    obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc hxI.2 (hc.mono (Icc_subset_Icc hxI.1 le_rfl))
      ⟨hxy, hyb.le⟩
    have hcK : c ∈ Icc a b ∩ φ ⁻¹' Iic y := ⟨⟨hxI.1.trans hc1.1, hc1.2⟩, by
      show φ c ≤ y
      rw [hc2]⟩
    have hcx : c ≤ x := hxmax hcK
    have : c = x := le_antisymm hcx hc1.1
    rw [← this, hc2]
  refine ⟨x, hxI, hφx, ?_⟩
  ext t
  constructor
  · rintro ⟨ht1, ht2⟩
    exact ⟨ht2.1, hxmax ⟨Ioc_subset_Icc_self ht2, ht1⟩⟩
  · rintro ⟨ht1, ht2⟩
    have htI : t ∈ Icc a b := ⟨ht1.le, ht2.trans hxI.2⟩
    refine ⟨?_, ht1, ht2.trans hxI.2⟩
    show φ t ≤ y
    rw [← hφx]
    exact hm htI hxI ht2

theorem densityMeasure_univ (h : IsPrimitive ρ φ a b) :
    densityMeasure ρ a b univ = ENNReal.ofReal (φ b - φ a) := by
  rw [densityMeasure_inter univ, univ_inter]
  exact densityMeasure_Ioc h ⟨h.le, le_rfl⟩

theorem aemeasurable_densityMeasure (h : IsPrimitive ρ φ a b) :
    AEMeasurable φ (densityMeasure ρ a b) :=
  (((primitive_continuousOn h).mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc).mono_ac
    (withDensity_absolutelyContinuous _ _)

/-- The density measure is pushed forward by φ to Lebesgue measure on (φ a, φ b]. -/
theorem map_densityMeasure (h : IsPrimitive ρ φ a b) :
    (densityMeasure ρ a b).map φ = volume.restrict (Ioc (φ a) (φ b)) := by
  have hab := h.le
  have hc := (primitive_continuousOn h)
  have hm := (primitive_monotoneOn h)
  have hae := aemeasurable_densityMeasure h
  have : IsFiniteMeasure (densityMeasure ρ a b) :=
    ⟨by rw [densityMeasure_univ h]; exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply_of_aemeasurable hae measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic,
    densityMeasure_inter]
  rcases lt_or_ge y (φ a) with hy | hy
  · have h1 : φ ⁻¹' Iic y ∩ Ioc a b = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false,
        not_and]
      intro ht hta htb
      have := hm ⟨le_rfl, hab⟩ ⟨hta.le, htb⟩ hta.le
      linarith
    have h2 : Iic y ∩ Ioc (φ a) (φ b) = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false, not_and]
      intro ht hta
      linarith
    rw [h1, h2, measure_empty, measure_empty]
  · rcases lt_or_ge y (φ b) with hyb | hyb
    · obtain ⟨x, hxI, hφx, hpre⟩ := preimage_Iic_eq hab hc hm hy hyb
      have h2 : Iic y ∩ Ioc (φ a) (φ b) = Ioc (φ a) y := by
        ext t
        simp only [mem_inter_iff, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨h1, h2, -⟩
          exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h2, h1, h2.trans hyb.le⟩
      rw [hpre, h2, densityMeasure_Ioc h hxI, hφx, Real.volume_Ioc]
    · have h1 : φ ⁻¹' Iic y ∩ Ioc a b = Ioc a b := by
        apply inter_eq_right.mpr
        intro t ht
        show φ t ≤ y
        exact (hm (Ioc_subset_Icc_self ht) ⟨hab, le_rfl⟩ ht.2).trans hyb
      have h2 : Iic y ∩ Ioc (φ a) (φ b) = Ioc (φ a) (φ b) :=
        inter_eq_right.mpr fun t ht => ht.2.trans hyb
      rw [h1, h2, densityMeasure_Ioc h ⟨hab, le_rfl⟩, Real.volume_Ioc]

/-- Substitution along the primitive of a nonnegative density. -/
theorem integral_comp_primitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (h : IsPrimitive ρ φ a b) {g : ℝ → E}
    (hg : IntegrableOn g (Ioc (φ a) (φ b))) :
    ∫ x in a..b, ρ x • g (φ x) = ∫ y in (φ a)..(φ b), g y := by
  have hab := h.le
  have hφab : φ a ≤ φ b := (primitive_monotoneOn h) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hae := aemeasurable_densityMeasure h
  have hmap := map_densityMeasure h
  have hgm : AEStronglyMeasurable g ((densityMeasure ρ a b).map φ) := by
    rw [hmap]
    exact hg.aestronglyMeasurable
  rw [intervalIntegral.integral_of_le hφab, ← hmap, integral_map hae hgm]
  unfold densityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀ (primitive_aemeasurable h)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), intervalIntegral.integral_of_le hab]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (h.nonneg x)]

/-- Substitution for lower integrals. -/
theorem lintegral_comp_primitive (h : IsPrimitive ρ φ a b) {G : ℝ → ℝ≥0∞}
    (hG : AEMeasurable G (volume.restrict (Ioc (φ a) (φ b)))) :
    ∫⁻ y in Ioc (φ a) (φ b), G y = ∫⁻ x in Ioc a b, ENNReal.ofReal (ρ x) * G (φ x) := by
  have hae := aemeasurable_densityMeasure h
  have hmap := map_densityMeasure h
  rw [← hmap] at hG ⊢
  rw [lintegral_map' hG hae]
  unfold densityMeasure
  exact lintegral_withDensity_eq_lintegral_mul₀' (primitive_aemeasurable h) (hG.comp_aemeasurable hae)

end Substitution

section Inverse

/-- The largest point of [0, 1] at which φ is at most t. -/
def rinv (φ : ℝ → ℝ) (t : ℝ) : ℝ := sSup {x | x ∈ Icc (0 : ℝ) 1 ∧ φ x ≤ t}

variable {φ : ℝ → ℝ}

theorem rinv_bddAbove (t : ℝ) : BddAbove {x | x ∈ Icc (0 : ℝ) 1 ∧ φ x ≤ t} :=
  ⟨1, fun _ hx => hx.1.2⟩

theorem rinv_mem (t : ℝ) : rinv φ t ∈ Icc (0 : ℝ) 1 := by
  by_cases hne : {x | x ∈ Icc (0 : ℝ) 1 ∧ φ x ≤ t}.Nonempty
  · obtain ⟨x, hx⟩ := hne
    exact ⟨hx.1.1.trans (le_csSup (rinv_bddAbove t) hx), csSup_le ⟨x, hx⟩ fun y hy => hy.1.2⟩
  · rw [not_nonempty_iff_eq_empty] at hne
    unfold rinv
    rw [hne, Real.sSup_empty]
    exact ⟨le_rfl, zero_le_one⟩

theorem rinv_monotone : Monotone (rinv φ) := by
  intro t t' htt'
  by_cases hne : {x | x ∈ Icc (0 : ℝ) 1 ∧ φ x ≤ t}.Nonempty
  · exact csSup_le_csSup (rinv_bddAbove t') hne fun x hx => ⟨hx.1, hx.2.trans htt'⟩
  · rw [not_nonempty_iff_eq_empty] at hne
    have h0 : rinv φ t = 0 := by
      unfold rinv
      rw [hne, Real.sSup_empty]
    rw [h0]
    exact (rinv_mem t').1

theorem rinv_measurable : Measurable (rinv φ) := rinv_monotone.measurable

theorem le_rinv {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : x ≤ rinv φ (φ x) :=
  le_csSup (rinv_bddAbove (φ x)) ⟨hx, le_rfl⟩

variable (hc : ContinuousOn φ (Icc 0 1)) (hm : MonotoneOn φ (Icc 0 1)) (h0 : φ 0 = 0)
  (h1 : φ 1 = 1)

include hc h0 in
theorem map_rinv_le {t : ℝ} (ht : 0 ≤ t) : φ (rinv φ t) ≤ t := by
  have hK : IsCompact {x | x ∈ Icc (0 : ℝ) 1 ∧ φ x ≤ t} :=
    isCompact_Icc.of_isClosed_subset (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic)
      fun _ hx => hx.1
  have hne : {x | x ∈ Icc (0 : ℝ) 1 ∧ φ x ≤ t}.Nonempty :=
    ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [h0]; exact ht⟩
  exact (hK.sSup_mem hne).2

include hc h0 h1 in
theorem map_rinv {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : φ (rinv φ t) = t := by
  have hr := rinv_mem (φ := φ) t
  have hle := map_rinv_le hc h0 ht.1
  by_contra hne
  have hlt : φ (rinv φ t) < t := lt_of_le_of_ne hle hne
  have hr1 : rinv φ t < 1 := by
    rcases lt_or_eq_of_le hr.2 with h | h
    · exact h
    · rw [h, h1] at hlt
      linarith [ht.2]
  obtain ⟨c, hcI, hct⟩ := intermediate_value_Icc hr1.le (hc.mono (Icc_subset_Icc hr.1 le_rfl))
    ⟨hlt.le, by rw [h1]; exact ht.2⟩
  have hcmem : c ∈ {x | x ∈ Icc (0 : ℝ) 1 ∧ φ x ≤ t} :=
    ⟨⟨hr.1.trans hcI.1, hcI.2⟩, hct.le⟩
  have hcle : c ≤ rinv φ t := le_csSup (rinv_bddAbove t) hcmem
  have hceq : c = rinv φ t := le_antisymm hcle hcI.1
  rw [← hceq, hct] at hlt
  exact lt_irrefl t hlt

include hm h0 h1 in
theorem map_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : φ x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← h0]
    exact hm ⟨le_rfl, zero_le_one⟩ hx hx.1
  · rw [← h1]
    exact hm hx ⟨zero_le_one, le_rfl⟩ hx.2

include hc hm h0 h1 in
/-- Off the values at rationals, the right inverse is a left inverse. -/
theorem rinv_map_eq_or_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    rinv φ (φ x) = x ∨ φ x ∈ φ '' range ((↑) : ℚ → ℝ) := by
  have hy := rinv_mem (φ := φ) (φ x)
  have hxy := le_rinv (φ := φ) hx
  rcases eq_or_lt_of_le hxy with h | h
  · exact Or.inl h.symm
  · right
    have hφy : φ (rinv φ (φ x)) = φ x := map_rinv hc h0 h1 (map_mem hm h0 h1 hx)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn h
    have hrI : (r : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans hr1.le, hr2.le.trans hy.2⟩
    have hlo : φ x ≤ φ r := hm hx hrI hr1.le
    have hhi : φ r ≤ φ (rinv φ (φ x)) := hm hrI hy hr2.le
    rw [hφy] at hhi
    exact ⟨r, mem_range_self r, le_antisymm hhi hlo⟩

variable {ρ : ℝ → ℝ}

/-- ρ dx-almost every point is not on a flat piece of φ. -/
theorem ae_rinv_map (h : IsPrimitive ρ φ 0 1) (h0 : φ 0 = 0) (h1 : φ 1 = 1) :
    ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), ρ x = 0 ∨ rinv φ (φ x) = x := by
  have hc := (primitive_continuousOn h)
  have hm := (primitive_monotoneOn h)
  set D : Set ℝ := φ '' range ((↑) : ℚ → ℝ) with hD
  have hDc : D.Countable := (countable_range _).image φ
  have hDm : MeasurableSet D := hDc.measurableSet
  have hnull : densityMeasure ρ 0 1 (φ ⁻¹' D) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable (aemeasurable_densityMeasure h) hDm,
      map_densityMeasure h]
    exact le_antisymm ((Measure.restrict_le_self (μ := volume) (s := Ioc (φ 0) (φ 1)) D).trans
      (hDc.measure_zero volume).le) (zero_le)
  have hlin : ∫⁻ x in φ ⁻¹' D, ENNReal.ofReal (ρ x) ∂(volume.restrict (Ioc (0 : ℝ) 1)) = 0 := by
    rw [← withDensity_apply' _ (φ ⁻¹' D)]
    exact hnull
  have hzero : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) 1)).restrict (φ ⁻¹' D)),
      ENNReal.ofReal (ρ x) = 0 :=
    (lintegral_eq_zero_iff' ((primitive_aemeasurable h).restrict)).mp hlin
  have himp := ae_imp_of_ae_restrict hzero
  have hmem : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)), x ∈ Ioc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [himp, hmem] with x hx hxI
  rcases rinv_map_eq_or_mem hc hm h0 h1 (Ioc_subset_Icc_self hxI) with hr | hr
  · exact Or.inr hr
  · left
    have h' := hx hr
    rw [ENNReal.ofReal_eq_zero] at h'
    exact le_antisymm h' (h.nonneg x)

/-- Substitution through the right inverse, on an initial interval. -/
theorem integral_comp_rinv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (h : IsPrimitive ρ φ 0 1) (h0 : φ 0 = 0) (h1 : φ 1 = 1) {H : ℝ → E}
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hH : IntegrableOn (fun y => H (rinv φ y)) (Ioc 0 t)) :
    ∫ y in (0 : ℝ)..t, H (rinv φ y) = ∫ x in (0 : ℝ)..(rinv φ t), ρ x • H x := by
  have hb := rinv_mem (φ := φ) t
  have hφb : φ (rinv φ t) = t := map_rinv (primitive_continuousOn h) h0 h1 ht
  have hsub := (primitive_mono h) hb
  have hH' : IntegrableOn (fun y => H (rinv φ y)) (Ioc (φ 0) (φ (rinv φ t))) := by
    rw [h0, hφb]
    exact hH
  have hsubst := integral_comp_primitive hsub hH'
  rw [h0, hφb] at hsubst
  rw [← hsubst]
  apply intervalIntegral.integral_congr_ae
  have hae := ae_rinv_map h h0 h1
  rw [ae_restrict_iff' measurableSet_Ioc] at hae
  filter_upwards [hae] with x hx hxI
  rw [uIoc_of_le hb.1] at hxI
  rcases hx ⟨hxI.1, hxI.2.trans hb.2⟩ with h' | h'
  · rw [h', zero_smul, zero_smul]
  · rw [h']

/-- Substitution through the right inverse for lower integrals on (0, 1]. -/
theorem lintegral_comp_rinv (h : IsPrimitive ρ φ 0 1) (h0 : φ 0 = 0) (h1 : φ 1 = 1)
    {H : ℝ → ℝ≥0∞} (hH : AEMeasurable (fun y => H (rinv φ y)) (volume.restrict (Ioc 0 1))) :
    ∫⁻ y in Ioc (0 : ℝ) 1, H (rinv φ y) = ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal (ρ x) * H x := by
  have hH' : AEMeasurable (fun y => H (rinv φ y)) (volume.restrict (Ioc (φ 0) (φ 1))) := by
    rw [h0, h1]
    exact hH
  have hsubst := lintegral_comp_primitive h hH'
  rw [h0, h1] at hsubst
  rw [hsubst]
  apply lintegral_congr_ae
  filter_upwards [ae_rinv_map h h0 h1] with x hx
  rcases hx with h' | h'
  · rw [h', ENNReal.ofReal_zero, zero_mul, zero_mul]
  · rw [h']

end Inverse

end

end Finsler.MonotoneSubst
