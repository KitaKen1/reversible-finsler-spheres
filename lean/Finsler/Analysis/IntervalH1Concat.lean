module

public import Finsler.Analysis.IntervalH1AffineRestrict

/-! Concatenation of actual weak H¹ graph elements. For 0 < a < 1 the first element is run on
[0,a] at speed 1/a and the second on [a,1] at speed 1/(1 − a). The value is defined as the
initial point plus the primitive of the piecewise velocity, so continuity is automatic; when the
end of the first element equals the start of the second, the representative is the expected
piecewise reparametrization. Restricting the concatenation to [0,a] and [a,1] recovers the two
pieces, so for sphere paths the energy is E₁/a + E₂/(1 − a). -/

@[expose] public section

namespace Finsler.SobolevConcat

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevOfPrimitive Finsler.SobolevSpherePath Finsler.SobolevAffine
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-- The affine map from [a,1] onto [0,1]. -/
def rightMap (a τ : ℝ) : ℝ := -((1 - a)⁻¹ * a) + (1 - a)⁻¹ * τ

/-- The velocity of the first piece, run on [0,a]. -/
def leftVel (u : Space n) (a τ : ℝ) : Ambient n := a⁻¹ • velocity u (a⁻¹ * τ)

/-- The velocity of the second piece, run on [a,1]. -/
def rightVel (w : Space n) (a τ : ℝ) : Ambient n := (1 - a)⁻¹ • velocity w (rightMap a τ)

/-- The piecewise velocity of the concatenation. -/
def concatVel (u w : Space n) (a τ : ℝ) : Ambient n :=
  (Iic a).indicator (leftVel u a) τ + (Ioi a).indicator (rightVel w a) τ

theorem concatVel_of_le (u w : Space n) {a τ : ℝ} (h : τ ≤ a) :
    concatVel u w a τ = leftVel u a τ := by
  have h1 : τ ∈ Iic a := h
  have h2 : τ ∉ Ioi a := not_lt.mpr h
  simp only [concatVel, indicator_of_mem h1, indicator_of_notMem h2, add_zero]

theorem concatVel_of_lt (u w : Space n) {a τ : ℝ} (h : a < τ) :
    concatVel u w a τ = rightVel w a τ := by
  have h1 : τ ∉ Iic a := not_le.mpr h
  have h2 : τ ∈ Ioi a := h
  simp only [concatVel, indicator_of_mem h2, indicator_of_notMem h1, zero_add]

theorem rightMap_left (a : ℝ) : rightMap a a = 0 := by
  unfold rightMap
  ring

theorem rightMap_one {a : ℝ} (ha1 : a < 1) : rightMap a 1 = 1 := by
  have h : (1 - a) ≠ 0 := by linarith
  unfold rightMap
  field_simp
  ring

theorem split_mem {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : a ∈ Icc (0 : ℝ) 1 := ⟨ha0.le, ha1.le⟩

section Bounds

variable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
include ha0 ha1

omit ha1 in
theorem leftVel_memLp (u : Space n) : MemLp (leftVel u a) 2 (volume.restrict (Ioo 0 a)) := by
  have h := memLp_comp_affine (n := n) (f := fun τ => a⁻¹ * τ) (c := a⁻¹) (d := 0)
    (a := 0) (b := a) (inv_pos.mpr ha0) (fun x => (zero_add _).symm) (by ring)
    (by rw [zero_add, inv_mul_cancel₀ ha0.ne']) (velocity u)
  exact h.const_smul a⁻¹

omit ha0 in
theorem rightVel_memLp (w : Space n) : MemLp (rightVel w a) 2 (volume.restrict (Ioo a 1)) := by
  have hc : 0 < (1 - a)⁻¹ := inv_pos.mpr (by linarith)
  have h := memLp_comp_affine (n := n) (f := rightMap a) (c := (1 - a)⁻¹)
    (d := -((1 - a)⁻¹ * a)) (a := a) (b := 1) hc (fun _ => rfl) (rightMap_left a)
    (rightMap_one ha1) (velocity w)
  exact h.const_smul (1 - a)⁻¹

theorem concatVel_memLp (u w : Space n) : MemLp (concatVel u w a) 2 intervalMeasure := by
  have hL : MemLp ((Iic a).indicator (leftVel u a)) 2 intervalMeasure := by
    rw [memLp_indicator_iff_restrict measurableSet_Iic.nullMeasurableSet]
    change MemLp _ 2 ((volume.restrict (Ioo (0 : ℝ) 1)).restrict (Iic a))
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic a ∩ Ioo 0 1 = Ioc 0 a := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, by linarith⟩
    rw [hset, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact leftVel_memLp ha0 u
  have hR : MemLp ((Ioi a).indicator (rightVel w a)) 2 intervalMeasure := by
    rw [memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet]
    change MemLp _ 2 ((volume.restrict (Ioo (0 : ℝ) 1)).restrict (Ioi a))
    rw [Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi a ∩ Ioo 0 1 = Ioo a 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by linarith, h2⟩
    rw [hset]
    exact rightVel_memLp ha1 w
  exact hL.add hR

theorem concatVel_intervalIntegrable (u w : Space n) :
    IntervalIntegrable (concatVel u w a) volume 0 1 :=
  intervalIntegrable_of_memLp (concatVel_memLp ha0 ha1 u w)

end Bounds

/-- The value of the concatenation: initial point plus the primitive of the velocity. -/
def concatRep (u w : Space n) (a τ : ℝ) : Ambient n :=
  continuousRepresentative u 0 + ∫ σ in (0 : ℝ)..τ, concatVel u w a σ

section Construction

variable (u w : Space n) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)

include ha0 ha1 in
theorem concatRep_continuousOn : ContinuousOn (concatRep u w a) (Icc 0 1) :=
  continuousOn_const.add
    (Finsler.IntervalPrimitive.primitive_continuousOn (concatVel_intervalIntegrable ha0 ha1 u w))

theorem concatRep_eq_add_integral (τ : ℝ) :
    concatRep u w a τ = concatRep u w a 0 + ∫ σ in (0 : ℝ)..τ, concatVel u w a σ := by
  unfold concatRep
  rw [intervalIntegral.integral_same, add_zero]

/-- The concatenation of two graph elements with split parameter a. -/
def concat : Space n :=
  ofPrimitive (concatRep_continuousOn u w ha0 ha1) (concatVel_memLp ha0 ha1 u w)
    (fun τ _ => concatRep_eq_add_integral u w τ)

theorem velocity_concat_ae :
    velocity (concat u w ha0 ha1) =ᵐ[intervalMeasure] concatVel u w a :=
  velocity_ofPrimitive_ae _ _ _

include ha0 in
theorem integral_concatVel_left {τ : ℝ} (hτ : τ ∈ Icc 0 a) :
    ∫ σ in (0 : ℝ)..τ, concatVel u w a σ =
      continuousRepresentative u (a⁻¹ * τ) - continuousRepresentative u 0 := by
  have heq : EqOn (concatVel u w a) (leftVel u a) (uIcc 0 τ) := by
    intro σ hσ
    rw [uIcc_of_le hτ.1] at hσ
    exact concatVel_of_le u w (hσ.2.trans hτ.2)
  rw [intervalIntegral.integral_congr heq]
  have hcv : ∫ σ in (0 : ℝ)..τ, leftVel u a σ = ∫ x in a⁻¹ * 0..a⁻¹ * τ, velocity u x := by
    simp only [leftVel]
    rw [intervalIntegral.integral_smul]
    exact intervalIntegral.smul_integral_comp_mul_left (fun x => velocity u x) a⁻¹
  have hmem : a⁻¹ * τ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (inv_nonneg.mpr ha0.le) hτ.1
    · calc a⁻¹ * τ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left hτ.2 (inv_nonneg.mpr ha0.le)
        _ = 1 := inv_mul_cancel₀ ha0.ne'
  rw [hcv, mul_zero]
  exact (continuousRepresentative_sub u (left_mem_Icc.mpr zero_le_one) hmem).symm

include ha0 ha1 in
theorem representative_concat_left {τ : ℝ} (hτ : τ ∈ Icc 0 a) :
    continuousRepresentative (concat u w ha0 ha1) τ = continuousRepresentative u (a⁻¹ * τ) := by
  have hτ1 : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ha1.le⟩
  rw [concat, representative_ofPrimitive _ _ _ hτ1, concatRep,
    integral_concatVel_left u w ha0 hτ]
  abel

include ha0 ha1 in
theorem representative_concat_right
    (hmatch : continuousRepresentative u 1 = continuousRepresentative w 0) {τ : ℝ}
    (hτ : τ ∈ Icc a 1) :
    continuousRepresentative (concat u w ha0 ha1) τ = continuousRepresentative w (rightMap a τ) := by
  have hτ1 : τ ∈ Icc (0 : ℝ) 1 := ⟨ha0.le.trans hτ.1, hτ.2⟩
  have hint := concatVel_intervalIntegrable ha0 ha1 u w
  have h0a : IntervalIntegrable (concatVel u w a) volume 0 a := by
    apply hint.mono_set
    rw [uIcc_of_le ha0.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ha1.le
  have haτ : IntervalIntegrable (concatVel u w a) volume a τ := by
    apply hint.mono_set
    rw [uIcc_of_le hτ.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha0.le hτ.2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0a haτ
  have hleft := integral_concatVel_left u w ha0 (right_mem_Icc.mpr ha0.le)
  rw [inv_mul_cancel₀ ha0.ne'] at hleft
  have hcongr : ∫ σ in a..τ, concatVel u w a σ = ∫ σ in a..τ, rightVel w a σ := by
    apply intervalIntegral.integral_congr_ae
    refine Eventually.of_forall fun σ hσ => ?_
    rw [uIoc_of_le hτ.1] at hσ
    exact concatVel_of_lt u w hσ.1
  have hcv : ∫ σ in a..τ, rightVel w a σ =
      ∫ x in -((1 - a)⁻¹ * a) + (1 - a)⁻¹ * a..-((1 - a)⁻¹ * a) + (1 - a)⁻¹ * τ,
        velocity w x := by
    simp only [rightVel, rightMap]
    rw [intervalIntegral.integral_smul]
    exact intervalIntegral.smul_integral_comp_add_mul (fun x => velocity w x) (1 - a)⁻¹
      (-((1 - a)⁻¹ * a))
  have hlow : -((1 - a)⁻¹ * a) + (1 - a)⁻¹ * a = 0 := by ring
  have hτ' : rightMap a τ ∈ Icc (0 : ℝ) 1 := by
    have h1a : 0 < 1 - a := by linarith
    have hr : rightMap a τ = (τ - a) / (1 - a) := by
      unfold rightMap
      field_simp
      ring
    rw [hr]
    constructor
    · exact div_nonneg (by linarith [hτ.1]) h1a.le
    · rw [div_le_one h1a]
      linarith [hτ.2]
  have hright : ∫ σ in a..τ, rightVel w a σ =
      continuousRepresentative w (rightMap a τ) - continuousRepresentative w 0 := by
    rw [hcv, hlow]
    exact (continuousRepresentative_sub w (left_mem_Icc.mpr zero_le_one) hτ').symm
  rw [concat, representative_ofPrimitive _ _ _ hτ1, concatRep, ← hsplit, hleft, hcongr, hright,
    hmatch]
  abel

include ha0 ha1 in
theorem representative_concat_zero :
    continuousRepresentative (concat u w ha0 ha1) 0 = continuousRepresentative u 0 := by
  rw [representative_concat_left u w ha0 ha1 (left_mem_Icc.mpr ha0.le), mul_zero]

include ha0 ha1 in
theorem representative_concat_one
    (hmatch : continuousRepresentative u 1 = continuousRepresentative w 0) :
    continuousRepresentative (concat u w ha0 ha1) 1 = continuousRepresentative w 1 := by
  rw [representative_concat_right u w ha0 ha1 hmatch (right_mem_Icc.mpr ha1.le),
    rightMap_one ha1]

include ha0 ha1 in
theorem concat_mem (hu : u ∈ SpherePath n) (hw : w ∈ SpherePath n)
    (hmatch : continuousRepresentative u 1 = continuousRepresentative w 0) :
    concat u w ha0 ha1 ∈ SpherePath n := by
  intro τ hτ
  rcases le_total τ a with h | h
  · rw [representative_concat_left u w ha0 ha1 ⟨hτ.1, h⟩]
    apply hu
    constructor
    · exact mul_nonneg (inv_nonneg.mpr ha0.le) hτ.1
    · calc a⁻¹ * τ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha0.le)
        _ = 1 := inv_mul_cancel₀ ha0.ne'
  · rw [representative_concat_right u w ha0 ha1 hmatch ⟨h, hτ.2⟩]
    apply hw
    have h1a : 0 < 1 - a := by linarith
    have hr : rightMap a τ = (τ - a) / (1 - a) := by
      unfold rightMap
      field_simp
      ring
    rw [hr]
    constructor
    · exact div_nonneg (by linarith) h1a.le
    · rw [div_le_one h1a]
      linarith [hτ.2]

theorem zero_mem_unit : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one

theorem one_mem_unit : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one

include ha0 ha1 in
/-- Restricting the concatenation to [0,a] recovers the first piece. -/
theorem restrict_concat_left :
    restrict (concat u w ha0 ha1) zero_mem_unit (split_mem ha0 ha1) ha0.le = u := by
  apply eq_of_representative_eqOn
  intro τ hτ
  have hmem : aff 0 a τ ∈ Icc 0 a := by
    unfold aff
    constructor
    · nlinarith [hτ.1]
    · nlinarith [hτ.2]
  rw [representative_restrict _ _ _ _ hτ, representative_concat_left u w ha0 ha1 hmem]
  congr 1
  unfold aff
  field_simp
  ring

include ha0 ha1 in
/-- Restricting the concatenation to [a,1] recovers the second piece. -/
theorem restrict_concat_right
    (hmatch : continuousRepresentative u 1 = continuousRepresentative w 0) :
    restrict (concat u w ha0 ha1) (split_mem ha0 ha1) one_mem_unit ha1.le = w := by
  apply eq_of_representative_eqOn
  intro τ hτ
  have hmem : aff a 1 τ ∈ Icc a 1 := by
    unfold aff
    constructor
    · nlinarith [hτ.1]
    · nlinarith [hτ.2]
  rw [representative_restrict _ _ _ _ hτ, representative_concat_right u w ha0 ha1 hmatch hmem]
  congr 1
  have h1a : (1 - a) ≠ 0 := by linarith
  unfold aff rightMap
  field_simp
  ring

include ha0 ha1 in
/-- The energy of a concatenation of sphere paths. -/
theorem pathEnergy_concat (F : ReversibleMetric n) (hu : u ∈ SpherePath n)
    (hw : w ∈ SpherePath n)
    (hmatch : continuousRepresentative u 1 = continuousRepresentative w 0) :
    pathEnergy F (concat u w ha0 ha1) = pathEnergy F u / a + pathEnergy F w / (1 - a) := by
  set c := concat u w ha0 ha1 with hc
  have hcm : c ∈ SpherePath n := concat_mem u w ha0 ha1 hu hw hmatch
  have hint := density_intervalIntegrable F hcm
  have h0a : IntervalIntegrable
      (fun t => lagrangian F (continuousRepresentative c t, velocity c t)) volume 0 a := by
    apply hint.mono_set
    rw [uIcc_of_le ha0.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ha1.le
  have ha1' : IntervalIntegrable
      (fun t => lagrangian F (continuousRepresentative c t, velocity c t)) volume a 1 := by
    apply hint.mono_set
    rw [uIcc_of_le ha1.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha0.le le_rfl
  have hEu : pathEnergy F u =
      a * ∫ t in (0 : ℝ)..a, lagrangian F (continuousRepresentative c t, velocity c t) := by
    have h := pathEnergy_restrict F c zero_mem_unit (split_mem ha0 ha1) ha0.le
    rw [hc, restrict_concat_left u w ha0 ha1, sub_zero] at h
    exact h
  have hEw : pathEnergy F w =
      (1 - a) * ∫ t in a..1, lagrangian F (continuousRepresentative c t, velocity c t) := by
    have h := pathEnergy_restrict F c (split_mem ha0 ha1) one_mem_unit ha1.le
    rw [hc, restrict_concat_right u w ha0 ha1 hmatch] at h
    exact h
  have h1a : (1 - a) ≠ 0 := by linarith
  rw [pathEnergy_eq_intervalIntegral F c, ← intervalIntegral.integral_add_adjacent_intervals h0a ha1',
    hEu, hEw]
  field_simp

end Construction

end

end Finsler.SobolevConcat
