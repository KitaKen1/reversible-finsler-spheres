module

public import Finsler.Geometry.LevelField
public import Finsler.Analysis.StrictField
public import Finsler.Analysis.LevelGlue

/-! The global root field. On the polygons with N vertices, let K₀ be a compact set of the
regular set of the penalized energy with weight λ, K₁ ⊆ interior K₀ compact, and W_rest an open
set of polygons with nonzero vertices, such that the stationary sphere polygons
of a compact band lie in the interior of K₁ or in W_rest. Then for every κ > 0 there is a smooth
compactly supported field V₀ supported in the regular set, bounded by κ, along which the
penalized energy does not increase on the regular set and decreases strictly at every
non-critical polygon of the band outside W_rest. It is the gluing, with a cutoff equal to 1 near
K₁ and supported in the interior of K₀, of a field strict at every non-critical point of K₀
(a series of pseudo-gradients) and a band field strict outside K₁ ∪ W_rest, scaled to norm κ. -/

@[expose] public section

namespace Finsler.RootField

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PolygonDescent
open Finsler.PseudoGradient Finsler.SphereFlow Finsler.FlowLens Finsler.AmbientPenalty
open Finsler.AmbientDescent Finsler.LevelField Finsler.StrictField Finsler.GlueField
open Finsler.LevelGlue
open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-- A smooth compactly supported field can be scaled to any bound κ > 0. -/
theorem exists_scaled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : E → E}
    (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V) {κ : ℝ} (hκ : 0 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, ‖c • V x‖ ≤ κ := by
  obtain ⟨C, hC⟩ := hVc.exists_bound_of_continuous hV.continuous
  refine ⟨κ / (|C| + 1), by positivity, fun x => ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖V x‖ ≤ |C| + 1 := by linarith [hC x, le_abs_self C]
  calc κ / (|C| + 1) * ‖V x‖ ≤ κ / (|C| + 1) * (|C| + 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = κ := by field_simp

/-- **The global root field.** -/
theorem exists_root_field (F : ReversibleMetric n) (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ → ShortPolygon δ q)
    {K₀ K₁ : Set (ZMod N → Ambient n)} (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hK₁₀ : K₁ ⊆ interior K₀) (hK₀reg : K₀ ⊆ regSet F N lam)
    {Wrest : Set (Om n N)} (hWrest : IsOpen Wrest)
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ PolygonDescent.energy F N q →
      PolygonDescent.energy F N q ≤ b₀ → PolyCritical F N q →
        (incl q : Om n N).1 ∈ interior K₁ ∨ incl q ∈ Wrest)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n, ContDiff ℝ ∞ V₀ ∧ HasCompactSupport V₀ ∧
      tsupport V₀ ⊆ regSet F N lam ∧ (∀ z, ‖V₀ z‖ ≤ κ) ∧
      (∀ z ∈ regSet F N lam, fderiv ℝ (pen F N lam) z (V₀ z) ≤ 0) ∧
      ∀ Q : Om n N, a₀ ≤ penW F N lam Q → penW F N lam Q ≤ b₀ → Q ∉ Wrest →
        fderiv ℝ (pen F N lam) Q.1 ≠ 0 → fderiv ℝ (pen F N lam) Q.1 (V₀ Q.1) < 0 := by
  have hO := regSet_isOpen (N := N) F lam
  have hf : ContDiffOn ℝ 1 (pen F N lam) (regSet F N lam) := fun Q hQ => hQ.2.contDiffWithinAt
  -- the critical points in K₀ form a closed set
  set Γ : Set (ZMod N → Ambient n) := K₀ ∩ {z | fderiv ℝ (pen F N lam) z = 0} with hΓdef
  have hΓ : IsClosed Γ := by
    have hc : ContinuousOn (fderiv ℝ (pen F N lam)) (regSet F N lam) :=
      hf.continuousOn_fderiv_of_isOpen hO le_rfl
    exact (hc.mono hK₀reg).preimage_isClosed_of_isClosed hK₀.isClosed isClosed_singleton
  -- a field strict at every non-critical point of K₀
  obtain ⟨Vs, hVs, hVsc, hVst, hVsle, hVslt, hVsb⟩ := exists_strict_field hO hf hK₀ hK₀reg hΓ
    (fun x hx hxΓ h0 => hxΓ ⟨hx, h0⟩) hκ
  -- the cutoff
  obtain ⟨χ, W₁, hχ, hχ01, hχc, hχs, hW₁, hK₁W₁, hχ1⟩ :=
    exists_cutoff hK₁ isOpen_interior hK₁₀
  -- the band field, strict outside W₁ ∪ Wrest
  set 𝒲 : Set (Om n N) := {Q | Q.1 ∈ W₁} ∪ Wrest with h𝒲def
  have h𝒲 : IsOpen 𝒲 := (hW₁.preimage continuous_subtype_val).union hWrest
  have hcrit' : ∀ q : ZMod N → Sphere n, a₀ ≤ PolygonDescent.energy F N q →
      PolygonDescent.energy F N q ≤ b₀ → PolyCritical F N q → incl q ∈ 𝒲 := by
    intro q h1 h2 h3
    rcases hcrit q h1 h2 h3 with h | h
    · exact Or.inl (hK₁W₁ (interior_subset h))
    · exact Or.inr h
  obtain ⟨Vb, hVb, hVbc, hVbt, hVble, hVblt⟩ :=
    exists_band_field F hn hlam hδ hshort h𝒲 hcrit'
  obtain ⟨cb, hcb, hcbκ⟩ := exists_scaled hVb hVbc hκ
  set Vb' := fun z => cb • Vb z with hVb'def
  have hVb's : ContDiff ℝ ∞ Vb' := hVb.const_smul cb
  have hVb'le : ∀ z ∈ regSet F N lam, fderiv ℝ (pen F N lam) z (Vb' z) ≤ 0 := by
    intro z hz
    change fderiv ℝ (pen F N lam) z (cb • Vb z) ≤ 0
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hcb.le (hVble z hz)
  -- the glued field
  have hχsK : tsupport χ ⊆ K₀ := hχs.trans interior_subset
  refine ⟨glue (interior K₀) χ Vs Vb', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact glue_contDiff isOpen_interior hχ hχs hVs.contDiffOn hVb's
  · have h1 : HasCompactSupport (cutField (interior K₀) χ Vs) :=
      hχc.mono' fun y hy => by
        by_contra h
        exact hy (cutField_of_not_mem_tsupport h)
    have h2 : HasCompactSupport (fun y => (1 - χ y) • Vb' y) := by
      have h3 : HasCompactSupport Vb' := hVbc.smul_left (f := fun _ => cb)
      exact h3.smul_left (f := fun y => 1 - χ y)
    exact h1.add h2
  · -- the support lies in K₀ ∪ tsupport Vb ⊆ regSet
    have hsupp : Function.support (glue (interior K₀) χ Vs Vb') ⊆ K₀ ∪ tsupport Vb := by
      intro y hy
      by_cases hyt : y ∈ tsupport χ
      · exact Or.inl (hχsK hyt)
      · right
        rw [Function.mem_support, glue_of_not_mem_tsupport hyt] at hy
        by_contra hyb
        apply hy
        change cb • Vb y = 0
        rw [image_eq_zero_of_notMem_tsupport hyb, smul_zero]
    have hcl : IsClosed (K₀ ∪ tsupport Vb) := hK₀.isClosed.union (isClosed_tsupport Vb)
    exact (closure_minimal hsupp hcl).trans (union_subset hK₀reg hVbt)
  · intro z
    by_cases hz : z ∈ interior K₀
    · unfold glue
      rw [cutField_of_mem hz]
      obtain ⟨h0, h1⟩ := hχ01 z
      calc ‖χ z • Vs z + (1 - χ z) • Vb' z‖ ≤ ‖χ z • Vs z‖ + ‖(1 - χ z) • Vb' z‖ :=
            norm_add_le _ _
        _ = χ z * ‖Vs z‖ + (1 - χ z) * ‖Vb' z‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg h0,
              Real.norm_of_nonneg (sub_nonneg.mpr h1)]
        _ ≤ χ z * κ + (1 - χ z) * κ :=
            add_le_add (mul_le_mul_of_nonneg_left (hVsb z) h0)
              (mul_le_mul_of_nonneg_left (hcbκ z) (sub_nonneg.mpr h1))
        _ = κ := by ring
    · have hzt : z ∉ tsupport χ := fun h => hz (hχs h)
      rw [glue_of_not_mem_tsupport hzt]
      exact hcbκ z
  · intro z hz
    exact (fderiv_glue_le (fun y => (hχ01 y).1) (fun y => (hχ01 y).2) hχs (pen F N lam)
      (fun y hy => hVsle y (hK₀reg (hχsK hy))) hVb'le hz).1
  · intro Q ha hb hQW hne
    have hQreg : Q.1 ∈ regSet F N lam := by
      refine ⟨Q.2, ?_⟩
      have hle : PolygonDescent.energy F N (normalizeP Q) ≤ b₀ :=
        (energy_le_penW F hlam.le Q).trans hb
      exact pen_contDiffAt_one F lam Q (polyEnergyN_contDiffAt F Q
        (polyEnergyN_contDiffAt_one F hδ (hshort _ hle)))
    have hglue := fderiv_glue_le (fun y => (hχ01 y).1) (fun y => (hχ01 y).2) hχs (pen F N lam)
      (fun y hy => hVsle y (hK₀reg (hχsK hy))) hVb'le hQreg
    apply hglue.2
    by_cases hpos : 0 < χ Q.1
    · -- the strict field decreases strictly at the non-critical point Q of K₀
      have hQt : Q.1 ∈ tsupport χ :=
        subset_tsupport χ (by rw [Function.mem_support]; exact hpos.ne')
      have hQK : Q.1 ∈ K₀ := hχsK hQt
      right
      exact ⟨hVslt Q.1 hQK fun h => hne h.2, hpos, hχs hQt⟩
    · -- the band field decreases strictly at Q
      have hχ0 : χ Q.1 = 0 := le_antisymm (not_lt.mp hpos) (hχ01 Q.1).1
      left
      refine ⟨?_, by rw [hχ0]; exact one_pos⟩
      change fderiv ℝ (pen F N lam) Q.1 (cb • Vb Q.1) < 0
      rw [map_smul, smul_eq_mul]
      refine mul_neg_of_pos_of_neg hcb (hVblt Q ha hb ?_)
      rintro (hQ1 | hQ2)
      · have := hχ1 Q.1 hQ1
        rw [hχ0] at this
        exact zero_ne_one this
      · exact hQW hQ2

end

end Finsler.RootField
