module

public import Finsler.Topology.Birkhoff

/-! Small sublevels. For small b > 0 the loops of energy below b² move less than the segment
scale during the whole period, so the sublevel has a polygon model with a single vertex. The
broken geodesic of a polygon with one vertex has energy zero, hence is a constant loop, so the
straightening homotopy of this model is a level deformation of t_b into the constant loops. For
a ≤ 0 the set t_a consists of the constant loops, and the relative cochains of a pair of equal
sets vanish, so the reflection Borel cohomology of (t_a, M) is zero. Consequently the
reflection Borel cohomology of (t_b, M) is zero for all small b > 0. -/

@[expose] public section

namespace Finsler.SmallLevel

open CategoryTheory Set Topology SphereOddDegree
open Finsler.BorelLoop Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.PolygonModel Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonBasics Finsler.PolygonLoop Finsler.RegularInterval Finsler.BorelCochain
open Finsler.BorelPair Finsler.SphereDistance

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- For small b the sublevel t_b has a polygon model with a single vertex. -/
theorem exists_one_vertex_model (F : ReversibleMetric n) :
    ∃ b : ℝ, 0 < b ∧ Nonempty (PolygonModelData F b 1) := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨c, hc, hv⟩ := exists_velocity_sq_le F
  refine ⟨S.δ * Real.sqrt c, mul_pos S.pos (Real.sqrt_pos.mpr hc),
    ⟨PolygonModelData.mk S fun u hu s t hs ht _ => ?_⟩⟩
  have h1 := representative_sub_le_sqrt (u.data : Space n) hs ht
  have hts : Real.sqrt |t - s| ≤ 1 := by
    have habs : |t - s| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
    calc Real.sqrt |t - s| ≤ Real.sqrt 1 := Real.sqrt_le_sqrt habs
      _ = 1 := Real.sqrt_one
  have hvel : ‖velocity (u.data : Space n)‖ < S.δ := by
    have h2 : c * ‖velocity (u.data : Space n)‖ ^ 2 < (S.δ * Real.sqrt c) ^ 2 :=
      (hv u).trans_lt hu
    rw [mul_pow, Real.sq_sqrt hc.le] at h2
    have h2' : c * ‖velocity (u.data : Space n)‖ ^ 2 < c * S.δ ^ 2 := by
      rw [mul_comm c (S.δ ^ 2)]
      exact h2
    have h3 : ‖velocity (u.data : Space n)‖ ^ 2 < S.δ ^ 2 := lt_of_mul_lt_mul_left h2' hc.le
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) S.pos.le two_ne_zero).mp h3
  calc ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖
      ≤ Real.sqrt |t - s| * ‖velocity (u.data : Space n)‖ := h1
    _ ≤ 1 * ‖velocity (u.data : Space n)‖ := mul_le_mul_of_nonneg_right hts (norm_nonneg _)
    _ = ‖velocity (u.data : Space n)‖ := one_mul _
    _ < S.δ := hvel

/-- The broken geodesic of a polygon with one vertex has energy zero. -/
theorem energy_broken_one {F : ReversibleMetric n} {b : ℝ} (M : PolygonModelData F b 1)
    (q : {q : ZMod 1 → Sphere n // ShortPolygon M.δ q}) : energy F (broken M q) = 0 := by
  rw [energy_broken]
  unfold polyEnergy
  rw [Finset.range_one, Finset.sum_singleton]
  have h : ((0 : ℕ) : ZMod 1) + 1 = ((0 : ℕ) : ZMod 1) := Subsingleton.elim _ _
  rw [h, minEnergy_self F (mem_sphere_zero_iff_norm.mp (q.1 _).2), mul_zero]

/-- The level deformation of a small sublevel into the constant loops. -/
def smallDeformation {F : ReversibleMetric n} {b : ℝ} (M : PolygonModelData F b 1)
    (hb : 0 < b) : LevelDeformation F 0 b b where
  r := Birkhoff.d1 M hb
  H := Birkhoff.g1 M hb
  energy_le := Birkhoff.energy_g1_le M hb
  r_mem := fun x _ => by
    have hx : energy F (x : SphereLoop n) < b ^ 2 := (Birkhoff.mem_lev_iff hb _).mp x.2
    have h1 : (Birkhoff.d1 M hb x : SphereLoop n) = deform M (1, (x : SphereLoop n)) := rfl
    have h0 : energy F (Birkhoff.d1 M hb x : SphereLoop n) = 0 := by
      rw [h1, deform_one M hx]
      exact energy_broken_one M _
    obtain ⟨y, hy⟩ := (energy_eq_zero_iff_constant F _).mp h0
    exact Or.inr ⟨y, hy.symm⟩

/-- Small sublevels carry level deformations into the constant loops. -/
theorem exists_small_deformation (F : ReversibleMetric n) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ → Nonempty (LevelDeformation F 0 b b) := by
  obtain ⟨b₀, hb₀, ⟨M⟩⟩ := exists_one_vertex_model F
  refine ⟨b₀, hb₀, fun b hb hbb => ?_⟩
  exact ⟨smallDeformation (PolygonModelData.mk M.toSegmentData fun u hu =>
    M.space u (hu.trans_le (pow_le_pow_left₀ hb.le hbb 2))) hb⟩

/-- The relative cochains of a pair of equal sets vanish. -/
theorem relative_eq_zero {X : TopCat.{0}} {s t : Set X} (hst : s ⊆ t) (hts : t ⊆ s) (j : ℕ)
    (ψ : RelativeCupCochain.relative (pairOf hst) j) : ψ = 0 := by
  apply RelativeCupCochain.toAmbient_injective (pairOf hst) j
  rw [map_zero]
  have h0 := RelativeCupCochain.restriction_toAmbient (pairOf hst) j ψ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : (pairOf hst).fst ⟶ (pairOf hst).snd,
      ρ ≫ (pairOf hst).map = 𝟙 (pairOf hst).fst :=
    ⟨TopCat.ofHom (ContinuousMap.inclusion hts), by
      ext x
      rfl⟩
  have h1 := Finsler.BorelEvaluation.cochain_comp ρ (pairOf hst).map j
    (RelativeCupCochain.toAmbient (pairOf hst) j ψ)
  rw [h0, hρ, Finsler.BorelCrossing.cochain_id] at h1
  rw [← h1]
  apply cochain_ext
  intro τ
  rw [cochainPullback_eval, cochainEval_zero, cochainEval_zero]

/-- For a ≤ 0 the set t_a consists of the constant loops. -/
theorem lev_subset_consts (F : ReversibleMetric n) {a : ℝ} (ha : a ≤ 0) : lev F a ⊆ consts n := by
  rintro u (hu | hu)
  · exact absurd (lt_of_lt_of_le hu ha) (not_lt.mpr (Real.sqrt_nonneg _))
  · exact hu

/-- For a ≤ 0 the reflection Borel cohomology of (t_a, M) is zero. -/
theorem HR_lev_eq_zero_of_nonpos (F : ReversibleMetric n) {a : ℝ} (ha : a ≤ 0) (q : ℕ)
    (x : HR (levComplex F a) q) : x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mk_eq_zero_iff_bcoboundary]
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero]
  funext j
  exact (relative_eq_zero (consts_subset_lev F a) (lev_subset_consts F ha) j _).symm

/-- For small b > 0 the reflection Borel cohomology of (t_b, M) is zero. -/
theorem exists_HR_lev_eq_zero (F : ReversibleMetric n) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ → ∀ (q : ℕ) (x : HR (levComplex F b) q),
      x = 0 := by
  obtain ⟨b₀, hb₀, h⟩ := exists_small_deformation F
  refine ⟨b₀, hb₀, fun b hb hbb q x => ?_⟩
  obtain ⟨D⟩ := h b hb hbb
  apply (cut_bijective_of_levelDeformation F hb.le D q).1
  rw [HR_lev_eq_zero_of_nonpos F le_rfl q (HRmap (cutHom F hb.le) q x), map_zero]

end

end Finsler.SmallLevel
