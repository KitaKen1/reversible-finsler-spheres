module

public import Finsler.Analysis.IntervalH1PairMap
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A stereographic chart of the actual H¹ sphere loops around a loop u. The chart map
sends a periodic tangent field h along u to the inverse stereographic loop
((1 - a) u + h) / (1 + a), a = ‖h‖² / 4, and its inverse projects a loop v
stereographically from the antipode of u. Both are one-dimensional superposition
operators, hence continuous in the original H¹ topology; on the open sets where
⟪v, u⟫ > -1/2 and ‖h‖ < √12 at every time they are mutually inverse. -/

@[expose] public section

namespace Finsler.SobolevSphereChart

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevTangent
open Finsler.RationalSphereCurve Finsler.SobolevPairMap
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- Stereographic projection from -x onto the tangent plane at x (scaled by 2). -/
def stereo (x z : Ambient n) : Ambient n :=
  (2 / (1 + ⟪z, x⟫)) • (z - ⟪z, x⟫ • x)

theorem inner_stereo {x z : Ambient n} (hx : ‖x‖ = 1) : ⟪stereo x z, x⟫ = 0 := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  simp only [stereo, inner_smul_left, inner_sub_left, inner_smul_left, hxx]
  simp

theorem norm_sq_tangentPart {x z : Ambient n} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) :
    ‖z - ⟪z, x⟫ • x‖ ^ 2 = 1 - ⟪z, x⟫ ^ 2 := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hzz : ⟪z, z⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hz]; norm_num
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hxx, hzz,
    real_inner_comm x z, RCLike.conj_to_real]
  ring

/-- The rational sphere curve at r = 1 inverts the stereographic projection. -/
theorem ratMap_stereo {x z : Ambient n} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hs : -1 < ⟪z, x⟫) :
    ratMap 1 (x, stereo x z) = z := by
  set s := ⟪z, x⟫ with hsdef
  have hpos : 0 < 1 + s := by linarith
  have hw := norm_sq_tangentPart hx hz
  have ha : aFun 1 (stereo x z) = (1 - s) / (1 + s) := by
    unfold aFun stereo
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← hsdef, hw]
    field_simp
    ring
  unfold ratMap
  simp only [ha]
  have h1 : 1 + (1 - s) / (1 + s) = 2 / (1 + s) := by field_simp; ring
  have h2 : 1 - (1 - s) / (1 + s) = 2 * s / (1 + s) := by field_simp; ring
  rw [h1, h2]
  unfold stereo
  rw [← hsdef]
  have hne : (1 + s) ≠ 0 := hpos.ne'
  have hinv : (2 / (1 + s))⁻¹ = (1 + s) / 2 := by rw [inv_div]
  rw [hinv, one_smul, smul_add, smul_smul, smul_smul]
  have e1 : (1 + s) / 2 * (2 * s / (1 + s)) = s := by field_simp
  have e2 : (1 + s) / 2 * (2 / (1 + s)) = 1 := by field_simp
  rw [e1, e2, one_smul]
  abel

/-- The stereographic projection inverts the rational sphere curve at r = 1. -/
theorem stereo_ratMap {x y : Ambient n} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫ = 0) :
    stereo x (ratMap 1 (x, y)) = y := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyx : ⟪y, x⟫ = 0 := by rw [real_inner_comm]; exact hxy
  have hA := aFun_nonneg 1 y
  set A := aFun 1 y with hAdef
  have hpos : 0 < 1 + A := by linarith
  have hin : ⟪ratMap 1 (x, y), x⟫ = (1 - A) / (1 + A) := by
    unfold ratMap
    rw [← hAdef]
    simp only [inner_smul_left, inner_add_left, hxx, hyx, RCLike.conj_to_real, one_smul]
    field_simp
    ring
  unfold stereo
  rw [hin]
  have h1 : 1 + (1 - A) / (1 + A) = 2 / (1 + A) := by field_simp; ring
  rw [h1]
  unfold ratMap
  rw [← hAdef, one_smul]
  have hne : (1 + A) ≠ 0 := hpos.ne'
  have e : (2 / (2 / (1 + A))) = 1 + A := by field_simp
  rw [e, smul_sub, smul_smul, smul_smul]
  have e1 : (1 + A) * (1 + A)⁻¹ = 1 := by field_simp
  have e2 : (1 + A) * ((1 - A) / (1 + A)) = 1 - A := by field_simp
  rw [e1, one_smul, e2]
  dsimp only
  abel


theorem norm_sq_stereo {x z : Ambient n} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hs : -1 < ⟪z, x⟫) :
    ‖stereo x z‖ ^ 2 = 4 * (1 - ⟪z, x⟫) / (1 + ⟪z, x⟫) := by
  have hpos : 0 < 1 + ⟪z, x⟫ := by linarith
  have hw := norm_sq_tangentPart hx hz
  unfold stereo
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hw]
  field_simp
  ring

theorem norm_stereo_lt {x z : Ambient n} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hs : -1 / 2 < ⟪z, x⟫) :
    ‖stereo x z‖ < Real.sqrt 12 := by
  have hpos : 0 < 1 + ⟪z, x⟫ := by linarith
  rw [Real.lt_sqrt (norm_nonneg _), norm_sq_stereo hx hz (by linarith), div_lt_iff₀ hpos]
  linarith

theorem inner_ratMap_one {x y : Ambient n} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫ = 0) :
    ⟪ratMap 1 (x, y), x⟫ = (1 - aFun 1 y) / (1 + aFun 1 y) := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hyx : ⟪y, x⟫ = 0 := by rw [real_inner_comm]; exact hxy
  have hA := aFun_nonneg 1 y
  unfold ratMap
  simp only [inner_smul_left, inner_add_left, hxx, hyx, RCLike.conj_to_real, one_smul]
  field_simp
  ring

theorem inner_ratMap_one_gt {x y : Ambient n} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫ = 0)
    (hy : ‖y‖ < Real.sqrt 12) : -1 / 2 < ⟪ratMap 1 (x, y), x⟫ := by
  rw [inner_ratMap_one hx hxy]
  have hA := aFun_nonneg 1 y
  have hy2 : ‖y‖ ^ 2 < 12 := (Real.lt_sqrt (norm_nonneg _)).mp hy
  have ha : aFun 1 y < 3 := by unfold aFun; nlinarith
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- Smooth positive denominator agreeing with 1 + s for s ≥ -1/2. -/
def denom (s : ℝ) : ℝ :=
  Real.smoothTransition (4 * (s + 3 / 4)) * (1 + s) +
    (1 - Real.smoothTransition (4 * (s + 3 / 4))) * (1 / 4)

theorem denom_eq {s : ℝ} (hs : -1 / 2 ≤ s) : denom s = 1 + s := by
  have h1 : Real.smoothTransition (4 * (s + 3 / 4)) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp [denom, h1]

theorem quarter_le_denom (s : ℝ) : 1 / 4 ≤ denom s := by
  by_cases hs : -3 / 4 ≤ s
  · have h0 := Real.smoothTransition.nonneg (4 * (s + 3 / 4))
    have h1 := Real.smoothTransition.le_one (4 * (s + 3 / 4))
    unfold denom
    nlinarith
  · have h0 : Real.smoothTransition (4 * (s + 3 / 4)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    simp [denom, h0]

theorem denom_pos (s : ℝ) : 0 < denom s := lt_of_lt_of_le (by norm_num) (quarter_le_denom s)

theorem denom_contDiff : ContDiff ℝ 1 denom := by
  have hθ : ContDiff ℝ 1 (fun s : ℝ => Real.smoothTransition (4 * (s + 3 / 4))) :=
    (Real.smoothTransition.contDiff (n := 1)).comp
      (contDiff_const.mul (contDiff_id.add contDiff_const))
  have h : ContDiff ℝ 1 (fun s : ℝ => Real.smoothTransition (4 * (s + 3 / 4)) * (1 + s) +
      (1 - Real.smoothTransition (4 * (s + 3 / 4))) * (1 / 4)) :=
    (hθ.mul (contDiff_const.add contDiff_id)).add ((contDiff_const.sub hθ).mul contDiff_const)
  exact h

/-- The stereographic projection with a smooth positive denominator. -/
def stereoG (x z : Ambient n) : Ambient n := (2 / denom ⟪z, x⟫) • (z - ⟪z, x⟫ • x)

theorem stereoG_eq {x z : Ambient n} (h : -1 / 2 ≤ ⟪z, x⟫) : stereoG x z = stereo x z := by
  simp only [stereoG, stereo, denom_eq h]

theorem inner_stereoG {x z : Ambient n} (hx : ‖x‖ = 1) : ⟪stereoG x z, x⟫ = 0 := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  simp only [stereoG, inner_smul_left, inner_sub_left, hxx]
  simp

theorem stereoG_contDiff :
    ContDiff ℝ 1 (fun p : Ambient n × Ambient n => stereoG p.1 p.2) := by
  have hs : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => ⟪p.2, p.1⟫) :=
    ContDiff.inner ℝ contDiff_snd contDiff_fst
  have hd : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => denom ⟪p.2, p.1⟫) :=
    denom_contDiff.comp hs
  have hc : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => 2 / denom ⟪p.2, p.1⟫) :=
    contDiff_const.div hd (fun p => (denom_pos _).ne')
  have hv : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => p.2 - ⟪p.2, p.1⟫ • p.1) :=
    contDiff_snd.sub (hs.smul contDiff_fst)
  exact hc.smul hv


section Chart

variable (u : SphereLoop n)

/-- The inverse chart: pointwise stereographic projection from the antipode of u. -/
def chartInvData (v : SphereLoop n) : Space n :=
  mapData stereoG_contDiff (u.data : Space n) (v.data : Space n)

/-- The chart map: the inverse stereographic loop through u in direction h. -/
def chartData (h : Space n) : Space n := mapData (ratMap_contDiff 1) (u.data : Space n) h

theorem representative_chartInvData (v : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (chartInvData u v) t =
      stereoG (continuousRepresentative (u.data : Space n) t)
        (continuousRepresentative (v.data : Space n) t) :=
  representative_mapData _ _ _ ht

theorem representative_chartData (h : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (chartData u h) t =
      ratMap 1 (continuousRepresentative (u.data : Space n) t, continuousRepresentative h t) :=
  representative_mapData _ _ _ ht

theorem chartInvData_mem (v : SphereLoop n) : chartInvData u v ∈ tangentSubmodule u := by
  rw [mem_tangentSubmodule_iff]
  refine ⟨mapData_periodic _ u.data.property v.data.property, fun t => ?_⟩
  rw [representative_chartInvData u v t.property, real_inner_comm]
  exact inner_stereoG (u.sphere_constraint t)

/-- The chart map lands in the actual sphere loops. -/
def chartLoop (h : TangentSpace u) : SphereLoop n where
  data := ⟨chartData u h, mapData_periodic _ u.data.property
    ((mem_tangentSubmodule_iff u h).mp h.property).1⟩
  sphere_constraint t := by
    rw [representative_chartData u h t.property]
    exact norm_ratMap (u.sphere_constraint t)
      (((mem_tangentSubmodule_iff u h).mp h.property).2 t)

/-- The tangent field of the inverse chart. -/
def chartInv (v : SphereLoop n) : TangentSpace u := ⟨chartInvData u v, chartInvData_mem u v⟩

/-- Loops whose angle with u stays below 2π/3. -/
def chartSource : Set (SphereLoop n) :=
  {v | ∀ t ∈ Icc (0 : ℝ) 1, -1 / 2 < ⟪continuousRepresentative (v.data : Space n) t,
    continuousRepresentative (u.data : Space n) t⟫}

/-- Tangent fields of pointwise norm below √12. -/
def chartTarget : Set (TangentSpace u) :=
  {h | ∀ t ∈ Icc (0 : ℝ) 1, ‖continuousRepresentative (h : Space n) t‖ < Real.sqrt 12}

theorem chartInv_mem_target {v : SphereLoop n} (hv : v ∈ chartSource u) :
    chartInv u v ∈ chartTarget u := by
  intro t ht
  change ‖continuousRepresentative (chartInvData u v) t‖ < Real.sqrt 12
  rw [representative_chartInvData u v ht, stereoG_eq (hv t ht).le]
  exact norm_stereo_lt (u.sphere_constraint ⟨t, ht⟩) (v.sphere_constraint ⟨t, ht⟩) (hv t ht)

theorem chartLoop_mem_source {h : TangentSpace u} (hh : h ∈ chartTarget u) :
    chartLoop u h ∈ chartSource u := by
  intro t ht
  change -1 / 2 < ⟪continuousRepresentative (chartData u h) t,
    continuousRepresentative (u.data : Space n) t⟫
  rw [representative_chartData u h ht]
  exact inner_ratMap_one_gt (u.sphere_constraint ⟨t, ht⟩)
    (((mem_tangentSubmodule_iff u h).mp h.property).2 ⟨t, ht⟩) (hh t ht)

theorem chartLoop_chartInv {v : SphereLoop n} (hv : v ∈ chartSource u) :
    chartLoop u (chartInv u v) = v := by
  apply Finsler.SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (chartData u (chartInvData u v)) t =
    continuousRepresentative (v.data : Space n) t
  rw [representative_chartData u _ t.property, representative_chartInvData u v t.property,
    stereoG_eq (hv t t.property).le]
  exact ratMap_stereo (u.sphere_constraint t) (v.sphere_constraint t)
    (by linarith [hv t t.property])

theorem chartInv_chartLoop {h : TangentSpace u} (hh : h ∈ chartTarget u) :
    chartInv u (chartLoop u h) = h := by
  apply Subtype.ext
  apply Finsler.SobolevEnergy.h1_eq_of_representative_eq
  intro t
  change continuousRepresentative (chartInvData u (chartLoop u h)) t =
    continuousRepresentative (h : Space n) t
  have hin := chartLoop_mem_source u hh t t.property
  rw [representative_chartInvData u _ t.property, stereoG_eq hin.le]
  change stereo (continuousRepresentative (u.data : Space n) t)
    (continuousRepresentative (chartData u h) t) = continuousRepresentative (h : Space n) t
  rw [representative_chartData u h t.property]
  exact stereo_ratMap (u.sphere_constraint t)
    (((mem_tangentSubmodule_iff u h).mp h.property).2 t)

theorem mapData_continuous_comp {X : Type*} [TopologicalSpace X]
    {Γ : Ambient n × Ambient n → Ambient n} (hΓ : ContDiff ℝ 1 Γ) {f g : X → Space n}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => mapData hΓ (f x) (g x)) :=
  (mapData_continuous hΓ).comp (hf.prodMk hg)

theorem rep_sub_norm_le_dist (a b : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖continuousRepresentative a t - continuousRepresentative b t‖ ≤ 2 * dist a b := by
  rw [dist_eq_norm a b]
  exact rep_sub_norm_le a b ht

theorem chartInvData_continuous : Continuous (chartInvData u) :=
  (mapData_continuous_comp stereoG_contDiff (f := fun _ : SphereLoop n => (u.data : Space n))
    (g := fun v : SphereLoop n => (v.data : Space n)) continuous_const
    (sphereLoop_data_isometry n).continuous).congr fun _ => rfl

theorem chartInv_continuous : Continuous (chartInv u) :=
  (chartInvData_continuous u).subtype_mk (chartInvData_mem u)

theorem chartLoop_data (h : TangentSpace u) :
    ((chartLoop u h).data : Space n) = chartData u h := rfl

theorem chartLoop_continuous : Continuous (chartLoop u) := by
  apply (sphereLoop_data_isometry n).isEmbedding.continuous_iff.mpr
  have hc : Continuous (fun h : TangentSpace u => chartData u h) :=
    (mapData_continuous_comp (ratMap_contDiff 1) (f := fun _ : TangentSpace u => (u.data : Space n))
      (g := fun h : TangentSpace u => (h : Space n)) continuous_const continuous_subtype_val).congr
      fun _ => rfl
  exact hc.congr fun h => (chartLoop_data u h).symm

theorem chartSource_open : IsOpen (chartSource u) := by
  rw [Metric.isOpen_iff]
  intro v hv
  have hc : ContinuousOn (fun t => ⟪continuousRepresentative (v.data : Space n) t,
      continuousRepresentative (u.data : Space n) t⟫) (Icc 0 1) :=
    (continuousRepresentative_continuousOn _).inner (continuousRepresentative_continuousOn _)
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hc
  have hm := hv t₀ ht₀
  refine ⟨(⟪continuousRepresentative (v.data : Space n) t₀,
    continuousRepresentative (u.data : Space n) t₀⟫ + 1 / 2) / 2, by linarith, fun w hw t ht => ?_⟩
  have hd : dist (w.data : Space n) (v.data : Space n) < (⟪continuousRepresentative
      (v.data : Space n) t₀, continuousRepresentative (u.data : Space n) t₀⟫ + 1 / 2) / 2 :=
    Metric.mem_ball.mp hw
  have hdiff := rep_sub_norm_le_dist (w.data : Space n) (v.data : Space n) ht
  have hcs := abs_real_inner_le_norm (continuousRepresentative (w.data : Space n) t -
    continuousRepresentative (v.data : Space n) t) (continuousRepresentative (u.data : Space n) t)
  have hu1 : ‖continuousRepresentative (u.data : Space n) t‖ = 1 := u.sphere_constraint ⟨t, ht⟩
  rw [hu1, mul_one] at hcs
  have hinner : ⟪continuousRepresentative (w.data : Space n) t,
      continuousRepresentative (u.data : Space n) t⟫ =
      ⟪continuousRepresentative (v.data : Space n) t,
        continuousRepresentative (u.data : Space n) t⟫ +
      ⟪continuousRepresentative (w.data : Space n) t - continuousRepresentative (v.data : Space n) t,
        continuousRepresentative (u.data : Space n) t⟫ := by
    rw [inner_sub_left]
    ring
  have hmin' : ⟪continuousRepresentative (v.data : Space n) t₀,
      continuousRepresentative (u.data : Space n) t₀⟫ ≤
      ⟪continuousRepresentative (v.data : Space n) t,
        continuousRepresentative (u.data : Space n) t⟫ := hmin ht
  have hneg := neg_abs_le ⟪continuousRepresentative (w.data : Space n) t -
    continuousRepresentative (v.data : Space n) t, continuousRepresentative (u.data : Space n) t⟫
  change -1 / 2 < ⟪continuousRepresentative (w.data : Space n) t,
    continuousRepresentative (u.data : Space n) t⟫
  linarith

theorem chartTarget_open : IsOpen (chartTarget u) := by
  rw [Metric.isOpen_iff]
  intro h hh
  have hc : ContinuousOn (fun t => ‖continuousRepresentative (h : Space n) t‖) (Icc 0 1) :=
    (continuousRepresentative_continuousOn _).norm
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr zero_le_one) hc
  have hM := hh t₀ ht₀
  refine ⟨(Real.sqrt 12 - ‖continuousRepresentative (h : Space n) t₀‖) / 2, by linarith,
    fun k hk t ht => ?_⟩
  have hd : dist (k : Space n) (h : Space n) <
      (Real.sqrt 12 - ‖continuousRepresentative (h : Space n) t₀‖) / 2 :=
    Metric.mem_ball.mp hk
  have hdiff := rep_sub_norm_le_dist (k : Space n) (h : Space n) ht
  have hmax' : ‖continuousRepresentative (h : Space n) t‖ ≤
      ‖continuousRepresentative (h : Space n) t₀‖ := hmax ht
  have htri := norm_le_insert' (continuousRepresentative (k : Space n) t)
    (continuousRepresentative (h : Space n) t)
  change ‖continuousRepresentative (k : Space n) t‖ < Real.sqrt 12
  linarith

/-- The stereographic H¹ chart around an actual sphere loop. -/
def chart : OpenPartialHomeomorph (SphereLoop n) (TangentSpace u) where
  toFun := chartInv u
  invFun := chartLoop u
  source := chartSource u
  target := chartTarget u
  map_source' := fun _ hv => chartInv_mem_target u hv
  map_target' := fun _ hh => chartLoop_mem_source u hh
  left_inv' := fun _ hv => chartLoop_chartInv u hv
  right_inv' := fun _ hh => chartInv_chartLoop u hh
  open_source := chartSource_open u
  open_target := chartTarget_open u
  continuousOn_toFun := (chartInv_continuous u).continuousOn
  continuousOn_invFun := (chartLoop_continuous u).continuousOn

theorem mem_chart_source : u ∈ (chart u).source := by
  intro t ht
  change -1 / 2 < ⟪continuousRepresentative (u.data : Space n) t,
    continuousRepresentative (u.data : Space n) t⟫
  rw [real_inner_self_eq_norm_sq, u.sphere_constraint ⟨t, ht⟩]
  norm_num

theorem chart_self : chart u u = 0 := by
  apply Subtype.ext
  apply Finsler.SobolevEnergy.h1_eq_of_representative_eq
  intro t
  change continuousRepresentative (chartInvData u u) t =
    continuousRepresentative ((0 : TangentSpace u) : Space n) t
  have hxx : ⟪continuousRepresentative (u.data : Space n) t,
      continuousRepresentative (u.data : Space n) t⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, u.sphere_constraint t]
    norm_num
  rw [representative_chartInvData u u t.property, stereoG_eq (by rw [hxx]; norm_num)]
  have h0 : continuousRepresentative ((0 : TangentSpace u) : Space n) t = 0 := by
    have := (traceL n t).map_zero
    rw [traceL_apply] at this
    exact this
  rw [h0]
  simp only [stereo, hxx, one_smul, sub_self, smul_zero]

end Chart

end

end Finsler.SobolevSphereChart
