module

public import Finsler.Analysis.IntervalH1SphereChart

/-! The radial normalization v ↦ v / ‖v‖ as an H¹ superposition operator. With a smooth
positive cutoff of ‖v‖², the normalization is a C¹ map on the whole ambient space, equal
to v / ‖v‖ when ‖v‖ ≥ 1/2. Hence it maps the open set of periodic H¹ loops staying outside
the ball of radius 1/2 continuously onto the actual sphere loops and fixes every sphere
loop: the sphere loops are a continuous retract of an open subset of the periodic H¹
loops. -/

@[expose] public section

namespace Finsler.SobolevRadialRetraction

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevPairMap
open Finsler.SobolevSphereChart
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

/-- Smooth positive function agreeing with s for s ≥ 1/4 and bounded below by 1/16. -/
def sqDenom (s : ℝ) : ℝ :=
  Real.smoothTransition (16 * (s - 3 / 16)) * s +
    (1 - Real.smoothTransition (16 * (s - 3 / 16))) * (1 / 16)

theorem sqDenom_eq {s : ℝ} (hs : 1 / 4 ≤ s) : sqDenom s = s := by
  have h1 : Real.smoothTransition (16 * (s - 3 / 16)) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp [sqDenom, h1]

theorem sixteenth_le_sqDenom (s : ℝ) : 1 / 16 ≤ sqDenom s := by
  by_cases hs : 3 / 16 ≤ s
  · have h0 := Real.smoothTransition.nonneg (16 * (s - 3 / 16))
    have h1 := Real.smoothTransition.le_one (16 * (s - 3 / 16))
    unfold sqDenom
    nlinarith
  · have h0 : Real.smoothTransition (16 * (s - 3 / 16)) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    simp [sqDenom, h0]

theorem sqDenom_pos (s : ℝ) : 0 < sqDenom s :=
  lt_of_lt_of_le (by norm_num) (sixteenth_le_sqDenom s)

theorem sqDenom_contDiff : ContDiff ℝ 1 sqDenom := by
  have hθ : ContDiff ℝ 1 (fun s : ℝ => Real.smoothTransition (16 * (s - 3 / 16))) :=
    (Real.smoothTransition.contDiff (n := 1)).comp
      (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have h : ContDiff ℝ 1 (fun s : ℝ => Real.smoothTransition (16 * (s - 3 / 16)) * s +
      (1 - Real.smoothTransition (16 * (s - 3 / 16))) * (1 / 16)) :=
    (hθ.mul contDiff_id).add ((contDiff_const.sub hθ).mul contDiff_const)
  exact h

/-- The smooth radial normalization. -/
def radial (x : Ambient n) : Ambient n := (Real.sqrt (sqDenom (‖x‖ ^ 2)))⁻¹ • x

theorem radial_eq {x : Ambient n} (hx : 1 / 2 ≤ ‖x‖) : radial x = ‖x‖⁻¹ • x := by
  have h : 1 / 4 ≤ ‖x‖ ^ 2 := by nlinarith
  simp only [radial, sqDenom_eq h, Real.sqrt_sq (norm_nonneg x)]

theorem norm_radial {x : Ambient n} (hx : 1 / 2 ≤ ‖x‖) : ‖radial x‖ = 1 := by
  have hpos : 0 < ‖x‖ := by linarith
  rw [radial_eq hx, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']

theorem radial_of_norm_one {x : Ambient n} (hx : ‖x‖ = 1) : radial x = x := by
  rw [radial_eq (by rw [hx]; norm_num), hx, inv_one, one_smul]

theorem radial_contDiff : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => radial p.2) := by
  have hn : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => ‖p.2‖ ^ 2) := contDiff_snd.norm_sq ℝ
  have hd : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => sqDenom (‖p.2‖ ^ 2)) :=
    sqDenom_contDiff.comp hn
  have hs : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => Real.sqrt (sqDenom (‖p.2‖ ^ 2))) :=
    hd.sqrt fun p => (sqDenom_pos _).ne'
  have hi : ContDiff ℝ 1 (fun p : Ambient n × Ambient n => (Real.sqrt (sqDenom (‖p.2‖ ^ 2)))⁻¹) :=
    hs.inv fun p => (Real.sqrt_pos.mpr (sqDenom_pos _)).ne'
  exact hi.smul contDiff_snd

/-- The radial normalization of an H¹ loop. -/
def radialData (v : Space n) : Space n := mapData radial_contDiff (0 : Space n) v

theorem representative_radialData (v : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (radialData v) t = radial (continuousRepresentative v t) :=
  representative_mapData _ _ _ ht

theorem radialData_continuous : Continuous (radialData (n := n)) :=
  (mapData_continuous_comp radial_contDiff (f := fun _ : Space n => (0 : Space n))
    (g := fun v : Space n => v) continuous_const continuous_id).congr fun _ => rfl

/-- Periodic loops staying outside the ball of radius 1/2. -/
def radialDomain (n : ℕ) : Set (periodicSubmodule n) :=
  {v | ∀ t ∈ Icc (0 : ℝ) 1, 1 / 2 < ‖continuousRepresentative (v : Space n) t‖}

theorem radialData_periodic (v : periodicSubmodule n) :
    radialData (v : Space n) ∈ periodicSubmodule n :=
  mapData_periodic _ (Submodule.zero_mem _) v.property

/-- The radial retraction onto the actual sphere loops. -/
def retraction (v : radialDomain n) : SphereLoop n where
  data := ⟨radialData (v.1 : Space n), radialData_periodic v.1⟩
  sphere_constraint t := by
    rw [representative_radialData _ t.property]
    exact norm_radial (v.2 t t.property).le

theorem retraction_continuous : Continuous (retraction (n := n)) := by
  apply (sphereLoop_data_isometry n).isEmbedding.continuous_iff.mpr
  have hc : Continuous (fun v : radialDomain n => radialData (v.1 : Space n)) :=
    radialData_continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact hc.congr fun _ => rfl

theorem mem_radialDomain (u : SphereLoop n) : u.data ∈ radialDomain n := by
  intro t ht
  rw [u.sphere_constraint ⟨t, ht⟩]
  norm_num

/-- The retraction fixes every actual sphere loop. -/
theorem retraction_sphereLoop (u : SphereLoop n) :
    retraction ⟨u.data, mem_radialDomain u⟩ = u := by
  apply Finsler.SobolevEnergy.sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (radialData (u.data : Space n)) t =
    continuousRepresentative (u.data : Space n) t
  rw [representative_radialData _ t.property]
  exact radial_of_norm_one (u.sphere_constraint t)

theorem radialDomain_open : IsOpen (radialDomain n) := by
  rw [Metric.isOpen_iff]
  intro v hv
  have hc : ContinuousOn (fun t => ‖continuousRepresentative (v : Space n) t‖) (Icc 0 1) :=
    (continuousRepresentative_continuousOn _).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one) hc
  have hm := hv t₀ ht₀
  refine ⟨(‖continuousRepresentative (v : Space n) t₀‖ - 1 / 2) / 2, by linarith,
    fun w hw t ht => ?_⟩
  have hd : dist (w : Space n) (v : Space n) <
      (‖continuousRepresentative (v : Space n) t₀‖ - 1 / 2) / 2 :=
    Metric.mem_ball.mp hw
  have hdiff := rep_sub_norm_le_dist (w : Space n) (v : Space n) ht
  have hmin' : ‖continuousRepresentative (v : Space n) t₀‖ ≤
      ‖continuousRepresentative (v : Space n) t‖ := hmin ht
  have htri := norm_le_insert' (continuousRepresentative (v : Space n) t)
    (continuousRepresentative (w : Space n) t)
  have hsym := norm_sub_rev (continuousRepresentative (v : Space n) t)
    (continuousRepresentative (w : Space n) t)
  change 1 / 2 < ‖continuousRepresentative (w : Space n) t‖
  linarith

end

end Finsler.SobolevRadialRetraction
