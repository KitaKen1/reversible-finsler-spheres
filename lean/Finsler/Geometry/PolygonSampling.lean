module

public import Finsler.Geometry.PolygonCritical
public import Finsler.Analysis.IntervalH1VariationContinuity
public import Finsler.Geometry.PolygonBasics

/-! Sampling loops below an energy level. The squared L² norm of the velocity of an H¹ sphere
loop is at most its energy divided by the round constant, so by the 1/2-Hölder estimate the
samples of a loop of energy below a² at spacing 1/N are closer than δ once N > a²/(cδ²). The
sampling map to polygons is continuous, the samples of a broken geodesic are its vertices, and
the polygon energy of the samples is at most the energy. -/

@[expose] public section

namespace Finsler.PolygonSampling

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevEnergy Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonBasics
open Finsler.SobolevEnergyDifferential
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- The squared velocity norm is at most the energy over the round constant. -/
theorem exists_velocity_sq_le (F : ReversibleMetric n) :
    ∃ c > 0, ∀ u : SphereLoop n, c * ‖velocity (u.data : Space n)‖ ^ 2 ≤ energy F u := by
  obtain ⟨c, C, hc, -, hb⟩ := exists_pathEnergy_bounds F
  refine ⟨c, hc, fun u => ?_⟩
  have h := (hb (u.data : Space n) (data_mem_spherePath u)).1
  rw [pathEnergy_sphereLoop] at h
  have hn : ‖velocity (u.data : Space n)‖ ^ 2 =
      ∫ t, ‖velocity (u.data : Space n) t‖ ^ 2 ∂intervalMeasure := by
    rw [lp_two_norm_eq_sqrt_integral_norm_sq]
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  rw [hn]
  exact h

/-- A spacing below which samples of loops of energy below a² are closer than δ. -/
theorem exists_sample_spacing (F : ReversibleMetric n) {δ a : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N → ∀ u : SphereLoop n, energy F u < a ^ 2 →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
        ‖continuousRepresentative (u.data : Space n) t -
          continuousRepresentative (u.data : Space n) s‖ < δ := by
  obtain ⟨c, hc, hv⟩ := exists_velocity_sq_le F
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (a ^ 2 / (c * δ ^ 2))
  refine ⟨N₀, fun N hN hNpos u hu s t hs ht hst => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1 := representative_sub_le_sqrt (u.data : Space n) hs ht
  have hvel : ‖velocity (u.data : Space n)‖ ^ 2 < a ^ 2 / c := by
    rw [lt_div_iff₀ hc]
    nlinarith [hv u]
  have hNbig : a ^ 2 / (c * δ ^ 2) < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
  have hprod : Real.sqrt |t - s| * ‖velocity (u.data : Space n)‖ < δ := by
    have hsq : (Real.sqrt |t - s| * ‖velocity (u.data : Space n)‖) ^ 2 < δ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
      have h2 : |t - s| * ‖velocity (u.data : Space n)‖ ^ 2 ≤
          1 / N * ‖velocity (u.data : Space n)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hst (sq_nonneg _)
      have h3 : 1 / N * ‖velocity (u.data : Space n)‖ ^ 2 ≤ 1 / N * (a ^ 2 / c) :=
        mul_le_mul_of_nonneg_left hvel.le (by positivity)
      have h4 : 1 / (N : ℝ) * (a ^ 2 / c) < δ ^ 2 := by
        rw [div_lt_iff₀ (by positivity)] at hNbig
        rw [one_div_mul_eq_div, div_lt_iff₀ hNR]
        rw [div_lt_iff₀ hc]
        nlinarith [sq_nonneg δ]
      linarith
    have hnn : 0 ≤ Real.sqrt |t - s| * ‖velocity (u.data : Space n)‖ := by positivity
    nlinarith [sq_nonneg (Real.sqrt |t - s| * ‖velocity (u.data : Space n)‖ - δ)]
  exact lt_of_le_of_lt h1 hprod

/-- The sampled polygon of a loop. -/
def samplePoly (N : ℕ) (u : SphereLoop n) : ZMod N → Sphere n :=
  fun i => sphereRepresentative u (sampleTime N i)

theorem samplePoly_coe (N : ℕ) (u : SphereLoop n) :
    (fun i => (samplePoly N u i : Ambient n)) = sampleN N u := rfl

/-- Samples of loops below the energy level are short polygons. -/
theorem shortPolygon_samplePoly (F : ReversibleMetric n) {δ a : ℝ} {N : ℕ} [NeZero N]
    (hspace : ∀ u : SphereLoop n, energy F u < a ^ 2 →
      ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
        ‖continuousRepresentative (u.data : Space n) t -
          continuousRepresentative (u.data : Space n) s‖ < δ)
    {u : SphereLoop n} (hu : energy F u < a ^ 2) : ShortPolygon δ (samplePoly N u) := by
  have hN := Nat.pos_of_neZero N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  intro i
  have hk : i.val < N := ZMod.val_lt i
  have hi : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_zmod_val i
  have h1 : (samplePoly N u i : Ambient n) =
      continuousRepresentative (u.data : Space n) ((i.val : ℝ) / N) := by
    have := sampleN_natCast u hk
    rw [hi] at this
    exact this
  have h2 : (samplePoly N u (i + 1) : Ambient n) =
      continuousRepresentative (u.data : Space n) (((i.val : ℝ) + 1) / N) := by
    have := sampleN_natCast_succ u hk
    rw [hi] at this
    exact this
  rw [h1, h2]
  have hs : (i.val : ℝ) / N ∈ Icc (0 : ℝ) 1 := (sampleTime N i).2
  have ht : ((i.val : ℝ) + 1) / N ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hNR]
      exact_mod_cast hk
  apply hspace u hu _ _ hs ht
  rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]

/-- The samples of a broken geodesic are its vertices. -/
theorem samplePoly_polySphereLoop (F : ReversibleMetric n) {δ : ℝ}
    {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
    (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
      ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
      (∀ t, ‖sc P Q t‖ = 1) ∧
      ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
        Finsler.SphereDistance.minEnergy F P Q)
    {N : ℕ} [NeZero N] {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    samplePoly N (polySphereLoop F hseg hq) = q := by
  funext i
  apply Subtype.ext
  have h := congrFun (sampleN_polySphereLoop F hseg hq) i
  exact h

/-- The sampling map is continuous. -/
theorem samplePoly_continuous (N : ℕ) : Continuous (samplePoly (n := n) N) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  have h1 : Continuous (fun u : SphereLoop n => (u.data : Space n)) :=
    (sphereLoop_data_isometry n).continuous
  exact (traceL n (sampleTime N i)).continuous.comp h1

end

end Finsler.PolygonSampling
