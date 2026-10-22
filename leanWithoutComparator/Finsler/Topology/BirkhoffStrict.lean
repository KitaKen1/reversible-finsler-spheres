module

public import Finsler.Topology.Birkhoff
public import Finsler.Analysis.IntervalH1SmoothMultiplier
public import Finsler.Analysis.IntervalH1CurveRealization
public import Finsler.Analysis.SphereDistance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Strictness of the curve shortening map. The minimal energy between two points of the sphere
is the square of a distance which satisfies the triangle inequality and is bounded by a
multiple of the round distance for close points; hence along curves of polygons whose vertices
have zero derivative, the polygon energy has zero derivative. If a loop has the energy of the
polygon of its samples at given times, and no loop has less energy than the polygon of its
samples at these times, then the first variation of the energy vanishes on tangent fields which
vanish at the sample times. A tangent field is the sum of one vanishing on the grid k/N and one
vanishing on the staggered grid (k + 1/2)/N (multiply by cos²(πNt)). Therefore a loop which has
the energy of its sample polygon on both grids is tangent critical. For the curve shortening
map this says: if straightening on the staggered grid does not decrease the energy of a broken
geodesic, the broken geodesic is tangent critical, hence a closed geodesic or constant. -/

@[expose] public section

namespace Finsler.BirkhoffStrict

open Set Filter Topology Asymptotics
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevEnergy Finsler.SobolevShiftEnergy Finsler.SobolevEnergyDifferential
open Finsler.SobolevCurveVariation Finsler.SobolevCurveRealization Finsler.SobolevTangent
open Finsler.SobolevSmoothMultiplier Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonLoop Finsler.PolygonModel Finsler.MilnorHomotopy Finsler.MilnorEquivariance
open Finsler.SphereDistance (minEnergy dist dist_sq dist_nonneg dist_comm dist_triangle_sphere
  exists_dist_upper)
open scoped ContDiff RealInnerProductSpace

noncomputable section

/-- The circle of parameters. -/
local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

variable {n : ℕ}

/-- Along curves of points of the sphere with zero derivative, the minimal energy has zero
derivative. -/
theorem minEnergy_hasDerivAt_zero (F : ReversibleMetric n) (hn : 1 ≤ n) {p q : ℝ → Ambient n}
    (hp1 : ∀ r, ‖p r‖ = 1) (hq1 : ∀ r, ‖q r‖ = 1) (hp : HasDerivAt p 0 0)
    (hq : HasDerivAt q 0 0) : HasDerivAt (fun r => minEnergy F (p r) (q r)) 0 0 := by
  obtain ⟨K, hK, hup⟩ := exists_dist_upper F
  have hpo : (fun r : ℝ => p r - p 0) =o[𝓝 0] fun r : ℝ => r := by
    have h := hasDerivAt_iff_isLittleO_nhds_zero.mp hp
    simpa using h
  have hqo : (fun r : ℝ => q r - q 0) =o[𝓝 0] fun r : ℝ => r := by
    have h := hasDerivAt_iff_isLittleO_nhds_zero.mp hq
    simpa using h
  have hsum : (fun r : ℝ => ‖p r - p 0‖ + ‖q r - q 0‖) =o[𝓝 0] fun r : ℝ => r :=
    hpo.norm_left.add hqo.norm_left
  have hpc : ∀ᶠ r in 𝓝 (0 : ℝ), ‖p r - p 0‖ ≤ 1 := by
    have h : Tendsto (fun r => ‖p r - p 0‖) (𝓝 0) (𝓝 0) := by
      have h1 := (hp.continuousAt.sub (continuousAt_const (y := p 0))).norm
      simpa using h1.tendsto
    exact h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hqc : ∀ᶠ r in 𝓝 (0 : ℝ), ‖q r - q 0‖ ≤ 1 := by
    have h : Tendsto (fun r => ‖q r - q 0‖) (𝓝 0) (𝓝 0) := by
      have h1 := (hq.continuousAt.sub (continuousAt_const (y := q 0))).norm
      simpa using h1.tendsto
    exact h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hbound : ∀ᶠ r in 𝓝 (0 : ℝ),
      ‖minEnergy F (p r) (q r) - minEnergy F (p 0) (q 0)‖ ≤
        (K * (2 * dist F (p 0) (q 0) + 2 * K)) * ‖‖p r - p 0‖ + ‖q r - q 0‖‖ := by
    filter_upwards [hpc, hqc] with r hpr hqr
    have hx : 0 ≤ ‖p r - p 0‖ := norm_nonneg _
    have hy : 0 ≤ ‖q r - q 0‖ := norm_nonneg _
    have e1 : dist F (p 0) (p r) ≤ K * ‖p r - p 0‖ := hup (p 0) (p r) (hp1 0) (hp1 r) hpr
    have e2 : dist F (q 0) (q r) ≤ K * ‖q r - q 0‖ := hup (q 0) (q r) (hq1 0) (hq1 r) hqr
    have t1 : dist F (p r) (q r) ≤ dist F (p r) (p 0) + dist F (p 0) (q r) :=
      dist_triangle_sphere F hn (hp1 r) (hp1 0) (hq1 r)
    have t2 : dist F (p 0) (q r) ≤ dist F (p 0) (q 0) + dist F (q 0) (q r) :=
      dist_triangle_sphere F hn (hp1 0) (hq1 0) (hq1 r)
    have t3 : dist F (p 0) (q 0) ≤ dist F (p 0) (p r) + dist F (p r) (q 0) :=
      dist_triangle_sphere F hn (hp1 0) (hp1 r) (hq1 0)
    have t4 : dist F (p r) (q 0) ≤ dist F (p r) (q r) + dist F (q r) (q 0) :=
      dist_triangle_sphere F hn (hp1 r) (hq1 r) (hq1 0)
    rw [dist_comm F (p r) (p 0)] at t1
    rw [dist_comm F (q r) (q 0)] at t4
    have hd0 : 0 ≤ dist F (p r) (q r) := dist_nonneg F _ _
    have hD0 : 0 ≤ dist F (p 0) (q 0) := dist_nonneg F _ _
    set d := dist F (p r) (q r) with hd
    set D := dist F (p 0) (q 0) with hD
    set t := K * (‖p r - p 0‖ + ‖q r - q 0‖) with ht
    have ht0 : 0 ≤ t := by positivity
    have ht2 : t ≤ 2 * K := by
      rw [ht]
      nlinarith
    have h1 : |d - D| ≤ t := by
      rw [abs_le, ht]
      constructor <;> linarith
    have h2 : d + D ≤ 2 * D + t := by
      have := (abs_le.mp h1).2
      linarith
    rw [← dist_sq F (p r) (q r), ← dist_sq F (p 0) (q 0), Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg hx hy)]
    calc |d ^ 2 - D ^ 2| = |d - D| * (d + D) := by
          rw [show d ^ 2 - D ^ 2 = (d - D) * (d + D) by ring, abs_mul,
            abs_of_nonneg (add_nonneg hd0 hD0)]
      _ ≤ t * (2 * D + t) := mul_le_mul h1 h2 (add_nonneg hd0 hD0) ht0
      _ ≤ t * (2 * D + 2 * K) := by
          apply mul_le_mul_of_nonneg_left _ ht0
          linarith
      _ = K * (2 * D + 2 * K) * (‖p r - p 0‖ + ‖q r - q 0‖) := by
          rw [ht]
          ring
  have hO : (fun r : ℝ => minEnergy F (p r) (q r) - minEnergy F (p 0) (q 0)) =O[𝓝 0]
      fun r : ℝ => ‖p r - p 0‖ + ‖q r - q 0‖ := IsBigO.of_bound _ hbound
  have hfin := hO.trans_isLittleO hsum
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simpa using hfin

/-- Along curves of polygons on the sphere whose vertices have zero derivative, the polygon
energy has zero derivative. -/
theorem polyEnergy_hasDerivAt_zero (F : ReversibleMetric n) (hn : 1 ≤ n) {N : ℕ}
    {c : ℝ → ZMod N → Ambient n} (hc1 : ∀ r i, ‖c r i‖ = 1) (hc : HasDerivAt c 0 0) :
    HasDerivAt (fun r => polyEnergy F N (c r)) 0 0 := by
  have hci : ∀ i, HasDerivAt (fun r => c r i) 0 0 := fun i => hasDerivAt_pi.mp hc i
  have hsum : HasDerivAt
      (fun r => ∑ k ∈ Finset.range N, minEnergy F (c r k) (c r ((k : ZMod N) + 1)))
      (∑ _k ∈ Finset.range N, (0 : ℝ)) 0 :=
    HasDerivAt.fun_sum fun k _ =>
      minEnergy_hasDerivAt_zero F hn (fun r => hc1 r _) (fun r => hc1 r _) (hci _) (hci _)
  have h2 := hsum.const_mul (N : ℝ)
  rw [Finset.sum_const_zero, mul_zero] at h2
  exact h2

section Stationary

variable (F : ReversibleMetric n) (hn : 1 ≤ n) {N : ℕ} (T : ZMod N → ClosedInterval)

include hn in
/-- If a loop has the energy of the polygon of its samples at the times T, and no loop has less
energy than the polygon of its samples at these times, then the first variation vanishes on
tangent fields which vanish at the times T. -/
theorem variation_zero_of_samples (u : SphereLoop n)
    (hle : ∀ v : SphereLoop n,
      polyEnergy F N (fun i => continuousRepresentative (v.data : Space n) (T i)) ≤ energy F v)
    (heq : polyEnergy F N (fun i => continuousRepresentative (u.data : Space n) (T i)) =
      energy F u)
    (h : TangentSpace u) (hz : ∀ i, continuousRepresentative (h : Space n) (T i) = 0) :
    variationL F u (h : Space n) = 0 := by
  obtain ⟨γ, hγ0, hd⟩ := exists_curve_realization u h
  have hE := energy_hasDerivAt_curve F γ hd
  have hcn : ∀ r (i : ZMod N), ‖continuousRepresentative ((γ r).data : Space n) (T i)‖ = 1 :=
    fun r i => (γ r).sphere_constraint _
  have hcd : HasDerivAt
      (fun r (i : ZMod N) => continuousRepresentative ((γ r).data : Space n) (T i)) 0 0 := by
    rw [hasDerivAt_pi]
    intro i
    have hi : HasDerivAt (fun r => continuousRepresentative ((γ r).data : Space n) (T i))
        (traceL n (T i) (h : Space n)) 0 :=
      (traceL n (T i)).hasFDerivAt.comp_hasDerivAt 0 hd
    rw [show traceL n (T i) (h : Space n) = 0 from hz i] at hi
    exact hi
  have hP := polyEnergy_hasDerivAt_zero F hn hcn hcd
  have hg := hE.sub hP
  have hmin : IsLocalMin (fun r => energy F (γ r) -
      polyEnergy F N (fun i => continuousRepresentative ((γ r).data : Space n) (T i))) 0 := by
    apply Filter.Eventually.of_forall
    intro r
    have h1 := hle (γ r)
    have h0 : energy F (γ 0) -
        polyEnergy F N (fun i => continuousRepresentative ((γ 0).data : Space n) (T i)) = 0 := by
      rw [hγ0, heq, sub_self]
    change energy F (γ 0) -
        polyEnergy F N (fun i => continuousRepresentative ((γ 0).data : Space n) (T i)) ≤
      energy F (γ r) -
        polyEnergy F N (fun i => continuousRepresentative ((γ r).data : Space n) (T i))
    linarith
  have hA := hmin.hasDerivAt_eq_zero hg
  rw [sub_zero, hγ0] at hA
  exact hA

end Stationary

section Grids

variable {N : ℕ} [NeZero N]

/-- The staggered sample time (k + 1/2)/N. -/
def stagTime (N : ℕ) [NeZero N] (i : ZMod N) : ClosedInterval :=
  ⟨((i.val : ℝ) + 1 / 2) / N, by
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
    have hi : (i.val : ℝ) + 1 ≤ N := by exact_mod_cast ZMod.val_lt i
    constructor
    · positivity
    · rw [div_le_one hN]
      linarith⟩

/-- The samples of the loop rotated by 1/(2N) are the values at the staggered times. -/
theorem sampleN_vadd_half (v : SphereLoop n) (i : ZMod N) :
    sampleN N ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ v) i =
      continuousRepresentative (v.data : Space n) (stagTime N i) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have h1 : ((i.val : ℝ) / N) ∈ Icc (0 : ℝ) 1 := (sampleTime N i).2
  have h2 : ((i.val : ℝ) / N + 1 / (2 * N)) ∈ Icc (0 : ℝ) 1 := by
    have he : (i.val : ℝ) / N + 1 / (2 * N) = ((i.val : ℝ) + 1 / 2) / N := by
      field_simp
    rw [he]
    exact (stagTime N i).2
  have he : ((stagTime N i : ClosedInterval) : ℝ) = (i.val : ℝ) / N + 1 / (2 * N) := by
    change ((i.val : ℝ) + 1 / 2) / N = _
    field_simp
  change continuousRepresentative
    (((((1 / (2 * N) : ℝ)) : Circ) +ᵥ v).data : Space n) ((i.val : ℝ) / N) = _
  rw [← pt_coe _ h1, pt_vadd, pt_coe _ h2, he]

end Grids

/-- The cut-off cos²(πNt) = (1 + cos(2πNt))/2: one on the grid, zero on the staggered grid. -/
def cutoff (N : ℕ) (t : ℝ) : ℝ := (1 + Real.cos (2 * Real.pi * N * t)) / 2

theorem cutoff_contDiff (N : ℕ) : ContDiff ℝ ∞ (cutoff N) := by
  unfold cutoff
  fun_prop

theorem cutoff_periodic (N : ℕ) : cutoff N 1 = cutoff N 0 := by
  unfold cutoff
  rw [mul_one, mul_zero, Real.cos_zero, show 2 * Real.pi * (N : ℝ) = (N : ℝ) * (2 * Real.pi) by ring,
    Real.cos_nat_mul_two_pi]

theorem cutoff_sampleTime {N : ℕ} [NeZero N] (i : ZMod N) :
    cutoff N ((sampleTime N i : ClosedInterval) : ℝ) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold cutoff
  change (1 + Real.cos (2 * Real.pi * N * ((i.val : ℝ) / N))) / 2 = 1
  rw [show 2 * Real.pi * (N : ℝ) * ((i.val : ℝ) / N) = (i.val : ℝ) * (2 * Real.pi) by
    field_simp, Real.cos_nat_mul_two_pi]
  norm_num

theorem cutoff_stagTime {N : ℕ} [NeZero N] (i : ZMod N) :
    cutoff N ((stagTime N i : ClosedInterval) : ℝ) = 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold cutoff
  change (1 + Real.cos (2 * Real.pi * N * (((i.val : ℝ) + 1 / 2) / N))) / 2 = 0
  rw [show 2 * Real.pi * (N : ℝ) * (((i.val : ℝ) + 1 / 2) / N) =
    (i.val : ℝ) * (2 * Real.pi) + Real.pi by field_simp, Real.cos_nat_mul_two_pi_add_pi]
  norm_num

section Split

/-- The product of a field with the cut-off. -/
def cutoffField (N : ℕ) (k : Space n) : Space n :=
  fieldData (cutoff_contDiff N) (ContinuousLinearMap.id ℝ (Ambient n)) k

theorem cutoffField_apply (N : ℕ) (k : Space n) (t : ClosedInterval) :
    continuousRepresentative (cutoffField N k) t =
      cutoff N (t : ℝ) • continuousRepresentative k t :=
  representative_fieldData (cutoff_contDiff N) (ContinuousLinearMap.id ℝ (Ambient n)) k t.2

/-- The product of a tangent field with the cut-off is a tangent field. -/
theorem cutoffField_mem (N : ℕ) (u : SphereLoop n) (h : TangentSpace u) :
    cutoffField N (h : Space n) ∈ tangentSubmodule u := by
  rw [mem_tangentSubmodule_iff]
  refine ⟨fieldData_periodic (cutoff_contDiff N) _ ⟨(h : Space n), tangent_periodic u h⟩
    (cutoff_periodic N), fun t => ?_⟩
  rw [cutoffField_apply, inner_smul_right, tangent_orthogonal u h t, mul_zero]

variable {N : ℕ} [NeZero N]

/-- The product with the cut-off vanishes on the staggered grid. -/
theorem cutoffField_stag (k : Space n) (i : ZMod N) :
    continuousRepresentative (cutoffField N k) (stagTime N i) = 0 := by
  rw [cutoffField_apply, cutoff_stagTime, zero_smul]

/-- The product with the cut-off agrees with the field on the grid. -/
theorem cutoffField_grid (k : Space n) (i : ZMod N) :
    continuousRepresentative (cutoffField N k) (sampleTime N i) =
      continuousRepresentative k (sampleTime N i) := by
  rw [cutoffField_apply, cutoff_sampleTime]
  exact one_smul ℝ _

/-- The difference of a field and its product with the cut-off vanishes on the grid. -/
theorem sub_cutoffField_grid (k : Space n) (i : ZMod N) :
    continuousRepresentative (k - cutoffField N k) (sampleTime N i) = 0 := by
  have e : continuousRepresentative (k - cutoffField N k) (sampleTime N i) =
      continuousRepresentative k (sampleTime N i) -
        continuousRepresentative (cutoffField N k) (sampleTime N i) :=
    map_sub (traceL n (sampleTime N i)) k (cutoffField N k)
  rw [e, cutoffField_grid, sub_self]

/-- No loop has less energy than the polygon of its values on the staggered grid. -/
theorem polyEnergy_stag_le (F : ReversibleMetric n) (v : SphereLoop n) :
    polyEnergy F N (fun i => continuousRepresentative (v.data : Space n) (stagTime N i)) ≤
      energy F v := by
  have h := polyEnergy_sample_le F (N := N) ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ v)
  rw [energy_vadd] at h
  have he : sampleN N ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ v) =
      fun i => continuousRepresentative (v.data : Space n) (stagTime N i) :=
    funext fun i => sampleN_vadd_half v i
  rw [he] at h
  exact h

/-- The polygon of the values on the staggered grid is the sample polygon of the rotated
loop. -/
theorem polyEnergy_stag_eq (F : ReversibleMetric n) (v : SphereLoop n) :
    polyEnergy F N (fun i => continuousRepresentative (v.data : Space n) (stagTime N i)) =
      polyEnergy F N (sampleN N ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ v)) := by
  have he : sampleN N ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ v) =
      fun i => continuousRepresentative (v.data : Space n) (stagTime N i) :=
    funext fun i => sampleN_vadd_half v i
  rw [he]

end Split

section Main

variable (F : ReversibleMetric n) (hn : 1 ≤ n) {N : ℕ} [NeZero N]

include hn in
/-- If a loop has the energy of its sample polygon on the grid, the first variation vanishes on
the part of a tangent field which vanishes on the grid. -/
theorem variation_grid_part (u : SphereLoop n)
    (h0 : polyEnergy F N (sampleN N u) = energy F u) (h : TangentSpace u) :
    variationL F u ((h : Space n) - cutoffField N (h : Space n)) = 0 :=
  variation_zero_of_samples F hn (sampleTime N) u (fun v => polyEnergy_sample_le F v) h0
    ⟨(h : Space n) - cutoffField N (h : Space n),
      (tangentSubmodule u).sub_mem h.2 (cutoffField_mem N u h)⟩
    (fun i => sub_cutoffField_grid (h : Space n) i)

include hn in
/-- If a loop has the energy of its sample polygon on the staggered grid, the first variation
vanishes on the part of a tangent field which vanishes on the staggered grid. -/
theorem variation_stag_part (u : SphereLoop n)
    (h1 : polyEnergy F N (sampleN N ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u)) = energy F u)
    (h : TangentSpace u) : variationL F u (cutoffField N (h : Space n)) = 0 :=
  variation_zero_of_samples F hn (stagTime N) u (fun v => polyEnergy_stag_le F v)
    ((polyEnergy_stag_eq F u).trans h1) ⟨cutoffField N (h : Space n), cutoffField_mem N u h⟩
    (fun i => cutoffField_stag (h : Space n) i)

omit [NeZero N] in
/-- The first variation vanishes on a field if it vanishes on two parts of it. -/
theorem variationL_split (u : SphereLoop n) (k k₁ : Space n)
    (hv0 : variationL F u (k - k₁) = 0) (hv1 : variationL F u k₁ = 0) :
    variationL F u k = 0 := by
  have e : (k - k₁) + k₁ = k := sub_add_cancel k k₁
  have hadd : variationL F u ((k - k₁) + k₁) =
      variationL F u (k - k₁) + variationL F u k₁ := map_add (variationL F u) (k - k₁) k₁
  calc variationL F u k = variationL F u ((k - k₁) + k₁) := congrArg (variationL F u) e.symm
    _ = variationL F u (k - k₁) + variationL F u k₁ := hadd
    _ = 0 + 0 := congrArg₂ (· + ·) hv0 hv1
    _ = 0 := add_zero 0

include hn in
/-- A loop which has the energy of its sample polygon on the grid and on the staggered grid is
tangent critical. -/
theorem tangentCritical_of_two_grids (u : SphereLoop n)
    (h0 : polyEnergy F N (sampleN N u) = energy F u)
    (h1 : polyEnergy F N (sampleN N ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ u)) = energy F u) :
    TangentCritical F u := by
  rw [tangentCritical_iff]
  intro h
  exact (variationL_apply F u (h : Space n)).symm.trans
    (variationL_split F u (h : Space n) (cutoffField N (h : Space n))
      (variation_grid_part F hn u h0 h) (variation_stag_part F hn u h1 h))

end Main

section Shortening

variable {F : ReversibleMetric n} {a : ℝ} {N : ℕ} [NeZero N] (M : PolygonModelData F a N)

/-- If straightening on the staggered grid does not decrease the energy of a broken geodesic,
the broken geodesic is tangent critical. -/
theorem tangentCritical_of_stag_energy_eq (hn : 1 ≤ n)
    (q : {q : ZMod N → Sphere n // ShortPolygon M.δ q})
    (hq : energy F (broken M q) < a ^ 2)
    (heq : energy F (Birkhoff.stag M 1 (broken M q)) = energy F (broken M q)) :
    TangentCritical F (broken M q) := by
  have hq' : energy F ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ broken M q) < a ^ 2 := by
    rw [energy_vadd]
    exact hq
  have h0 : polyEnergy F N (sampleN N (broken M q)) = energy F (broken M q) := by
    rw [← samplePoly_coe, sample_broken M q, energy_broken M q]
  have h1 : polyEnergy F N (sampleN N ((((1 / (2 * N) : ℝ)) : Circ) +ᵥ broken M q)) =
      energy F (broken M q) := by
    rw [← heq]
    unfold Birkhoff.stag
    rw [energy_vadd, deform_one M hq', energy_broken, samplePoly_coe]
  exact tangentCritical_of_two_grids F hn (broken M q) h0 h1

end Shortening

end

end Finsler.BirkhoffStrict
