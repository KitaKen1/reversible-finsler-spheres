module

public import Finsler.Geometry.PolygonLoop
public import Finsler.Analysis.IntervalH1GeodesicReadback
public import Finsler.Analysis.IntervalH1CurveRealization
public import Finsler.Geometry.EnergyConservation

/-! Critical polygons give closed geodesics. The polygon energy of the samples of an H¹ sphere loop
at k/N is at most its energy, because each restriction to [k/N,(k+1)/N] has energy (1/N) times the
energy on that piece and dominates the minimal energy between its ends; for a broken geodesic
equality holds. If a polygon is stationary for the polygon energy along every differentiable curve
of polygons, then along every H¹ curve of loops through its broken geodesic the difference of the
two energies is nonnegative, vanishes at the broken geodesic and is differentiable there, so the
first variation of the energy vanishes: the broken geodesic is tangent critical, hence a smooth
regular closed geodesic when its energy is positive. -/

@[expose] public section

namespace Finsler.PolygonCritical

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevAffine Finsler.SobolevEnergy Finsler.SobolevCurveVariation
open Finsler.SobolevCurveRealization Finsler.PolygonLoop Finsler.PiecewiseC1
open Finsler.AmbientLagrangian
open Finsler.SphereDistance (minEnergy pathsBetween minEnergy_le)
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- The polygon energy N Σ e(q_k, q_{k+1}). -/
def polyEnergy (F : ReversibleMetric n) (N : ℕ) (q : ZMod N → Ambient n) : ℝ :=
  N * ∑ k ∈ Finset.range N, minEnergy F (q k) (q ((k : ZMod N) + 1))

/-- The sample time of a vertex index. -/
def sampleTime (N : ℕ) (i : ZMod N) : ClosedInterval :=
  ⟨(i.val : ℝ) / N, by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      simp
    · have hN : (0 : ℝ) < N := by exact_mod_cast h
      constructor
      · positivity
      · rw [div_le_one hN]
        have : i.val < N := by
          have : NeZero N := ⟨h.ne'⟩
          exact ZMod.val_lt i
        exact_mod_cast this.le⟩

/-- The samples of a loop at the times k/N. -/
def sampleN (N : ℕ) (u : SphereLoop n) : ZMod N → Ambient n :=
  fun i => continuousRepresentative (u.data : Space n) (sampleTime N i)

theorem sampleN_natCast {N : ℕ} [NeZero N] (u : SphereLoop n) {k : ℕ} (hk : k < N) :
    sampleN N u (k : ZMod N) = continuousRepresentative (u.data : Space n) ((k : ℝ) / N) := by
  unfold sampleN sampleTime
  simp [ZMod.val_natCast_of_lt hk]

theorem sampleN_natCast_succ {N : ℕ} [NeZero N] (u : SphereLoop n) {k : ℕ} (hk : k < N) :
    sampleN N u ((k : ZMod N) + 1) =
      continuousRepresentative (u.data : Space n) (((k : ℝ) + 1) / N) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk1 | hk1
  · have h := sampleN_natCast u hk1
    push_cast at h
    exact h
  · have hz : (k : ZMod N) + 1 = ((0 : ℕ) : ZMod N) := by
      rw [show (k : ZMod N) + 1 = ((k + 1 : ℕ) : ZMod N) by push_cast; rfl,
        show k + 1 = N from hk1, ZMod.natCast_self]
      simp
    rw [show sampleN N u ((k : ZMod N) + 1) = sampleN N u ((0 : ℕ) : ZMod N) from
      congrArg (sampleN N u) hz, sampleN_natCast u hN]
    have hper := Finsler.SobolevCircleRepresentative.periodic_endpoint_eq u.data
    have h1 : ((k : ℝ) + 1) / N = 1 := by
      rw [show ((k : ℝ) + 1) = N by exact_mod_cast hk1, div_self hN'.ne']
    rw [h1]
    simpa using hper

theorem data_mem_spherePath (u : SphereLoop n) : (u.data : Space n) ∈ SpherePath n :=
  fun t ht => u.sphere_constraint ⟨t, ht⟩

/-- The polygon energy of the samples of a loop is at most its energy. -/
theorem polyEnergy_sample_le (F : ReversibleMetric n) {N : ℕ} [NeZero N] (u : SphereLoop n) :
    polyEnergy F N (sampleN N u) ≤ energy F u := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := data_mem_spherePath u
  have hint := density_intervalIntegrable F hw
  set f : ℝ → ℝ := fun t =>
    lagrangian F (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)
    with hf
  have hmem : ∀ k : ℕ, k ≤ N → (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    constructor
    · positivity
    · rw [div_le_one hN']
      exact_mod_cast hk
  have hpiece : ∀ k < N, IntervalIntegrable f volume ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) := by
    intro k hk
    apply hint.mono_set
    rw [uIcc_of_le zero_le_one, uIcc_of_le (div_le_div_of_nonneg_right (by push_cast; linarith)
      hN'.le)]
    exact Icc_subset_Icc (hmem k hk.le).1 (hmem (k + 1) hk).2
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ) / N)
    (n := N) (f := f) (μ := volume) hpiece
  simp only [Nat.cast_zero, zero_div, div_self hN'.ne'] at hsum
  rw [← pathEnergy_sphereLoop, pathEnergy_eq_intervalIntegral, ← hsum]
  unfold polyEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hs := hmem k hk'.le
  have ht := hmem (k + 1) hk'
  have hst : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N :=
    div_le_div_of_nonneg_right (by push_cast; linarith) hN'.le
  have hres := pathEnergy_restrict F (u.data : Space n) hs ht hst
  have hmemp : restrict (u.data : Space n) hs ht hst ∈
      pathsBetween n (continuousRepresentative (u.data : Space n) ((k : ℝ) / N))
        (continuousRepresentative (u.data : Space n) (((k + 1 : ℕ) : ℝ) / N)) :=
    ⟨restrict_mem hw hs ht hst, representative_restrict_zero _ hs ht hst,
      representative_restrict_one _ hs ht hst⟩
  have hle := minEnergy_le F hmemp
  rw [hres] at hle
  have hlen : ((k + 1 : ℕ) : ℝ) / N - (k : ℝ) / N = 1 / N := by
    rw [div_sub_div_same, Nat.cast_succ, add_sub_cancel_left]
  simp only [hlen] at hle
  have h1 : (N : ℝ) * minEnergy F (continuousRepresentative (u.data : Space n) ((k : ℝ) / N))
      (continuousRepresentative (u.data : Space n) (((k + 1 : ℕ) : ℝ) / N)) ≤
      ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), f x := by
    calc (N : ℝ) * minEnergy F (continuousRepresentative (u.data : Space n) ((k : ℝ) / N))
          (continuousRepresentative (u.data : Space n) (((k + 1 : ℕ) : ℝ) / N)) ≤
          (N : ℝ) * (1 / N * ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), f x) :=
          mul_le_mul_of_nonneg_left hle hN'.le
      _ = ∫ x in ((k : ℝ) / N)..(((k + 1 : ℕ) : ℝ) / N), f x := by
          field_simp
  rw [sampleN_natCast u hk', sampleN_natCast_succ u hk']
  push_cast at h1 ⊢
  exact h1

/-- Stationarity of the polygon energy along every differentiable curve of sphere polygons. -/
def PolyCritical (F : ReversibleMetric n) (N : ℕ) (q : ZMod N → Sphere n) : Prop :=
  ∀ (c : ℝ → ZMod N → Ambient n) (c' : ZMod N → Ambient n),
    c 0 = (fun i => (q i : Ambient n)) → (∀ r i, ‖c r i‖ = 1) →
    HasDerivAt c c' 0 → HasDerivAt (fun r => polyEnergy F N (c r)) 0 0

section Critical

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, lagrangian F (sc P Q t, sv P Q t) = minEnergy F P Q)
  {N : ℕ} [NeZero N]

/-- The samples of a broken geodesic are its vertices. -/
theorem sampleN_polySphereLoop {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    sampleN N (polySphereLoop F hseg hq) = fun i => (q i : Ambient n) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  funext i
  have hk : i.val < N := ZMod.val_lt i
  have hi : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_zmod_val i
  rw [← hi, sampleN_natCast _ hk]
  change continuousRepresentative (polyLoop F hseg hq) ((i.val : ℝ) / N) = _
  have hmem : ((i.val : ℝ) / N) ∈ Icc (0 : ℝ) 1 := (sampleTime N i).2
  rw [representative_polyLoop F hseg hq hmem]
  unfold polyCurve
  have hpiece : ((i.val : ℝ) / N) ∈ Icc ((i.val : ℝ) / N) (((i.val : ℝ) + 1) / N) :=
    ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hN'.le⟩
  rw [glue_eq_of_mem_Icc hk (fun j _ => edge_match F hseg hq j) hpiece]
  have h0 : (N : ℝ) * ((i.val : ℝ) / N) - (i.val : ℝ) = 0 := by
    field_simp
    ring
  rw [h0]
  unfold edgeCurve
  rw [(hseg _ _ (hq ((i.val : ℕ) : ZMod N))).2.2.1]

/-- The polygon energy of the vertices is the energy of the broken geodesic. -/
theorem polyEnergy_polySphereLoop {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    polyEnergy F N (fun i => (q i : Ambient n)) = energy F (polySphereLoop F hseg hq) := by
  rw [← pathEnergy_sphereLoop]
  change _ = pathEnergy F (polyLoop F hseg hq)
  rw [pathEnergy_polyLoop F hseg hq]
  rfl

/-- The broken geodesic of a critical polygon is tangent critical. -/
theorem tangentCritical_of_polyCritical {q : ZMod N → Sphere n} (hq : ShortPolygon δ q)
    (hc : PolyCritical F N q) : TangentCritical F (polySphereLoop F hseg hq) := by
  rw [tangentCritical_iff_curve_stationary]
  intro γ h hγ0 hd
  have hE := energy_hasDerivAt_curve F γ hd
  set c : ℝ → ZMod N → Ambient n := fun r => sampleN N (γ r) with hcdef
  have hc0 : c 0 = fun i => (q i : Ambient n) := by
    rw [hcdef]
    simp only
    rw [hγ0, sampleN_polySphereLoop F hseg hq]
  have hcn : ∀ r i, ‖c r i‖ = 1 := fun r i => (γ r).sphere_constraint _
  have hcd : HasDerivAt c (fun i => traceL n (sampleTime N i) h) 0 := by
    rw [hasDerivAt_pi]
    intro i
    exact (traceL n (sampleTime N i)).hasFDerivAt.comp_hasDerivAt 0 hd
  have hP := hc c _ hc0 hcn hcd
  have hg := hE.sub hP
  have hmin : IsLocalMin (fun r => energy F (γ r) - polyEnergy F N (c r)) 0 := by
    apply Filter.Eventually.of_forall
    intro r
    have h1 := polyEnergy_sample_le F (N := N) (γ r)
    have h0 : energy F (γ 0) - polyEnergy F N (c 0) = 0 := by
      rw [hc0, hγ0, polyEnergy_polySphereLoop F hseg hq, sub_self]
    simp only [hcdef] at h0 h1 ⊢
    linarith
  have hA := hmin.hasDerivAt_eq_zero hg
  rw [sub_zero] at hA
  rw [hA] at hE
  exact hE

/-- A critical polygon of positive energy is the polygon of a smooth regular closed geodesic. -/
theorem exists_closedGeodesic_of_polyCritical {q : ZMod N → Sphere n} (hq : ShortPolygon δ q)
    (hc : PolyCritical F N q) (hpos : 0 < polyEnergy F N (fun i => (q i : Ambient n))) :
    ∃ γ : Finsler.Geodesics.ClosedGeodesic F, ∀ t,
      ((γ.loop t : Sphere n) : Ambient n) =
        Finsler.SobolevCircleRepresentative.realMap (polySphereLoop F hseg hq).data t :=
  Finsler.SobolevGeodesicReadback.exists_closedGeodesic_of_tangentCritical F _
    (tangentCritical_of_polyCritical F hseg hq hc)
    (by rw [← polyEnergy_polySphereLoop F hseg hq]; exact hpos)

/-- A regular smooth loop has nonzero ambient velocity. -/
theorem deriv_position_ne_zero (γ : Finsler.Loops.SmoothLoop n) (hreg : Finsler.Geodesics.Regular γ) (t : ℝ) :
    deriv (Finsler.EnergyConservation.position γ) t ≠ 0 := by
  rw [← Finsler.EnergyConservation.velocity_eq_deriv]
  have h := (loopJet_mem_slitDomain γ hreg t).2
  rw [loopJet, Finsler.SphereRetraction.lift_ambientPair, slitBundle_eq] at h
  exact h

omit [NeZero N] in
theorem polyCurve_eq_edge (q : ZMod N → Sphere n) {k : ℕ} (hk : k < N)
    {t : ℝ} (ht : t ∈ Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :
    polyCurve N sc q t = sc (q k) (q ((k : ZMod N) + 1)) ((N : ℝ) * t - k) :=
  glue_eq_of_mem_Ico hk _ ht

include hseg in
/-- Zero edges are excluded at critical polygons of positive energy. -/
theorem edge_ne_of_polyCritical (hconst : ∀ P : Sphere n, ∀ t, sc P P t = P)
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hc : PolyCritical F N q)
    (hpos : 0 < polyEnergy F N (fun i => (q i : Ambient n))) {k : ℕ} (hk : k < N) :
    q k ≠ q ((k : ZMod N) + 1) := by
  intro heq
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨γ, hγ⟩ := exists_closedGeodesic_of_polyCritical F hseg hq hc hpos
  set t₀ : ℝ := ((k : ℝ) + 1 / 2) / N with ht₀
  have hlo : (k : ℝ) / N < t₀ := by
    rw [ht₀]
    exact div_lt_div_of_pos_right (by linarith) hN'
  have hhi : t₀ < ((k : ℝ) + 1) / N := by
    rw [ht₀]
    exact div_lt_div_of_pos_right (by linarith) hN'
  have hconst_on : ∀ t ∈ Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N),
      Finsler.EnergyConservation.position γ.loop t = (q k : Ambient n) := by
    intro t ht
    have h01 : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact le_trans (by positivity) ht.1.le
      · have : ((k : ℝ) + 1) / N ≤ 1 := by
          rw [div_le_one hN']
          exact_mod_cast hk
        linarith [ht.2]
    change ((γ.loop t : Sphere n) : Ambient n) = _
    rw [hγ t, Finsler.SobolevCircleRepresentative.realMap_eqOn _ h01]
    change continuousRepresentative (polyLoop F hseg hq) t = _
    rw [representative_polyLoop F hseg hq h01, polyCurve_eq_edge q hk ⟨ht.1.le, ht.2⟩,
      ← heq, hconst]
  have hev : Finsler.EnergyConservation.position γ.loop =ᶠ[𝓝 t₀] fun _ => (q k : Ambient n) := by
    filter_upwards [Ioo_mem_nhds hlo hhi] with t ht
    exact hconst_on t ht
  have hd := hev.deriv_eq
  rw [deriv_const] at hd
  exact deriv_position_ne_zero γ.loop γ.regular t₀ hd

end Critical

end

end Finsler.PolygonCritical
