module

public import Finsler.Geometry.SegmentCurves
public import Finsler.Analysis.PiecewiseC1
public import Finsler.Analysis.IntervalH1CircleAction
public import Finsler.Analysis.IntervalH1EnergyZero

/-! Closed polygons with short edges and their broken geodesics. For vertices q : ZMod N → Sⁿ with
consecutive vertices closer than δ, the broken geodesic glues the short segments of the edges on
the pieces [k/N, (k+1)/N]. It is an H¹ sphere loop whose energy is N Σ e(q_k, q_{k+1}), and the
map q ↦ b_N(q) is continuous into the H¹ graph space, since positions and velocities of the pieces
converge uniformly. -/

@[expose] public section

namespace Finsler.PolygonLoop

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevOfPrimitive Finsler.SobolevC1Continuity Finsler.PiecewiseC1
open Finsler.AmbientLagrangian Finsler.SphereRetraction Finsler.EnergyConservation
open Finsler.SphereDistance (minEnergy)
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

theorem lagrangian_continuousAt (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z.1 ≠ 0) : ContinuousAt (lagrangian F) z :=
  (F.continuous.continuousAt.comp (lift_smoothAt hz).continuousAt).pow 2

/-- Consecutive vertices of a closed polygon are closer than δ. -/
def ShortPolygon (δ : ℝ) {N : ℕ} (q : ZMod N → Sphere n) : Prop :=
  ∀ i : ZMod N, ‖(q (i + 1) : Ambient n) - q i‖ < δ

/-- The k-th edge curve. -/
def edgeCurve {N : ℕ} (c : Sphere n → Sphere n → ℝ → Ambient n) (q : ZMod N → Sphere n) (k : ℕ) :
    ℝ → Ambient n :=
  c (q k) (q ((k : ZMod N) + 1))

/-- The broken geodesic as a curve. -/
def polyCurve (N : ℕ) (sc : Sphere n → Sphere n → ℝ → Ambient n) (q : ZMod N → Sphere n) :
    ℝ → Ambient n :=
  glue N (edgeCurve sc q)

/-- Its velocity. -/
def polyVel (N : ℕ) (sv : Sphere n → Sphere n → ℝ → Ambient n) (q : ZMod N → Sphere n) :
    ℝ → Ambient n :=
  glueVel N (edgeCurve sv q)

section Loop

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, lagrangian F (sc P Q t, sv P Q t) = minEnergy F P Q)
  {N : ℕ} [NeZero N] {q : ZMod N → Sphere n} (hq : ShortPolygon δ q)

include hseg hq

omit [NeZero N] in
theorem edge_hasDerivAt (k : ℕ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (edgeCurve sc q k) (edgeCurve sv q k s) s :=
  (hseg _ _ (hq k)).1 s hs

omit [NeZero N] in
theorem edge_continuousOn (k : ℕ) : ContinuousOn (edgeCurve sc q k) (Icc 0 1) :=
  fun _ hs => (edge_hasDerivAt F hseg hq k hs).continuousAt.continuousWithinAt

omit [NeZero N] in
theorem edgeVel_continuousOn (k : ℕ) : ContinuousOn (edgeCurve sv q k) (Icc 0 1) :=
  (hseg _ _ (hq k)).2.1

omit [NeZero N] in
theorem edge_match (j : ℕ) : edgeCurve sc q j 1 = edgeCurve sc q (j + 1) 0 := by
  unfold edgeCurve
  rw [(hseg _ _ (hq j)).2.2.2.1, (hseg _ _ (hq (j + 1 : ℕ))).2.2.1]
  push_cast
  rfl

theorem polyCurve_continuousOn : ContinuousOn (polyCurve N sc q) (Icc 0 1) :=
  glue_continuousOn (Nat.pos_of_neZero N) (fun k _ => edge_continuousOn F hseg hq k)
    (fun j _ => edge_match F hseg hq j)

theorem polyCurve_eq_add_integral {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    polyCurve N sc q t = polyCurve N sc q 0 + ∫ s in (0 : ℝ)..t, polyVel N sv q s :=
  glue_eq_add_integral (Nat.pos_of_neZero N) (fun k _ => edge_continuousOn F hseg hq k)
    (fun k _ _ hs => edge_hasDerivAt F hseg hq k (Ioo_subset_Icc_self hs))
    (fun k _ => edgeVel_continuousOn F hseg hq k) (fun j _ => edge_match F hseg hq j) ht

omit [NeZero N] in
theorem polyCurve_zero : polyCurve N sc q 0 = q 0 := by
  unfold polyCurve glue pieceLoc pieceIdx
  simp only [mul_zero, Nat.floor_zero, Nat.zero_min, Nat.cast_zero, sub_zero]
  unfold edgeCurve
  rw [(hseg _ _ (hq ((0 : ℕ) : ZMod N))).2.2.1]
  simp

theorem polyCurve_one : polyCurve N sc q 1 = q 0 := by
  have hN := Nat.pos_of_neZero N
  unfold polyCurve glue pieceLoc
  rw [pieceIdx_one N, natCast_pred hN, mul_one, sub_sub_cancel]
  unfold edgeCurve
  rw [(hseg _ _ (hq ((N - 1 : ℕ) : ZMod N))).2.2.2.1]
  congr 2
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne'), Nat.cast_one, sub_add_cancel,
    ZMod.natCast_self]

omit [NeZero N] in
theorem norm_polyCurve (t : ℝ) : ‖polyCurve N sc q t‖ = 1 :=
  (hseg _ _ (hq _)).2.2.2.2.1 _

theorem polyVel_memLp : MemLp (polyVel N sv q) 2 intervalMeasure := by
  have hN := Nat.pos_of_neZero N
  have hII := glueVel_intervalIntegrable hN (fun k _ => edgeVel_continuousOn F hseg hq k)
  have hmeas : AEStronglyMeasurable (polyVel N sv q) intervalMeasure := by
    have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hII
    exact h.aestronglyMeasurable
  have hb : ∀ k ∈ Finset.range N, ∃ M : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ‖edgeCurve sv q k s‖ ≤ M := by
    intro k _
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (edgeVel_continuousOn F hseg hq k)
    exact ⟨M, hM⟩
  choose! M hM using hb
  set C := ∑ k ∈ Finset.range N, |M k| with hC
  have hbound : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1, ‖edgeCurve sv q k s‖ ≤ C := by
    intro k hk s hs
    have hk' : k ∈ Finset.range N := Finset.mem_range.mpr hk
    calc ‖edgeCurve sv q k s‖ ≤ M k := hM k hk' s hs
      _ ≤ |M k| := le_abs_self _
      _ ≤ C := Finset.single_le_sum (f := fun k => |M k|) (fun _ _ => abs_nonneg _) hk'
  apply MemLp.of_bound hmeas (N * C)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact norm_glueVel_le hN hbound (Ioo_subset_Icc_self ht)

/-- The broken geodesic as an H¹ graph element. -/
def polyLoop : Space n :=
  ofPrimitive (polyCurve_continuousOn F hseg hq) (polyVel_memLp F hseg hq)
    (fun _ ht => polyCurve_eq_add_integral F hseg hq ht)

theorem polyLoop_periodic : polyLoop F hseg hq ∈ periodicSubmodule n :=
  ofPrimitive_periodic _ _ _ ((polyCurve_one F hseg hq).trans (polyCurve_zero F hseg hq).symm)

theorem representative_polyLoop {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (polyLoop F hseg hq) t = polyCurve N sc q t :=
  representative_ofPrimitive _ _ _ ht

theorem value_polyLoop_ae : value (polyLoop F hseg hq) =ᵐ[intervalMeasure] polyCurve N sc q :=
  value_ofPrimitive_ae _ _ _

theorem velocity_polyLoop_ae :
    velocity (polyLoop F hseg hq) =ᵐ[intervalMeasure] polyVel N sv q :=
  velocity_ofPrimitive_ae _ _ _

/-- The energy of the broken geodesic is N Σ e(q_k, q_{k+1}). -/
theorem pathEnergy_polyLoop :
    pathEnergy F (polyLoop F hseg hq) =
      N * ∑ k ∈ Finset.range N, minEnergy F (q k) (q ((k : ZMod N) + 1)) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [pathEnergy_eq_intervalIntegral]
  have hcongr : ∫ t in (0 : ℝ)..1, lagrangian F (continuousRepresentative (polyLoop F hseg hq) t,
      velocity (polyLoop F hseg hq) t) =
      ∫ t in (0 : ℝ)..1, lagrangian F (polyCurve N sc q t, polyVel N sv q t) := by
    apply intervalIntegral.integral_congr_ae
    have h1 : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 1 →
        velocity (polyLoop F hseg hq) t = polyVel N sv q t := by
      have h := velocity_polyLoop_ae F hseg hq
      change ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        velocity (polyLoop F hseg hq) t = polyVel N sv q t at h
      rw [ae_restrict_iff' measurableSet_Ioo] at h
      exact h
    have h2 : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by
      rw [ae_iff]
      simp
    filter_upwards [h1, h2] with t ht1 ht2 ht
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩
    rw [representative_polyLoop F hseg hq (Ioo_subset_Icc_self ht'), ht1 ht']
  rw [hcongr]
  have hpiece := integral_piecewise (F := ℝ) hN
    (f := fun t => lagrangian F (polyCurve N sc q t, polyVel N sv q t))
    (φ := fun k s => lagrangian F (edgeCurve sc q k s, (N : ℝ) • edgeCurve sv q k s))
    (fun k _ s hs => ?_) (fun k hk t ht => ?_)
  · rw [hpiece, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have he := (hseg _ _ (hq k)).2.2.2.2.2
    have hsmul : ∫ s in (0 : ℝ)..1,
        lagrangian F (edgeCurve sc q k s, (N : ℝ) • edgeCurve sv q k s) =
        (N : ℝ) ^ 2 * ∫ s in (0 : ℝ)..1, lagrangian F (edgeCurve sc q k s, edgeCurve sv q k s) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext s
      exact lagrangian_velocity_smul F _ _ _
    rw [hsmul]
    change (N : ℝ)⁻¹ • ((N : ℝ) ^ 2 *
      ∫ s in (0 : ℝ)..1, lagrangian F (sc (q k) (q ((k : ZMod N) + 1)) s,
        sv (q k) (q ((k : ZMod N) + 1)) s)) = _
    rw [he, smul_eq_mul]
    field_simp
  · have hz : (edgeCurve sc q k s) ≠ 0 := by
      intro h0
      have := norm_polyCurve F hseg hq (0 : ℝ)
      have h1 : ‖edgeCurve sc q k s‖ = 1 := (hseg _ _ (hq k)).2.2.2.2.1 s
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have hc1 : ContinuousWithinAt (edgeCurve sc q k) (Icc 0 1) s := edge_continuousOn F hseg hq k s hs
    have hc2 : ContinuousWithinAt (fun s => (N : ℝ) • edgeCurve sv q k s) (Icc 0 1) s :=
      (edgeVel_continuousOn F hseg hq k s hs).const_smul (N : ℝ)
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun x => (edgeCurve sc q k x, (N : ℝ) • edgeCurve sv q k x)) (x := s)
      (lagrangian_continuousAt F (z := (edgeCurve sc q k s, (N : ℝ) • edgeCurve sv q k s)) hz)
      (hc1.prodMk hc2)
  · show lagrangian F (polyCurve N sc q t, polyVel N sv q t) =
      lagrangian F (edgeCurve sc q k ((N : ℝ) * t - k), (N : ℝ) • edgeCurve sv q k ((N : ℝ) * t - k))
    rw [show polyCurve N sc q t = edgeCurve sc q k ((N : ℝ) * t - k) from
        glue_eq_of_mem_Ico hk _ ⟨ht.1.le, ht.2⟩,
      show polyVel N sv q t = (N : ℝ) • edgeCurve sv q k ((N : ℝ) * t - k) from
        glueVel_eq_of_mem_Ico hk _ ⟨ht.1.le, ht.2⟩]

end Loop

theorem shortPolygon_isOpen (δ : ℝ) (N : ℕ) [NeZero N] :
    IsOpen {q : ZMod N → Sphere n | ShortPolygon δ q} := by
  have he : {q : ZMod N → Sphere n | ShortPolygon δ q} =
      ⋂ i : ZMod N, {q : ZMod N → Sphere n | ‖(q (i + 1) : Ambient n) - q i‖ < δ} := by
    ext q
    simp [ShortPolygon]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (continuous_norm.comp ((continuous_subtype_val.comp (continuous_apply _)).sub
    (continuous_subtype_val.comp (continuous_apply _)))) continuous_const

section Continuity

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, lagrangian F (sc P Q t, sv P Q t) = minEnergy F P Q)
  (hunif : ∀ P₀ Q₀ : Sphere n, ‖(Q₀ : Ambient n) - P₀‖ < δ → ∀ ε > 0,
    ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), ∀ t ∈ Icc (0 : ℝ) 1,
      ‖sc x.1 x.2 t - sc P₀ Q₀ t‖ < ε ∧ ‖sv x.1 x.2 t - sv P₀ Q₀ t‖ < ε)
  (N : ℕ) [NeZero N]

open Classical in
/-- The broken geodesic map on all polygons, zero off the short polygons. -/
def brokenGeodesic (q : ZMod N → Sphere n) : Space n :=
  if h : ShortPolygon δ q then polyLoop F hseg h else 0

theorem brokenGeodesic_of_short {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    brokenGeodesic F hseg N q = polyLoop F hseg hq := by
  unfold brokenGeodesic
  simp [hq]

include hunif in
/-- The broken geodesic map is continuous at short polygons. -/
theorem brokenGeodesic_continuousAt {q₀ : ZMod N → Sphere n} (hq₀ : ShortPolygon δ q₀) :
    ContinuousAt (brokenGeodesic F hseg N) q₀ := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hev : ∀ᶠ q in 𝓝 q₀, ShortPolygon δ q := (shortPolygon_isOpen δ N).mem_nhds hq₀
  apply tendsto_of_uniform (c := fun q => polyCurve N sc q) (c' := fun q => polyVel N sv q)
    (c₀ := polyCurve N sc q₀) (c₀' := polyVel N sv q₀)
  · filter_upwards [hev] with q hq
    rw [brokenGeodesic_of_short F hseg N hq]
    exact value_polyLoop_ae F hseg hq
  · filter_upwards [hev] with q hq
    rw [brokenGeodesic_of_short F hseg N hq]
    exact velocity_polyLoop_ae F hseg hq
  · rw [brokenGeodesic_of_short F hseg N hq₀]
    exact value_polyLoop_ae F hseg hq₀
  · rw [brokenGeodesic_of_short F hseg N hq₀]
    exact velocity_polyLoop_ae F hseg hq₀
  · intro ε hε
    set ε' := ε / ((N : ℝ) + 1) with hε'def
    have hε' : 0 < ε' := by positivity
    have hle1 : ε' ≤ ε := by
      rw [hε'def, div_le_iff₀ (by positivity)]
      nlinarith
    have hle2 : (N : ℝ) * ε' ≤ ε := by
      rw [hε'def, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    have hedge : ∀ k ∈ Finset.range N, ∀ᶠ q in 𝓝 q₀, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖edgeCurve sc q k t - edgeCurve sc q₀ k t‖ < ε' ∧
        ‖edgeCurve sv q k t - edgeCurve sv q₀ k t‖ < ε' := by
      intro k _
      have h := hunif _ _ (hq₀ k) ε' hε'
      have hcont : ContinuousAt (fun q : ZMod N → Sphere n => (q k, q ((k : ZMod N) + 1))) q₀ :=
        ((continuous_apply _).prodMk (continuous_apply _)).continuousAt
      exact hcont.tendsto.eventually h
    rw [← Filter.eventually_all_finset] at hedge
    filter_upwards [hedge] with q hq t ht
    have h1 : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1, ‖edgeCurve sc q k s - edgeCurve sc q₀ k s‖ ≤ ε' :=
      fun k hk s hs => (hq k (Finset.mem_range.mpr hk) s hs).1.le
    have h2 : ∀ k < N, ∀ s ∈ Icc (0 : ℝ) 1, ‖edgeCurve sv q k s - edgeCurve sv q₀ k s‖ ≤ ε' :=
      fun k hk s hs => (hq k (Finset.mem_range.mpr hk) s hs).2.le
    have ht' := Ioo_subset_Icc_self ht
    exact ⟨(norm_glue_sub_le hN h1 ht').trans hle1, (norm_glueVel_sub_le hN h2 ht').trans hle2⟩

end Continuity

section Rotation

open Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, lagrangian F (sc P Q t, sv P Q t) = minEnergy F P Q)
  {N : ℕ} [NeZero N]

/-- The broken geodesic as a sphere loop. -/
def polySphereLoop {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) : SphereLoop n :=
  ⟨⟨polyLoop F hseg hq, polyLoop_periodic F hseg hq⟩, fun t => by
    change ‖continuousRepresentative (polyLoop F hseg hq) t‖ = 1
    rw [representative_polyLoop F hseg hq t.2]
    exact norm_polyCurve F hseg hq t⟩

/-- Rotation of the vertices. -/
def rotatePolygon (q : ZMod N → Sphere n) : ZMod N → Sphere n := fun i => q (i + 1)

omit [NeZero N] in
theorem shortPolygon_rotate {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    ShortPolygon δ (rotatePolygon q) := fun i => by
  unfold rotatePolygon
  rw [add_assoc, add_comm (1 : ZMod N) 1, ← add_assoc]
  exact hq (i + 1)

omit [NeZero N] in
theorem edgeCurve_rotate (c : Sphere n → Sphere n → ℝ → Ambient n) (q : ZMod N → Sphere n)
    (k : ℕ) : edgeCurve c (rotatePolygon q) k = edgeCurve c q (k + 1) := by
  unfold edgeCurve rotatePolygon
  push_cast
  rfl

/-- On [0,1] the rotated broken geodesic is the broken geodesic shifted by 1/N. -/
theorem realMap_rotate_of_mem {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    realMap (polySphereLoop F hseg (shortPolygon_rotate hq)).data t =
      realMap (polySphereLoop F hseg hq).data (t + 1 / N) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk := pieceIdx_lt hN t
  have hpiece := mem_piece hN ht
  set k := pieceIdx N t with hkdef
  have hL : realMap (polySphereLoop F hseg (shortPolygon_rotate hq)).data t =
      edgeCurve sc q (k + 1) ((N : ℝ) * t - k) := by
    rw [realMap_eqOn _ ht]
    change continuousRepresentative (polyLoop F hseg (shortPolygon_rotate hq)) t = _
    rw [representative_polyLoop F hseg _ ht]
    unfold polyCurve
    rw [glue_eq_of_mem_Icc hk (fun j _ => edge_match F hseg (shortPolygon_rotate hq) j) hpiece,
      edgeCurve_rotate]
  rw [hL]
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk1 | hk1
  · have hs : t + 1 / N ∈ Icc (((k + 1 : ℕ) : ℝ) / N) ((((k + 1 : ℕ) : ℝ) + 1) / N) := by
      push_cast
      constructor
      · have := hpiece.1
        rw [add_div]
        linarith
      · have := hpiece.2
        rw [add_div]
        linarith
    have hs01 : t + 1 / N ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have := ht.1
        positivity
      · have := hs.2
        have hle : ((((k + 1 : ℕ) : ℝ) + 1) / N) ≤ 1 := by
          rw [div_le_one hN']
          have : (k + 1 + 1 : ℕ) ≤ N := hk1
          exact_mod_cast this
        linarith
    rw [realMap_eqOn _ hs01]
    change _ = continuousRepresentative (polyLoop F hseg hq) (t + 1 / N)
    rw [representative_polyLoop F hseg hq hs01]
    unfold polyCurve
    rw [glue_eq_of_mem_Icc hk1 (fun j _ => edge_match F hseg hq j) hs]
    congr 1
    push_cast
    field_simp
    ring
  · have hkN : k = N - 1 := by omega
    have hs : t + 1 / N - 1 ∈ Icc (((0 : ℕ) : ℝ) / N) ((((0 : ℕ) : ℝ) + 1) / N) := by
      have h1 := hpiece.1
      have hkR : (k : ℝ) + 1 = N := by exact_mod_cast hk1
      push_cast
      constructor
      · rw [zero_div]
        have : (k : ℝ) / N = 1 - 1 / N := by
          rw [eq_sub_iff_add_eq, ← add_div, hkR, div_self hN'.ne']
        linarith
      · rw [zero_add]
        linarith [ht.2]
    have hs01 : t + 1 / N - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have := hs.1
        simpa using this
      · have := hs.2
        have : (((0 : ℕ) : ℝ) + 1) / N ≤ 1 := by
          push_cast
          rw [zero_add, div_le_one hN']
          exact_mod_cast hN
        linarith
    have hper : realMap (polySphereLoop F hseg hq).data (t + 1 / N) =
        realMap (polySphereLoop F hseg hq).data (t + 1 / N - 1) := by
      have h := realMap_periodic (polySphereLoop F hseg hq).data (t + 1 / N - 1)
      rw [sub_add_cancel] at h
      exact h
    rw [hper, realMap_eqOn _ hs01]
    change _ = continuousRepresentative (polyLoop F hseg hq) (t + 1 / N - 1)
    rw [representative_polyLoop F hseg hq hs01]
    unfold polyCurve
    rw [glue_eq_of_mem_Icc hN (fun j _ => edge_match F hseg hq j) hs]
    have hedge : edgeCurve sc q (k + 1) = edgeCurve sc q 0 := by
      have hz : ((k + 1 : ℕ) : ZMod N) = 0 := by
        rw [show k + 1 = N from hk1]
        exact ZMod.natCast_self N
      unfold edgeCurve
      rw [hz]
      simp
    rw [hedge]
    congr 1
    have hkR : (k : ℝ) + 1 = N := by exact_mod_cast hk1
    push_cast
    field_simp
    linarith

/-- The rotated broken geodesic is the broken geodesic shifted by 1/N, everywhere on ℝ. -/
theorem realMap_rotate {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (t : ℝ) :
    realMap (polySphereLoop F hseg (shortPolygon_rotate hq)).data t =
      realMap (polySphereLoop F hseg hq).data (t + 1 / N) := by
  set g : ℝ → Ambient n := fun t =>
    realMap (polySphereLoop F hseg (shortPolygon_rotate hq)).data t -
      realMap (polySphereLoop F hseg hq).data (t + 1 / N) with hg
  have hgp : Function.Periodic g 1 := by
    intro s
    simp only [hg]
    rw [realMap_periodic, show s + 1 + 1 / N = (s + 1 / N) + 1 by ring, realMap_periodic]
  obtain ⟨y, hy, hgy⟩ := hgp.exists_mem_Ico₀ one_pos t
  have h0 : g y = 0 := by
    simp only [hg]
    rw [realMap_rotate_of_mem F hseg hq (Ico_subset_Icc_self hy), sub_self]
  have h1 : g t = 0 := hgy.trans h0
  simp only [hg] at h1
  exact sub_eq_zero.mp h1

/-- Rotating the vertices rotates the broken geodesic by 1/N. -/
theorem polySphereLoop_rotate {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    polySphereLoop F hseg (shortPolygon_rotate hq) =
      ((1 / N : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ polySphereLoop F hseg hq := by
  apply sphereCircleMap_injective n
  apply ContinuousMap.ext
  intro x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [sphereCircleMap_vadd]
  apply Subtype.ext
  rw [sphereCircleMap_val, sphereCircleMap_val]
  have h := realMap_rotate F hseg hq t
  rw [realMap_apply, realMap_apply] at h
  rw [show ((1 / N : ℝ) : SobolevCircleRepresentative.Circle) +
      (t : SobolevCircleRepresentative.Circle) =
      ((t + 1 / N : ℝ) : SobolevCircleRepresentative.Circle) by
    rw [add_comm]; rfl]
  exact h


end Rotation

/-- Reversal of the vertices. -/
def reversePolygon {N : ℕ} (q : ZMod N → Sphere n) : ZMod N → Sphere n := fun i => q (-i)

theorem shortPolygon_reverse {δ : ℝ} {N : ℕ} {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    ShortPolygon δ (reversePolygon q) := fun i => by
  unfold reversePolygon
  have h := hq (-(i + 1))
  rw [show -(i + 1) + 1 = -i by ring] at h
  rw [norm_sub_rev]
  exact h

theorem natCast_rev {N k : ℕ} (hk : k < N) :
    ((N - 1 - k : ℕ) : ZMod N) = -((k : ZMod N) + 1) := by
  have h1 : N - 1 - k = N - (k + 1) := by omega
  rw [h1, Nat.cast_sub (by omega : k + 1 ≤ N), ZMod.natCast_self]
  push_cast
  ring

section Reversal

open Finsler.SobolevReverse Finsler.SobolevEnergy

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, lagrangian F (sc P Q t, sv P Q t) = minEnergy F P Q)
  (hrev : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
    sc Q P s = sc P Q (1 - s))
  {N : ℕ} [NeZero N]

omit [NeZero N] in
include hrev in
theorem edgeCurve_reverse {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) {k : ℕ} (hk : k < N)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    edgeCurve sc (reversePolygon q) k s = edgeCurve sc q (N - 1 - k) (1 - s) := by
  unfold edgeCurve reversePolygon
  rw [natCast_rev hk, show -((k : ZMod N) + 1) + 1 = -(k : ZMod N) by ring]
  have h := hq (-((k : ZMod N) + 1))
  rw [show -((k : ZMod N) + 1) + 1 = -(k : ZMod N) by ring] at h
  exact hrev _ _ h s hs

include hseg hrev in
/-- The reversed polygon's broken geodesic is the reversed broken geodesic, as curves. -/
theorem polyCurve_reverse {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    polyCurve N sc (reversePolygon q) t = polyCurve N sc q (1 - t) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk := pieceIdx_lt hN t
  have hpiece := mem_piece hN ht
  set k := pieceIdx N t with hkdef
  have hloc : (N : ℝ) * t - k ∈ Icc (0 : ℝ) 1 := by
    have h1 := hpiece.1
    have h2 := hpiece.2
    rw [div_le_iff₀ hN'] at h1
    rw [le_div_iff₀ hN'] at h2
    constructor <;> linarith
  unfold polyCurve
  rw [glue_eq_of_mem_Icc hk (fun j _ => edge_match F hseg (shortPolygon_reverse hq) j) hpiece,
    edgeCurve_reverse hrev hq hk hloc]
  have hj : N - 1 - k < N := by omega
  have hcast : ((N - 1 - k : ℕ) : ℝ) = N - 1 - k := by
    rw [Nat.cast_sub (by omega : k ≤ N - 1), natCast_pred hN]
  have hmem : 1 - t ∈ Icc (((N - 1 - k : ℕ) : ℝ) / N) ((((N - 1 - k : ℕ) : ℝ) + 1) / N) := by
    rw [hcast]
    have h1 := hpiece.1
    have h2 := hpiece.2
    rw [div_le_iff₀ hN'] at h1
    rw [le_div_iff₀ hN'] at h2
    constructor
    · rw [div_le_iff₀ hN']
      nlinarith
    · rw [le_div_iff₀ hN']
      nlinarith
  rw [glue_eq_of_mem_Icc hj (fun j _ => edge_match F hseg hq j) hmem, hcast]
  congr 1
  ring

include hseg hrev in
/-- Reversing the vertices reverses the broken geodesic. -/
theorem polySphereLoop_reverse {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) :
    polySphereLoop F hseg (shortPolygon_reverse hq) = reverseSphere (polySphereLoop F hseg hq) := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_reverseSphere]
  apply Subtype.ext
  change continuousRepresentative (polyLoop F hseg (shortPolygon_reverse hq)) t =
    continuousRepresentative (polyLoop F hseg hq) (reflectionInterval t)
  rw [representative_polyLoop F hseg _ t.2,
    representative_polyLoop F hseg hq (reflectionInterval t).2]
  exact polyCurve_reverse F hseg hrev hq t.2

end Reversal

end

end Finsler.PolygonLoop
