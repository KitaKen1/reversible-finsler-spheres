module

public import Finsler.Analysis.QuadraticHomogeneous
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Joint C¹ regularity of a velocity-quadratic density across its zero section.
All smoothness assumptions are restricted to nonzero velocities. Bounds on a
compact base set times the unit velocity sphere control the actual full
derivative, not just the derivative of a fixed fiber. -/

@[expose] public section

namespace Finsler.ParametricQuadratic

open Filter Asymptotics Function Metric
open scoped Topology ContDiff

noncomputable section

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : B × V → ℝ} {U K : Set B}

def velocityScale (r : ℝ) : B × V →L[ℝ] B × V :=
  (ContinuousLinearMap.fst ℝ B V).prod (r • ContinuousLinearMap.snd ℝ B V)

theorem velocityScale_apply (r : ℝ) (z : B × V) :
    velocityScale r z = (z.1, r • z.2) := rfl

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
theorem zero_of_homogeneous
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v)) (x : B) :
    f (x, 0) = 0 := by
  simpa using hh x 0 0

theorem differential_scale_apply
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    {x : B} (hx : x ∈ U) {v : V} (hv : v ≠ 0) (r : ℝ) (hr : r ≠ 0)
    (a : B × V) :
    fderiv ℝ f (x, r • v) a = r ^ 2 * fderiv ℝ f (x, v) (a.1, r⁻¹ • a.2) := by
  have hrv : r • v ≠ 0 := smul_ne_zero hr hv
  have hl := ((hs (x, r • v) hx hrv).differentiableAt (by simp)).hasFDerivAt.comp
    (x, v) (velocityScale r).hasFDerivAt
  have he : (f ∘ velocityScale r) = r ^ 2 • f := by
    funext z
    simpa only [comp_apply, velocityScale_apply, Pi.smul_apply, smul_eq_mul] using hh z.1 r z.2
  rw [he] at hl
  have h := hl.unique (((hs (x, v) hx hv).differentiableAt (by simp)).hasFDerivAt.const_smul (r ^ 2))
  have ha := congrArg (fun L : B × V →L[ℝ] ℝ => L (a.1, r⁻¹ • a.2)) h
  simpa only [ContinuousLinearMap.comp_apply, velocityScale_apply, smul_smul,
    mul_inv_cancel₀ hr, one_smul, Prod.mk.eta, smul_apply, smul_eq_mul] using ha

theorem exists_unit_bounds [FiniteDimensional ℝ V] (hK : IsCompact K)
    (hKU : K ⊆ U)
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K ×ˢ Metric.sphere (0 : V) 1,
      ‖f z‖ ≤ C ∧ ‖fderiv ℝ f z‖ ≤ C := by
  have hc : ContinuousOn (fun z : B × V => ‖f z‖ + ‖fderiv ℝ f z‖)
      (K ×ˢ Metric.sphere (0 : V) 1) := by
    intro z hz
    have hv : z.2 ≠ 0 := by
      intro he
      simp [he] at hz
    have hh := hs z (hKU hz.1) hv
    exact (hh.continuousAt.norm.add (hh.continuousAt_fderiv (by simp)).norm).continuousWithinAt
  obtain ⟨C, hb⟩ := (hK.prod (isCompact_sphere (0 : V) 1)).bddAbove_image hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro z hz
  have h := (hb ⟨z, hz, rfl⟩).trans (le_max_left C 1)
  constructor <;> nlinarith [norm_nonneg (f z), norm_nonneg (fderiv ℝ f z)]

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
theorem quadratic_bound_on_compact
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ z ∈ K ×ˢ Metric.sphere (0 : V) 1, ‖f z‖ ≤ C)
    {x : B} (hx : x ∈ K) (v : V) : ‖f (x, v)‖ ≤ C * ‖v‖ ^ 2 := by
  by_cases hv : v = 0
  · simp [hv, zero_of_homogeneous hh]
  · have hn := norm_ne_zero_iff.mpr hv
    let w : V := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.sphere (0 : V) 1 := by
      simp [w, norm_smul, inv_mul_cancel₀ hn]
    have he : ‖v‖ • w = v := by simp [w, smul_smul, mul_inv_cancel₀ hn]
    calc
      ‖f (x, v)‖ = ‖v‖ ^ 2 * ‖f (x, w)‖ := by
        have hfv := hh x ‖v‖ w
        rw [he] at hfv
        rw [hfv, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ‖v‖ ^ 2 * C := mul_le_mul_of_nonneg_left (hb (x, w) ⟨hx, hw⟩) (sq_nonneg _)
      _ = C * ‖v‖ ^ 2 := mul_comm _ _

theorem differential_bound_on_compact
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    (hKU : K ⊆ U) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z ∈ K ×ˢ Metric.sphere (0 : V) 1, ‖fderiv ℝ f z‖ ≤ C)
    {x : B} (hx : x ∈ K) {v : V} (hv : v ≠ 0) :
    ‖fderiv ℝ f (x, v)‖ ≤ C * (‖v‖ ^ 2 + ‖v‖) := by
  have hn := norm_ne_zero_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : V) 1 := by simp [w, norm_smul, inv_mul_cancel₀ hn]
  have hw' : w ≠ 0 := by intro he; simp [he] at hw
  have he : ‖v‖ • w = v := by simp [w, smul_smul, mul_inv_cancel₀ hn]
  apply (fderiv ℝ f (x, v)).opNorm_le_bound (mul_nonneg hC (by positivity))
  intro a
  have ha1 : ‖a.1‖ ≤ ‖a‖ := le_max_left _ _
  have ha2 : ‖a.2‖ ≤ ‖a‖ := le_max_right _ _
  have ha : ‖(a.1, ‖v‖⁻¹ • a.2)‖ ≤ (1 + ‖v‖⁻¹) * ‖a‖ := by
    change max ‖a.1‖ ‖‖v‖⁻¹ • a.2‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    apply max_le
    · nlinarith [inv_nonneg.mpr (norm_nonneg v), norm_nonneg a]
    · have hmul := mul_le_mul_of_nonneg_left ha2 (inv_nonneg.mpr (norm_nonneg v))
      nlinarith [norm_nonneg a]
  have hd := differential_scale_apply hh hs (hKU hx) hw' ‖v‖ hn a
  rw [he] at hd
  calc
    ‖fderiv ℝ f (x, v) a‖ = ‖v‖ ^ 2 * ‖fderiv ℝ f (x, w) (a.1, ‖v‖⁻¹ • a.2)‖ := by
      rw [hd, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ‖v‖ ^ 2 * (C * ‖(a.1, ‖v‖⁻¹ • a.2)‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact ((fderiv ℝ f (x, w)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hb (x, w) ⟨hx, hw⟩) (norm_nonneg _))
    _ ≤ ‖v‖ ^ 2 * (C * ((1 + ‖v‖⁻¹) * ‖a‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha hC) (sq_nonneg _)
    _ = (C * (‖v‖ ^ 2 + ‖v‖)) * ‖a‖ := by field_simp [hn]

theorem exists_local_bounds [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
    (hU : IsOpen U)
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    {x : B} (hx : x ∈ U) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ closedBall x ε ⊆ U ∧
      (∀ y ∈ closedBall x ε, ∀ v : V, ‖f (y, v)‖ ≤ C * ‖v‖ ^ 2) ∧
      (∀ y ∈ closedBall x ε, ∀ v : V, v ≠ 0 →
        ‖fderiv ℝ f (y, v)‖ ≤ C * (‖v‖ ^ 2 + ‖v‖)) := by
  obtain ⟨ε, he, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC, hb⟩ := exists_unit_bounds (isCompact_closedBall x ε) hsub hs
  refine ⟨ε, C, he, hC, hsub, ?_, ?_⟩
  · intro y hy v
    exact quadratic_bound_on_compact hh hC.le (fun z hz => (hb z hz).1) hy v
  · intro y hy v hv
    exact differential_bound_on_compact hh hs hsub hC.le
      (fun z hz => (hb z hz).2) hy hv

theorem partial_differential_bounds_on_compact
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    (hKU : K ⊆ U) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z ∈ K ×ˢ Metric.sphere (0 : V) 1, ‖fderiv ℝ f z‖ ≤ C)
    {x : B} (hx : x ∈ K) {v : V} (hv : v ≠ 0) :
    ‖(fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inl ℝ B V)‖ ≤ C * ‖v‖ ^ 2 ∧
    ‖(fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inr ℝ B V)‖ ≤ C * ‖v‖ := by
  have hn := norm_ne_zero_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : V) 1 := by simp [w, norm_smul, inv_mul_cancel₀ hn]
  have hw' : w ≠ 0 := by intro he; simp [he] at hw
  have he : ‖v‖ • w = v := by simp [w, smul_smul, mul_inv_cancel₀ hn]
  have hb' (a : B × V) : ‖fderiv ℝ f (x, w) a‖ ≤ C * ‖a‖ :=
    ((fderiv ℝ f (x, w)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hb (x, w) ⟨hx, hw⟩) (norm_nonneg a))
  constructor
  · apply ((fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inl ℝ B V)).opNorm_le_bound
      (mul_nonneg hC (sq_nonneg _))
    intro a
    have hd := differential_scale_apply hh hs (hKU hx) hw' ‖v‖ hn (a, 0)
    rw [he] at hd
    change ‖fderiv ℝ f (x, v) (a, 0)‖ ≤ _
    rw [hd, smul_zero, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖v‖ ^ 2 * (C * ‖(a, (0 : V))‖) :=
        mul_le_mul_of_nonneg_left (hb' (a, 0)) (sq_nonneg _)
      _ = (C * ‖v‖ ^ 2) * ‖a‖ := by simp [Prod.norm_def]; ring
  · apply ((fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inr ℝ B V)).opNorm_le_bound
      (mul_nonneg hC (norm_nonneg _))
    intro a
    have hd := differential_scale_apply hh hs (hKU hx) hw' ‖v‖ hn (0, a)
    rw [he] at hd
    change ‖fderiv ℝ f (x, v) (0, a)‖ ≤ _
    rw [hd, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖v‖ ^ 2 * (C * ‖((0 : B), ‖v‖⁻¹ • a)‖) :=
        mul_le_mul_of_nonneg_left (hb' (0, ‖v‖⁻¹ • a)) (sq_nonneg _)
      _ = (C * ‖v‖) * ‖a‖ := by
        simp only [Prod.norm_def, norm_zero, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
        rw [max_eq_right (mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) (norm_nonneg a))]
        field_simp [hn]

theorem hasFDerivAt_zero [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
    (hU : IsOpen U)
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    {x : B} (hx : x ∈ U) :
    HasFDerivAt f (0 : B × V →L[ℝ] ℝ) (x, 0) := by
  obtain ⟨ε, C, he, hC, _, hb, _⟩ := exists_local_bounds hU hh hs hx
  have hbase : ∀ᶠ z : B × V in 𝓝 (x, 0), z.1 ∈ closedBall x ε :=
    continuous_fst.continuousAt.preimage_mem_nhds (closedBall_mem_nhds x he)
  have hbig : f =O[𝓝 (x, 0)] (fun z : B × V => ‖z - (x, 0)‖ ^ 2) := by
    apply IsBigO.of_bound C
    filter_upwards [hbase] with z hz
    have hv : ‖z.2‖ ≤ ‖z - (x, 0)‖ := by
      change ‖z.2‖ ≤ max ‖z.1 - x‖ ‖z.2 - (0 : V)‖
      simpa only [sub_zero] using (le_max_right ‖z.1 - x‖ ‖z.2‖)
    rw [Real.norm_of_nonneg (sq_nonneg ‖z - (x, 0)‖)]
    exact (hb z.1 hz z.2).trans (mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hv) hC.le)
  have ht : Tendsto (fun z : B × V => z - (x, 0)) (𝓝 (x, 0)) (𝓝 0) := by
    have hc : Continuous (fun z : B × V => z - (x, 0)) := continuous_id.sub continuous_const
    simpa using (hc.continuousAt (x := (x, (0 : V)))).tendsto
  have hlittle : f =o[𝓝 (x, 0)] (fun z : B × V => z - (x, 0)) :=
    hbig.trans_isLittleO ((isLittleO_norm_pow_id (by norm_num : 1 < 2)).comp_tendsto ht)
  apply HasFDerivAt.of_isLittleO
  simpa only [zero_of_homogeneous hh, zero_apply, sub_zero] using hlittle

theorem hasFDerivAt [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
    (hU : IsOpen U)
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    {z : B × V} (hz : z.1 ∈ U) : HasFDerivAt f (fderiv ℝ f z) z := by
  by_cases hv : z.2 = 0
  · have he : z = (z.1, 0) := Prod.ext rfl hv
    rw [he]
    exact (hasFDerivAt_zero hU hh hs hz).differentiableAt.hasFDerivAt
  · exact ((hs z hz hv).differentiableAt (by simp)).hasFDerivAt

theorem continuousAt_fderiv_zero [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
    (hU : IsOpen U)
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    {x : B} (hx : x ∈ U) : ContinuousAt (fderiv ℝ f) (x, 0) := by
  obtain ⟨ε, C, he, _, hsub, _, hb⟩ := exists_local_bounds hU hh hs hx
  change Tendsto (fderiv ℝ f) (𝓝 (x, 0)) (𝓝 (fderiv ℝ f (x, 0)))
  rw [(hasFDerivAt_zero hU hh hs hx).fderiv, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun z : B × V => C * (‖z.2‖ ^ 2 + ‖z.2‖))
    (Eventually.of_forall fun z => norm_nonneg (fderiv ℝ f z))
  · have hbase : ∀ᶠ z : B × V in 𝓝 (x, 0), z.1 ∈ closedBall x ε :=
      continuous_fst.continuousAt.preimage_mem_nhds (closedBall_mem_nhds x he)
    filter_upwards [hbase] with z hz
    by_cases hv : z.2 = 0
    · have hez : z = (z.1, 0) := Prod.ext rfl hv
      rw [hez, (hasFDerivAt_zero hU hh hs (hsub hz)).fderiv]
      simp
    · exact hb z.1 hz z.2 hv
  · have hc : Continuous (fun z : B × V => C * (‖z.2‖ ^ 2 + ‖z.2‖)) :=
      continuous_const.mul ((continuous_snd.norm.pow 2).add continuous_snd.norm)
    simpa using (hc.continuousAt (x := (x, (0 : V)))).tendsto

theorem contDiffAt_one [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
    (hU : IsOpen U)
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    {z : B × V} (hz : z.1 ∈ U) : ContDiffAt ℝ 1 f z := by
  have ho : IsOpen (Prod.fst ⁻¹' U : Set (B × V)) := hU.preimage continuous_fst
  refine contDiffAt_one_iff.mpr ⟨fderiv ℝ f, Prod.fst ⁻¹' U, ho.mem_nhds hz, ?_, ?_⟩
  · intro y hy
    by_cases hv : y.2 = 0
    · have he : y = (y.1, 0) := Prod.ext rfl hv
      rw [he]
      exact (continuousAt_fderiv_zero hU hh hs hy).continuousWithinAt
    · exact ((hs y hy hv).continuousAt_fderiv (by simp)).continuousWithinAt
  · intro y hy
    exact hasFDerivAt hU hh hs hy

theorem exists_local_partial_bounds [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
    (hU : IsOpen U)
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hs : ∀ z : B × V, z.1 ∈ U → z.2 ≠ 0 → ContDiffAt ℝ ∞ f z)
    {x : B} (hx : x ∈ U) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ closedBall x ε ⊆ U ∧
      ∀ y ∈ closedBall x ε, ∀ v : V,
        ‖(fderiv ℝ f (y, v)).comp (ContinuousLinearMap.inl ℝ B V)‖ ≤ C * ‖v‖ ^ 2 ∧
        ‖(fderiv ℝ f (y, v)).comp (ContinuousLinearMap.inr ℝ B V)‖ ≤ C * ‖v‖ := by
  obtain ⟨ε, he, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC, hb⟩ := exists_unit_bounds (isCompact_closedBall x ε) hsub hs
  refine ⟨ε, C, he, hC, hsub, ?_⟩
  intro y hy v
  by_cases hv : v = 0
  · rw [hv, (hasFDerivAt_zero hU hh hs (hsub hy)).fderiv]
    simp
  · exact partial_differential_bounds_on_compact hh hs hsub hC.le
      (fun z hz => (hb z hz).2) hy hv

end

end Finsler.ParametricQuadratic
