module

public import Finsler.Geometry.AmbientHessian
public import Finsler.Geometry.AmbientCalibrator
public import Finsler.Algebra.KernelComparison

/-! The nullity of the penalized polygon energy at a stationary sphere polygon. A vector which
is annihilated by the derivative of the radial projection at a unit vector is a multiple of that
vector; hence the kernel of the derivative of the Hilbert coordinates of the normalization at a
sphere polygon consists of the radial vectors, with vertices c_j q_j. Along such a vector the
polygon energy with normalized vertices is constant and the penalty is the sum of the squares of
log(1 + t c_j), so the second derivative of the penalized energy there is 2 λ Σ c_j², positive
for λ > 0. The derivative of the inverse coordinate map is a section of the derivative of the
coordinates of the normalization. By the comparison of the kernels of two symmetric bilinear
functions related by a section and a retraction, the kernel of the second derivative of the
penalized energy at a short stationary sphere polygon without zero edges has the dimension of
the kernel of the Hessian in Hilbert coordinates: the nullity of the polygon. -/

@[expose] public section

namespace Finsler.AmbientNullity

open Module Filter
open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonChart
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.IndexComparison
open Finsler.AmbientPenalty Finsler.AmbientDescent Finsler.AmbientEnergyRegularity
open Finsler.SphereCoordinateEuler Finsler.PolygonEnergyGlobal Finsler.AmbientHessian
open Finsler.AmbientCalibrator Finsler.KernelComparison
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section
set_option maxSynthPendingDepth 3

/-! ### The kernel of the derivative of the radial projection -/

section Radial

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- A vector annihilated by the derivative of the radial projection at a unit vector is a
multiple of that vector. -/
theorem exists_smul_of_fderiv_radial {p : G} (hp : ‖p‖ = 1) {w : G}
    (h : fderiv ℝ (fun Q : G => ‖Q‖⁻¹ • Q) p w = 0) : ∃ c : ℝ, w = c • p := by
  have hp0 : p ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hp
    exact zero_ne_one hp
  have hnorm : HasFDerivAt (fun Q : G => ‖Q‖) (fderiv ℝ (fun Q : G => ‖Q‖) p) p :=
    ((contDiffAt_norm (n := 1) ℝ hp0).differentiableAt (by norm_num)).hasFDerivAt
  have hinv : HasFDerivAt (fun Q : G => ‖Q‖⁻¹)
      ((-(‖p‖ ^ 2)⁻¹) • fderiv ℝ (fun Q : G => ‖Q‖) p) p :=
    (hasDerivAt_inv (norm_ne_zero_iff.mpr hp0)).comp_hasFDerivAt p hnorm
  have hD := hinv.smul (hasFDerivAt_id p)
  have hfd : fderiv ℝ (fun Q : G => ‖Q‖⁻¹ • Q) p =
      ‖p‖⁻¹ • ContinuousLinearMap.id ℝ G +
        ((-(‖p‖ ^ 2)⁻¹) • fderiv ℝ (fun Q : G => ‖Q‖) p).smulRight (id p) := hD.fderiv
  rw [hfd] at h
  refine ⟨-(((-(‖p‖ ^ 2)⁻¹) • fderiv ℝ (fun Q : G => ‖Q‖) p) w), ?_⟩
  have h2 : ‖p‖⁻¹ • w + (((-(‖p‖ ^ 2)⁻¹) • fderiv ℝ (fun Q : G => ‖Q‖) p) w) • p = 0 := h
  have h3 : ‖p‖⁻¹ • w = w := by rw [hp, inv_one, one_smul]
  rw [h3] at h2
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h2

end Radial

variable {n : ℕ}

/-- A vector annihilated by the derivative of the coordinates of the normalization at a sphere
point is a multiple of the point. -/
theorem exists_smul_of_fderiv_chartNormalize (p : Sphere n) {w : Ambient n}
    (h : fderiv ℝ (chartNormalize p) (p : Ambient n) w = 0) :
    ∃ c : ℝ, w = c • (p : Ambient n) := by
  have hp0 : (p : Ambient n) ≠ 0 := fun h0 => by
    have h1 := norm_coe p
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hs : SphereRetraction.normalize (p : Ambient n) ∈ (extChartAt (𝓡 n) p).source := by
    rw [normalize_inclusion]
    exact mem_extChartAt_source p
  have hev : (fun Q : Ambient n => inverseAmbient p (chartNormalize p Q)) =ᶠ[𝓝 (p : Ambient n)]
      fun Q => ‖Q‖⁻¹ • Q := by
    have h1 : ∀ᶠ Q : Ambient n in 𝓝 (p : Ambient n), Q ≠ 0 :=
      isOpen_ne.mem_nhds hp0
    have h2 : ∀ᶠ Q : Ambient n in 𝓝 (p : Ambient n),
        SphereRetraction.normalize Q ∈ (extChartAt (𝓡 n) p).source :=
      (normalize_smoothAt hp0).continuousAt.eventually
        ((isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds hs)
    filter_upwards [h1, h2] with Q hQ0 hQs
    unfold chartNormalize inverseAmbient inverseSphere
    rw [(extChartAt (𝓡 n) p).left_inv hQs, coe_normalize hQ0]
  have hc : HasFDerivAt (chartNormalize p) (fderiv ℝ (chartNormalize p) (p : Ambient n))
      (p : Ambient n) :=
    ((chartNormalize_smoothAt p hp0 hs).differentiableAt (by simp)).hasFDerivAt
  have hi : HasFDerivAt (inverseAmbient p)
      (fderiv ℝ (inverseAmbient p) (chartNormalize p (p : Ambient n)))
      (chartNormalize p (p : Ambient n)) :=
    ((inverseAmbient_smoothAt p (chartNormalize_mem_target p hs)).differentiableAt
      (by simp)).hasFDerivAt
  have hcomp := hi.comp (p : Ambient n) hc
  have hfd : fderiv ℝ (fun Q : Ambient n => ‖Q‖⁻¹ • Q) (p : Ambient n) =
      (fderiv ℝ (inverseAmbient p) (chartNormalize p (p : Ambient n))).comp
        (fderiv ℝ (chartNormalize p) (p : Ambient n)) := by
    rw [← hev.fderiv_eq]
    exact hcomp.fderiv
  apply exists_smul_of_fderiv_radial (norm_coe p)
  rw [hfd, ContinuousLinearMap.comp_apply, h, map_zero]

variable {N : ℕ} [NeZero N]

/-- The components of the derivative of the coordinates of the normalization of a polygon. -/
theorem fderiv_chartN_apply (q : ZMod N → Sphere n) (u : ZMod N → Ambient n) (i : ZMod N) :
    (fderiv ℝ (chartN q) (amb q) u) i = fderiv ℝ (chartNormalize (q i)) (amb q i) (u i) := by
  have hs : SphereRetraction.normalize (amb q i) ∈ (extChartAt (𝓡 n) (q i)).source := by
    rw [show amb q i = (q i : Ambient n) from rfl, normalize_inclusion]
    exact mem_extChartAt_source (q i)
  have hci : HasFDerivAt (chartNormalize (q i)) (fderiv ℝ (chartNormalize (q i)) (amb q i))
      (amb q i) :=
    ((chartNormalize_smoothAt (q i) (amb_ne_zero q i) hs).differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun Q : ZMod N → Ambient n => chartNormalize (q i) (Q i))
      ((fderiv ℝ (chartNormalize (q i)) (amb q i)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod N => Ambient n) i)) (amb q) :=
    HasFDerivAt.comp (g := chartNormalize (q i)) (f := fun Q : ZMod N → Ambient n => Q i)
      (amb q) hci (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ZMod N => Ambient n)
        i).hasFDerivAt
  have hρ : HasFDerivAt (chartN q) (fderiv ℝ (chartN q) (amb q)) (amb q) :=
    ((chartN_contDiffAt q).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasFDerivAt (fun Q : ZMod N → Ambient n => (chartN q Q) i)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ZMod N => Coordinates n) i).comp
        (fderiv ℝ (chartN q) (amb q))) (amb q) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ZMod N => Coordinates n) i).hasFDerivAt.comp (amb q) hρ
  have h3 := h1.unique h2
  exact (congrArg (fun L : (ZMod N → Ambient n) →L[ℝ] Coordinates n => L u) h3).symm

/-- The kernel of the derivative of the coordinates of the normalization at a sphere polygon
consists of the radial vectors. -/
theorem exists_radial_of_fderiv_chartN (q : ZMod N → Sphere n) {u : ZMod N → Ambient n}
    (h : fderiv ℝ (chartN q) (amb q) u = 0) :
    ∃ c : ZMod N → ℝ, u = fun i => c i • amb q i := by
  have hi : ∀ i, ∃ c : ℝ, u i = c • amb q i := by
    intro i
    apply exists_smul_of_fderiv_chartNormalize (q i)
    have h1 := fderiv_chartN_apply q u i
    rw [h] at h1
    exact h1.symm
  choose c hc using hi
  exact ⟨c, funext hc⟩

/-- The derivative of the inverse coordinate map is a section of the derivative of the
coordinates of the normalization. -/
theorem fderiv_chartN_decode (q : ZMod N → Sphere n) (v : Model n N) :
    fderiv ℝ (chartN q) (amb q) (fderiv ℝ (decode q) (base q) v) = v := by
  have hev : (fun x : Model n N => chartN q (decode q x)) =ᶠ[𝓝 (base q)] fun x => x := by
    filter_upwards [(chart q).open_target.mem_nhds (base_mem_target q)] with x hx
    unfold chartN
    have hx' := (mem_chart_target q x).mp hx
    have h1 : (fun i => chartNormalize (q i) (decode q x i)) = fun i => x i :=
      funext fun i => chartNormalize_inverseAmbient (hx' i)
    rw [h1]
  have hR : HasFDerivAt (decode q) (fderiv ℝ (decode q) (base q)) (base q) :=
    ((decode_contDiffAt q (base_mem_target q)).differentiableAt (by simp)).hasFDerivAt
  have hρ : HasFDerivAt (chartN q) (fderiv ℝ (chartN q) (amb q)) (decode q (base q)) := by
    rw [decode_base q]
    exact ((chartN_contDiffAt q).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hρ.comp (base q) hR
  have hid : fderiv ℝ (fun x : Model n N => chartN q (decode q x)) (base q) =
      ContinuousLinearMap.id ℝ (Model n N) := by
    rw [hev.fderiv_eq]
    exact fderiv_fun_id
  have h2 : (fderiv ℝ (chartN q) (amb q)).comp (fderiv ℝ (decode q) (base q)) =
      ContinuousLinearMap.id ℝ (Model n N) := by
    rw [← hid]
    exact hcomp.fderiv.symm
  exact congrArg (fun L : Model n N →L[ℝ] Model n N => L v) h2

/-- The second derivative of the penalized energy at a critical sphere polygon along a radial
vector. -/
theorem sndDeriv_pen_radial (F : ReversibleMetric n) (lam : ℝ) (q : ZMod N → Sphere n)
    (hf : ContDiffAt ℝ 2 (pen F N lam) (amb q)) (h0 : fderiv ℝ (pen F N lam) (amb q) = 0)
    (c : ZMod N → ℝ) :
    fderiv ℝ (fderiv ℝ (pen F N lam)) (amb q) (fun i => c i • amb q i)
      (fun i => c i • amb q i) = 2 * lam * ∑ i, c i ^ 2 := by
  have hγ : HasDerivAt (fun t : ℝ => amb q + t • (fun i => c i • amb q i : ZMod N → Ambient n))
      (fun i => c i • amb q i) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const
      (fun i => c i • amb q i : ZMod N → Ambient n)).const_add (amb q)
    rwa [one_smul] at h
  have hT := tendsto_div_sq hf h0 hγ (by simp)
  -- the increment along the radial line
  have hpos : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ i, 0 < 1 + t * c i := by
    have h1 : ∀ i, ∀ᶠ t : ℝ in 𝓝 0, 0 < 1 + t * c i := by
      intro i
      have hc : Continuous fun t : ℝ => 1 + t * c i := by fun_prop
      have h2 := hc.tendsto 0
      rw [zero_mul, add_zero] at h2
      exact h2.eventually (lt_mem_nhds zero_lt_one)
    exact (eventually_all.mpr h1).filter_mono nhdsWithin_le_nhds
  have hinc : (fun t : ℝ => (pen F N lam (amb q + t • (fun i => c i • amb q i)) -
      pen F N lam (amb q)) / t ^ 2) =ᶠ[𝓝[≠] 0]
      fun t : ℝ => lam * ∑ i, (t⁻¹ • (Real.log (1 + (0 + t) * c i) - Real.log (1 + 0 * c i))) ^ 2 := by
    filter_upwards [hpos, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t ≠ 0 := ht0
    have hpt : (amb q + t • (fun i => c i • amb q i : ZMod N → Ambient n)) =
        fun i => (1 + t * c i) • amb q i := by
      funext i
      rw [Pi.add_apply, Pi.smul_apply, smul_smul, add_smul, one_smul]
    have hE : polyEnergyN F N (fun i => (1 + t * c i) • amb q i) = polyEnergyN F N (amb q) :=
      polyEnergyN_smul F (fun i => 1 + t * c i) ht (amb q)
    have hlog : logPen (fun i => (1 + t * c i) • amb q i : ZMod N → Ambient n) =
        ∑ i, Real.log (1 + t * c i) ^ 2 := by
      unfold logPen
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, norm_amb, mul_one, Real.norm_of_nonneg (ht i).le]
    have hlog0 : logPen (amb q) = 0 := logPen_incl q
    rw [hpt]
    unfold pen
    rw [hE, hlog, hlog0, mul_zero, add_zero, add_sub_cancel_left, mul_div_assoc,
      Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zero_add, zero_mul, add_zero, Real.log_one, sub_zero, smul_eq_mul, mul_pow, inv_pow]
    field_simp
  have hlim : Tendsto (fun t : ℝ => lam * ∑ i,
      (t⁻¹ • (Real.log (1 + (0 + t) * c i) - Real.log (1 + 0 * c i))) ^ 2) (𝓝[≠] 0)
      (𝓝 (lam * ∑ i, c i ^ 2)) := by
    refine Tendsto.const_mul lam (tendsto_finsetSum _ fun i _ => Tendsto.pow ?_ 2)
    have hd : HasDerivAt (fun t : ℝ => Real.log (1 + t * c i)) (c i) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => 1 + t * c i) (c i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (c i)).const_add 1
      have h2 := (Real.hasDerivAt_log (by norm_num : (1 : ℝ) + 0 * c i ≠ 0)).comp (0 : ℝ) h1
      have h3 : (1 + 0 * c i)⁻¹ * c i = c i := by simp
      rw [h3] at h2
      exact h2
    exact hd.tendsto_slope_zero
  have huniq := tendsto_nhds_unique (hT.congr' hinc) hlim
  linarith

/-- The kernel of the second derivative of the penalized energy at a short stationary sphere
polygon without zero edges has the dimension of the nullity of the polygon. -/
theorem finrank_ker_sndDeriv_pen (F : ReversibleMetric n) {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)
    (hc : PolyCritical F N q) {lam : ℝ} (hlam : 0 < lam) :
    finrank ℝ (LinearMap.ker (fderiv ℝ (fderiv ℝ (pen F N lam)) (amb q)).toLinearMap₁₂) =
      nullity F q := by
  have hf₁ : ContDiffAt ℝ 2 (PolygonChart.energy F q) (base q) :=
    (energy_contDiffAt F hδ hq hne).of_le (by norm_num)
  have hE : ContDiffAt ℝ 2 (polyEnergyN F N) (amb q) :=
    (polyEnergyN_contDiffAt F hδ hq hne).of_le (by norm_num)
  have hf₂ : ContDiffAt ℝ 2 (pen F N lam) (amb q) := by
    unfold pen
    exact hE.add (contDiffAt_const.mul ((logPen_contDiffAt (incl q)).of_le (by simp)))
  have h₁ : fderiv ℝ (PolygonChart.energy F q) (base q) = 0 :=
    fderiv_energy_eq_zero_of_polyCritical F hδ hq hne hc
  have hR : HasFDerivAt (decode q) (fderiv ℝ (decode q) (base q)) (base q) :=
    ((decode_contDiffAt q (base_mem_target q)).differentiableAt (by simp)).hasFDerivAt
  have hR0 : decode q (base q) = amb q := decode_base q
  have hρ : HasFDerivAt (chartN q) (fderiv ℝ (chartN q) (amb q)) (amb q) :=
    ((chartN_contDiffAt q).differentiableAt (by simp)).hasFDerivAt
  have hρ0 : chartN q (amb q) = base q := chartN_amb q
  have hcomp : ∀ᶠ x in 𝓝 (base q), pen F N lam (decode q x) = PolygonChart.energy F q x :=
    Eventually.of_forall fun x => pen_decode F lam q x
  have hle : ∀ᶠ Q in 𝓝 (amb q), PolygonChart.energy F q (chartN q Q) ≤ pen F N lam Q := by
    filter_upwards [eventually_decode_chartN q] with Q hQ
    have h1 : PolygonChart.energy F q (chartN q Q) = polyEnergyN F N Q := by
      unfold PolygonChart.energy
      rw [hQ, polyEnergyN_eq_normalize F Q]
      exact polyEnergyN_eq F N (fun i => norm_coe (SphereRetraction.normalize (Q i)))
    rw [h1]
    unfold pen
    linarith [mul_nonneg hlam.le (logPen_nonneg Q)]
  have heq : PolygonChart.energy F q (base q) = pen F N lam (amb q) := by
    rw [← hR0]
    exact (pen_decode F lam q (base q)).symm
  have h₂ : fderiv ℝ (pen F N lam) (amb q) = 0 :=
    fderiv_eq_zero_of_le hρ0 (hf₁.differentiableAt (by simp)) (hf₂.differentiableAt (by simp))
      h₁ hρ hle heq
  have hs₁ : ∀ v w : Model n N,
      (fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q)).toLinearMap₁₂ v w =
      (fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q)).toLinearMap₁₂ w v :=
    fun v w => (hf₁.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq v w
  have hs₂ : ∀ v w : ZMod N → Ambient n,
      (fderiv ℝ (fderiv ℝ (pen F N lam)) (amb q)).toLinearMap₁₂ v w =
      (fderiv ℝ (fderiv ℝ (pen F N lam)) (amb q)).toLinearMap₁₂ w v :=
    fun v w => (hf₂.isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq v w
  have hker := finrank_ker_eq
    (β₁ := (fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q)).toLinearMap₁₂)
    (β₂ := (fderiv ℝ (fderiv ℝ (pen F N lam)) (amb q)).toLinearMap₁₂)
    (L := (fderiv ℝ (decode q) (base q)).toLinearMap)
    (π := (fderiv ℝ (chartN q) (amb q)).toLinearMap) hs₁ hs₂
    (fun v => fderiv_chartN_decode q v)
    (fun v => (sndDeriv_eq_of_comp hR0 hf₁ hf₂ h₁ h₂ hR hcomp v).symm)
    (fun u => sndDeriv_le_of_le hρ0 hf₁ hf₂ h₁ h₂ hρ hle heq u)
    (fun u hu hu0 => by
      obtain ⟨c, rfl⟩ := exists_radial_of_fderiv_chartN q hu
      have h1 := sndDeriv_pen_radial F lam q hf₂ h₂ c
      have h2 : ∃ i, c i ≠ 0 := by
        by_contra hcon
        apply hu0
        funext i
        have hci : c i = 0 := by
          by_contra hne'
          exact hcon ⟨i, hne'⟩
        rw [hci, zero_smul]
        rfl
      obtain ⟨i, hi⟩ := h2
      have h3 : 0 < ∑ j, c j ^ 2 :=
        lt_of_lt_of_le (by positivity)
          (Finset.single_le_sum (f := fun j => c j ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ i))
      change 0 < fderiv ℝ (fderiv ℝ (pen F N lam)) (amb q) (fun i => c i • amb q i)
        (fun i => c i • amb q i)
      rw [h1]
      positivity)
  rw [hker]
  -- the kernel of the bilinear function of the coordinate energy is the kernel of the Hessian
  have hkeq : LinearMap.ker
      (fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q)).toLinearMap₁₂ =
      LinearMap.ker (hessian F q).toLinearMap := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hv
      have hall : ∀ w : Model n N, ⟪hessian F q v, w⟫ = 0 := fun w => by
        rw [show ⟪hessian F q v, w⟫ =
          fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q) v w from
          Hessian.inner_operator _ _ _ _]
        exact congrArg (fun L : Model n N →ₗ[ℝ] ℝ => L w) hv
      have hz : hessian F q v = 0 := inner_self_eq_zero.mp (hall (hessian F q v))
      exact hz
    · intro hv
      refine LinearMap.ext fun w => ?_
      have h1 : ⟪hessian F q v, w⟫ =
          fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q) v w :=
        Hessian.inner_operator _ _ _ _
      change fderiv ℝ (fderiv ℝ (PolygonChart.energy F q)) (base q) v w = 0
      rw [← h1]
      have hv' : hessian F q v = 0 := hv
      rw [hv', inner_zero_left]
  rw [hkeq]
  rfl

end

end Finsler.AmbientNullity
