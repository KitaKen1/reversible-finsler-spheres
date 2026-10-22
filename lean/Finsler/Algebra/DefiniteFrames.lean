module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded

/-! Frames on which a symmetric bilinear function is negative definite. A frame is a tuple of b
vectors of a real normed space; it is negative for a bilinear function β if β(v, v) < 0 for every
nonzero combination v of its vectors. Multiplying a negative frame by an invertible matrix gives
a negative frame. For a continuous family of bilinear functions, negativity of a continuous
family of frames is an open condition in the parameter, uniformly over a compact set of further
parameters. If the β-orthogonal complement of a negative frame G carries no negative vector
(which holds when b is the index of β), every other negative frame H is joined to a frame G K of
the span of G, with K invertible, through the frames (1 − s) H + s G K, which are all
negative: H = G K + W with W orthogonal to G, and the quadratic function at a combination of
(1 − s) H + s G K is its value at G K plus (1 − s)² times a nonnegative number. A positive
multiple of a negative frame is negative. -/

@[expose] public section

namespace Finsler.DefiniteFrames

open Matrix Set Topology

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {b : ℕ}

/-- The combination of the vectors of a frame with given coefficients. -/
def comb (G : Fin b → V) (u : Fin b → ℝ) : V := ∑ i, u i • G i

theorem comb_smul (G : Fin b → V) (c : ℝ) (u : Fin b → ℝ) : comb G (c • u) = c • comb G u := by
  simp only [comb, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem comb_add_frame (G H : Fin b → V) (u : Fin b → ℝ) :
    comb (G + H) u = comb G u + comb H u := by
  simp only [comb, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem comb_smul_frame (c : ℝ) (G : Fin b → V) (u : Fin b → ℝ) :
    comb (c • G) u = c • comb G u := by
  simp only [comb, Pi.smul_apply, Finset.smul_sum, smul_comm c]

theorem comb_sub_frame (G H : Fin b → V) (u : Fin b → ℝ) :
    comb (G - H) u = comb G u - comb H u := by
  simp only [comb, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem comb_continuous :
    Continuous fun p : (Fin b → V) × (Fin b → ℝ) => comb p.1 p.2 := by
  unfold comb
  fun_prop

/-- The frame G K for a matrix K. -/
def mulF (G : Fin b → V) (K : Matrix (Fin b) (Fin b) ℝ) : Fin b → V :=
  fun j => ∑ i, K i j • G i

theorem comb_mulF (G : Fin b → V) (K : Matrix (Fin b) (Fin b) ℝ) (u : Fin b → ℝ) :
    comb (mulF G K) u = comb G (K.mulVec u) := by
  simp only [comb, mulF, Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem mulF_one (G : Fin b → V) : mulF G 1 = G := by
  funext j
  simp only [mulF, Matrix.one_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

theorem mulF_mul (G : Fin b → V) (K K' : Matrix (Fin b) (Fin b) ℝ) :
    mulF (mulF G K) K' = mulF G (K * K') := by
  funext j
  simp only [mulF, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem map_mulF (T : V →ₗ[ℝ] V) (G : Fin b → V) (K : Matrix (Fin b) (Fin b) ℝ) :
    (fun j => T (mulF G K j)) = mulF (fun j => T (G j)) K := by
  funext j
  simp only [mulF, map_sum, map_smul]

/-- A frame is negative for a bilinear function if the function is negative at every nonzero
combination of its vectors. -/
def Neg (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Fin b → V) : Prop :=
  ∀ u : Fin b → ℝ, u ≠ 0 → β (comb G u) (comb G u) < 0

variable {β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {G H : Fin b → V}

/-- A negative frame times an invertible matrix is a negative frame. -/
theorem neg_mulF (hG : Neg β G) {K : Matrix (Fin b) (Fin b) ℝ} (hK : K.det ≠ 0) :
    Neg β (mulF G K) := by
  intro u hu
  rw [comb_mulF]
  apply hG
  intro h
  exact hK (Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu, h⟩)

/-- The matrix of the values of a bilinear function at the vectors of two frames. -/
def gram (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G H : Fin b → V) : Matrix (Fin b) (Fin b) ℝ :=
  Matrix.of fun i j => β (G i) (H j)

theorem form_comb (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G H : Fin b → V) (u v : Fin b → ℝ) :
    β (comb G u) (comb H v) = u ⬝ᵥ (gram β G H).mulVec v := by
  simp only [comb, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    dotProduct, Matrix.mulVec, gram, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A vector orthogonal to the vectors of a frame is orthogonal to their combinations. -/
theorem form_comb_left_eq_zero (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (G : Fin b → V) {w : V}
    (hw : ∀ i, β (G i) w = 0) (u : Fin b → ℝ) : β (comb G u) w = 0 := by
  simp only [comb, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hw, smul_zero,
    Finset.sum_const_zero]

theorem det_gram_ne_zero (hG : Neg β G) : (gram β G G).det ≠ 0 := by
  intro h
  obtain ⟨u, hu, hu0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have h1 := hG u hu
  rw [form_comb, hu0, dotProduct_zero] at h1
  exact lt_irrefl _ h1

/-- Projection of a negative frame to the span of another: if the orthogonal complement of the
negative frame G carries no negative vector, a negative frame H is joined to G K, K invertible,
through negative frames. -/
theorem exists_projection (hsym : ∀ v w, β v w = β w v) (hG : Neg β G) (hH : Neg β H)
    (hidx : ∀ w, (∀ i, β (G i) w = 0) → 0 ≤ β w w) :
    ∃ K : Matrix (Fin b) (Fin b) ℝ, K.det ≠ 0 ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Neg β ((1 - s) • H + s • mulF G K) := by
  set S := gram β G G with hS
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr (det_gram_ne_zero hG)
  set K : Matrix (Fin b) (Fin b) ℝ := S⁻¹ * gram β G H with hK
  have hSK : S * K = gram β G H := by
    rw [hK, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul]
  -- the residual frame is orthogonal to G
  have hres : ∀ i j, β (G i) ((H - mulF G K) j) = 0 := by
    intro i j
    have h1 : β (G i) (mulF G K j) = (S * K) i j := by
      simp only [mulF, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, hS, gram,
        Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_comm]
    rw [Pi.sub_apply, map_sub, h1, hSK, gram, Matrix.of_apply, sub_self]
  have horth : ∀ (u : Fin b → ℝ) (i : Fin b), β (G i) (comb (H - mulF G K) u) = 0 := by
    intro u i
    simp only [comb, map_sum, map_smul, hres, smul_zero, Finset.sum_const_zero]
  have hcross : ∀ u x : Fin b → ℝ, β (comb G x) (comb (H - mulF G K) u) = 0 :=
    fun u x => form_comb_left_eq_zero β G (horth u) x
  have hpos : ∀ u : Fin b → ℝ, 0 ≤ β (comb (H - mulF G K) u) (comb (H - mulF G K) u) :=
    fun u => hidx _ (horth u)
  -- the value of the quadratic function along the segment
  have hval : ∀ (t : ℝ) (u : Fin b → ℝ),
      β (comb (mulF G K) u + t • comb (H - mulF G K) u)
          (comb (mulF G K) u + t • comb (H - mulF G K) u) =
        β (comb (mulF G K) u) (comb (mulF G K) u) +
          t ^ 2 * β (comb (H - mulF G K) u) (comb (H - mulF G K) u) := by
    intro t u
    have hc1 : β (comb (mulF G K) u) (comb (H - mulF G K) u) = 0 := by
      rw [comb_mulF]
      exact hcross u _
    have hc2 : β (comb (H - mulF G K) u) (comb (mulF G K) u) = 0 := by
      rw [hsym]
      exact hc1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hc1,
      hc2]
    ring
  have hHdecomp : ∀ u : Fin b → ℝ,
      comb H u = comb (mulF G K) u + (1 : ℝ) • comb (H - mulF G K) u := by
    intro u
    rw [one_smul, comb_sub_frame]
    abel
  refine ⟨K, ?_, ?_⟩
  · intro hdet
    obtain ⟨u, hu, hu0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h1 := hH u hu
    rw [hHdecomp u, hval 1 u, comb_mulF, hu0] at h1
    have h0 : comb G (0 : Fin b → ℝ) = 0 := by simp [comb]
    rw [h0, map_zero, zero_add, one_pow, one_mul] at h1
    exact absurd h1 (not_lt.mpr (hpos u))
  · intro s hs0 hs1 u hu
    have hfr : comb ((1 - s) • H + s • mulF G K) u =
        comb (mulF G K) u + (1 - s) • comb (H - mulF G K) u := by
      rw [comb_add_frame, comb_smul_frame, comb_smul_frame, comb_sub_frame]
      module
    rw [hfr, hval (1 - s) u]
    have h1 := hH u hu
    rw [hHdecomp u, hval 1 u, one_pow, one_mul] at h1
    have h2 : (1 - s) ^ 2 ≤ 1 := by nlinarith
    nlinarith [hpos u]

/-- A positive multiple of a negative frame is negative. -/
theorem neg_smul_frame (hG : Neg β G) {c : ℝ} (hc : 0 < c) : Neg β (c • G) := by
  intro u hu
  rw [comb_smul_frame]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have h := hG u hu
  nlinarith [mul_pos hc hc]

/-! ### Openness of negativity -/

variable {Θ : Type*} [TopologicalSpace Θ] (B : Θ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

theorem form_smul (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (c : ℝ) (v : V) :
    β (c • v) (c • v) = c ^ 2 * β v v := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- A frame is negative if the function is negative at its combinations with coefficients of
norm one. -/
theorem neg_of_sphere {β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {G : Fin b → V}
    (h : ∀ u ∈ Metric.sphere (0 : Fin b → ℝ) 1, β (comb G u) (comb G u) < 0) : Neg β G := by
  intro u hu
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hsph : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : Fin b → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have h1 := h _ hsph
  have h2 : u = ‖u‖ • (‖u‖⁻¹ • u) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [h2, comb_smul, form_smul]
  exact mul_neg_of_pos_of_neg (pow_pos hn 2) h1

/-- Negativity of a continuous family of frames for a continuous family of bilinear functions
is an open condition in the parameter, uniformly over a compact set of further parameters. -/
theorem isOpen_neg (hB : Continuous fun p : Θ × V × V => B p.1 p.2.1 p.2.2) {Y : Type*}
    [TopologicalSpace Y] {S : Set Y} (hS : IsCompact S) (Φ : Θ × Y → Fin b → V)
    (hΦ : Continuous Φ) : IsOpen {θ : Θ | ∀ y ∈ S, Neg (B θ) (Φ (θ, y))} := by
  have hF : Continuous fun z : Θ × (Y × (Fin b → ℝ)) =>
      B z.1 (comb (Φ (z.1, z.2.1)) z.2.2) (comb (Φ (z.1, z.2.1)) z.2.2) := by
    have hc : Continuous fun z : Θ × (Y × (Fin b → ℝ)) => comb (Φ (z.1, z.2.1)) z.2.2 :=
      comb_continuous.comp ((hΦ.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))
    exact hB.comp (continuous_fst.prodMk (hc.prodMk hc))
  have hK : IsCompact (S ×ˢ Metric.sphere (0 : Fin b → ℝ) 1) :=
    hS.prod (isCompact_sphere 0 1)
  rw [isOpen_iff_eventually]
  intro θ₀ hθ₀
  have hev : ∀ᶠ θ in 𝓝 θ₀, ∀ p ∈ S ×ˢ Metric.sphere (0 : Fin b → ℝ) 1,
      B θ (comb (Φ (θ, p.1)) p.2) (comb (Φ (θ, p.1)) p.2) < 0 := by
    refine hK.eventually_forall_of_forall_eventually fun p hp => ?_
    have hneg : B θ₀ (comb (Φ (θ₀, p.1)) p.2) (comb (Φ (θ₀, p.1)) p.2) < 0 := by
      apply hθ₀ p.1 hp.1
      intro h0
      have h1 : ‖p.2‖ = 1 := mem_sphere_zero_iff_norm.mp hp.2
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    exact (hF.tendsto (θ₀, p)).eventually (gt_mem_nhds hneg)
  filter_upwards [hev] with θ hθ y hy
  exact neg_of_sphere fun u hu => hθ (y, u) ⟨hy, hu⟩

end

end Finsler.DefiniteFrames
