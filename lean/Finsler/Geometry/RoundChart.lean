module

public import Finsler.Geometry.RoundPenForm
public import Finsler.Geometry.RoundSpectral

/-! The chart around the critical manifold of regular m-gons and the definiteness of the second
derivative on its fibres.

Let N = 2M + 1 and 0 < m ≤ M. The chart sends an orthonormal pair z = (x, u) and a fibre
vector ξ = (τ, V), τ ∈ ℝ³ and V a polygon without the frequency m, to

  chart(z, ξ) = regular(x + τ₁ x, τ₂ x + u + τ₃ u) + V,

the Gram–Schmidt form of the frequency-m coefficients. The negative part of V is the
projection of its low modes 0 ≤ j < m onto the normal space of the plane of (x, u); the
reflection J z exchanges its sign with the rest: J z (τ, V) = (−τ, 2·neg V − V).

At the regular m-gon Q = chart(z, 0) put A = neg V and B = lin ξ − A. Then
D²pen(A + B, A − B) = D²pen(A, A) − D²pen(B, B); A is a sum of normal low modes, so
D²pen(A, A) ≤ −μ |A|²; B = (radial) + (tangential) + (normal high modes), so
D²pen(B, B) = 2N Σ (Δβ)² + 2 Σ ρ² + D²E(w, w) ≥ 0 with D²E(w, w) ≥ ν |w|². If the difference
vanishes, A = 0, w = 0, ρ = 0 and β is constant, so B is a multiple of the rotation of the
regular polygon; comparing frequency-m coefficients shows that the multiple and τ vanish, and
then V = 0. Hence −D²pen(lin ξ, lin (J z ξ)) > 0 for ξ ≠ 0. -/

@[expose] public section

namespace Finsler.RoundChart

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon Finsler.RoundHessian
open Finsler.RoundModes Finsler.RoundNondeg Finsler.RoundCoords Finsler.RoundSpectral
open Finsler.RoundPenHess Finsler.RoundPenForm Finsler.AmbientPenalty Finsler.PolygonSmooth
open Finset Filter Set
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-! ### The Stiefel set -/

/-- The orthonormal pairs. -/
def V2 : Set (Ambient n × Ambient n) := {z | ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧ ⟪z.1, z.2⟫ = 0}

theorem isCompact_V2 : IsCompact (V2 (n := n)) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have h1 : IsClosed {z : Ambient n × Ambient n | ‖z.1‖ = 1} :=
      isClosed_eq (continuous_norm.comp continuous_fst) continuous_const
    have h2 : IsClosed {z : Ambient n × Ambient n | ‖z.2‖ = 1} :=
      isClosed_eq (continuous_norm.comp continuous_snd) continuous_const
    have h3 : IsClosed {z : Ambient n × Ambient n | ⟪z.1, z.2⟫ = 0} :=
      isClosed_eq (continuous_fst.inner continuous_snd) continuous_const
    exact h1.inter (h2.inter h3)
  · refine (Metric.isBounded_iff_subset_closedBall (0 : Ambient n × Ambient n)).mpr ⟨1, ?_⟩
    rintro z ⟨h1, h2, -⟩
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, h1, h2, max_self]

variable (m : ℕ)

/-! ### The fibre and the chart -/

/-- The fibre: triangular increments and polygons without the frequency m. -/
abbrev Fib (n N m : ℕ) [NeZero N] := (ℝ × ℝ × ℝ) × kern (n := n) (N := N) m

/-- The linear part of the chart at a pair. -/
def linL (z : Ambient n × Ambient n) : Fib n N m →ₗ[ℝ] (ZMod N → Ambient n) where
  toFun ξ := regular N m (ξ.1.1 • z.1) (ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2) + (ξ.2 : ZMod N → Ambient n)
  map_add' ξ η := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    rw [show ξ.1.2.1 • z.1 + η.1.2.1 • z.1 + (ξ.1.2.2 • z.2 + η.1.2.2 • z.2) =
      (ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2) + (η.1.2.1 • z.1 + η.1.2.2 • z.2) by abel, regular_add]
    abel
  map_smul' r ξ := by
    change regular N m ((r * ξ.1.1) • z.1) ((r * ξ.1.2.1) • z.1 + (r * ξ.1.2.2) • z.2) +
        r • (ξ.2 : ZMod N → Ambient n) =
      r • (regular N m (ξ.1.1 • z.1) (ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2) + (ξ.2 : ZMod N → Ambient n))
    rw [smul_add, ← regular_smul, smul_add, mul_smul, mul_smul, mul_smul]

/-- The linear part of the chart as a continuous linear map. -/
def lin (z : Ambient n × Ambient n) : Fib n N m →L[ℝ] (ZMod N → Ambient n) :=
  LinearMap.toContinuousLinearMap (linL m z)

theorem lin_apply (z : Ambient n × Ambient n) (ξ : Fib n N m) :
    lin m z ξ = regular N m (ξ.1.1 • z.1) (ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2) +
      (ξ.2 : ZMod N → Ambient n) := rfl

/-- The chart. -/
def chart (p : (Ambient n × Ambient n) × Fib n N m) : ZMod N → Ambient n :=
  regular N m p.1.1 p.1.2 + lin m p.1 p.2

theorem chart_zero (z : Ambient n × Ambient n) : chart m (z, 0) = regular N m z.1 z.2 := by
  simp [chart]

/-- The chart is smooth. -/
theorem chart_contDiff : ContDiff ℝ ∞ (chart (n := n) (N := N) m) := by
  have hsub : ContDiff ℝ ∞ (fun p : (Ambient n × Ambient n) × Fib n N m =>
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n)) :=
    (kern (n := n) (N := N) m).subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)
  rw [contDiff_pi]
  intro i
  have h : (fun p : (Ambient n × Ambient n) × Fib n N m => chart m p i) = fun p =>
      (Real.cos (2 * π * m / N * i.val) • p.1.1 + Real.sin (2 * π * m / N * i.val) • p.1.2) +
      (Real.cos (2 * π * m / N * i.val) • (p.2.1.1 • p.1.1) +
        Real.sin (2 * π * m / N * i.val) • (p.2.1.2.1 • p.1.1 + p.2.1.2.2 • p.1.2)) +
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) i := by
    funext p
    simp only [chart, lin_apply, regular, circ, Pi.add_apply, smul_add]
    abel
  rw [h]
  have hi : ContDiff ℝ ∞ (fun p : (Ambient n × Ambient n) × Fib n N m =>
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) i) :=
    (contDiff_apply ℝ (Ambient n) i).comp hsub
  fun_prop

/-! ### Low modes and the negative part -/

/-- The low modes of a polygon. -/
def low (V : ZMod N → Ambient n) : ZMod N → Ambient n := ∑ j ∈ range m, mode j V

/-- The high modes of a polygon. -/
def high (M : ℕ) (V : ZMod N → Ambient n) : ZMod N → Ambient n :=
  ∑ j ∈ Ico (m + 1) (M + 1), mode j V

theorem low_add (V V' : ZMod N → Ambient n) : low m (V + V') = low m V + low m V' := by
  simp only [low, mode_add, Finset.sum_add_distrib]

theorem low_smul (r : ℝ) (V : ZMod N → Ambient n) : low m (r • V) = r • low m V := by
  simp only [low, mode_smul, Finset.smul_sum]

theorem low_onVert (f : Ambient n →L[ℝ] Ambient n) (V : ZMod N → Ambient n) :
    low m (onVert f V) = onVert f (low m V) := by
  simp only [low, mode_onVert, map_sum]

theorem high_onVert (M : ℕ) (f : Ambient n →L[ℝ] Ambient n) (V : ZMod N → Ambient n) :
    high m M (onVert f V) = onVert f (high m M V) := by
  simp only [high, mode_onVert, map_sum]

variable {m}

/-- A polygon without the frequency m is the sum of its low and high modes. -/
theorem low_add_high {M : ℕ} (hNM : N = 2 * M + 1) (hm : 0 < m) (hmM : m ≤ M)
    {V : ZMod N → Ambient n} (hV : V ∈ kern (n := n) (N := N) m) : low m V + high m M V = V := by
  have hmode : mode m V = 0 := by
    rw [mem_kern] at hV
    unfold mode coefPair
    rw [if_neg hm.ne', hV.1, hV.2]
    funext i
    simp [regular, circ]
  conv_rhs => rw [← sum_mode hNM V]
  unfold low high
  rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ M + 1 by omega),
    Finset.sum_eq_sum_Ico_succ_bot (show m < M + 1 by omega), hmode, zero_add]

theorem coefA_mode_ne {j j' : ℕ} (hj0 : 0 < j) (hj : 2 * j < N) (hj' : 2 * j' < N) (hne : j ≠ j')
    (V : ZMod N → Ambient n) : coefA j (mode j' V) = 0 := by
  unfold mode
  rw [coefA_regular hj0 hj hj', if_neg hne]

theorem coefB_mode_ne {j j' : ℕ} (hj0 : 0 < j) (hj : 2 * j < N) (hj' : 2 * j' < N) (hne : j ≠ j')
    (V : ZMod N → Ambient n) : coefB j (mode j' V) = 0 := by
  unfold mode
  rw [coefB_regular hj0 hj hj', if_neg hne]

/-- The low modes have no frequency m. -/
theorem low_mem_kern (hm : 0 < m) (hmN : 2 * m < N) (V : ZMod N → Ambient n) :
    low m V ∈ kern (n := n) (N := N) m := by
  rw [mem_kern]
  unfold low
  constructor
  · rw [coefA_sum]
    exact Finset.sum_eq_zero fun j hj => coefA_mode_ne hm hmN
      (by have := Finset.mem_range.mp hj; omega) (by have := Finset.mem_range.mp hj; omega) V
  · rw [coefB_sum]
    exact Finset.sum_eq_zero fun j hj => coefB_mode_ne hm hmN
      (by have := Finset.mem_range.mp hj; omega) (by have := Finset.mem_range.mp hj; omega) V

theorem onVert_mem_kern (f : Ambient n →L[ℝ] Ambient n) {V : ZMod N → Ambient n}
    (hV : V ∈ kern (n := n) (N := N) m) : onVert f V ∈ kern (n := n) (N := N) m := by
  rw [mem_kern] at hV ⊢
  rw [coefA_onVert, coefB_onVert, hV.1, hV.2, map_zero]
  exact ⟨rfl, rfl⟩

variable (m)

/-- The negative part of a polygon at a pair: the normal projection of its low modes. -/
def negV (z : Ambient n × Ambient n) (V : ZMod N → Ambient n) : ZMod N → Ambient n :=
  onVert (projW z) (low m V)

variable {m}

theorem negV_mem_kern (hm : 0 < m) (hmN : 2 * m < N) (z : Ambient n × Ambient n)
    (V : ZMod N → Ambient n) : negV m z V ∈ kern (n := n) (N := N) m :=
  onVert_mem_kern _ (low_mem_kern hm hmN V)

variable (hm : 0 < m) (hmN : 2 * m < N)

/-- The reflection of the fibre exchanging the sign of the negative part. -/
def JL (z : Ambient n × Ambient n) : Fib n N m →ₗ[ℝ] Fib n N m where
  toFun ξ := (-ξ.1, ⟨(2 : ℝ) • negV m z (ξ.2 : ZMod N → Ambient n) - (ξ.2 : ZMod N → Ambient n),
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (negV_mem_kern hm hmN z _)) ξ.2.2⟩)
  map_add' ξ η := by
    refine Prod.ext (neg_add _ _) (Subtype.ext ?_)
    simp only [Prod.snd_add, Submodule.coe_add, negV, low_add, map_add, smul_add]
    abel
  map_smul' r ξ := by
    refine Prod.ext (smul_neg r ξ.1).symm (Subtype.ext ?_)
    simp only [Prod.smul_snd, Submodule.coe_smul, negV, low_smul, map_smul, RingHom.id_apply,
      smul_sub, smul_comm r (2 : ℝ)]

/-- The reflection as a continuous linear map. -/
def J (z : Ambient n × Ambient n) : Fib n N m →L[ℝ] Fib n N m :=
  LinearMap.toContinuousLinearMap (JL hm hmN z)

theorem J_apply (z : Ambient n × Ambient n) (ξ : Fib n N m) :
    ((J hm hmN z ξ).1 = -ξ.1) ∧
      ((J hm hmN z ξ).2 : ZMod N → Ambient n) =
        (2 : ℝ) • negV m z (ξ.2 : ZMod N → Ambient n) - (ξ.2 : ZMod N → Ambient n) :=
  ⟨rfl, rfl⟩

/-- The chart's linear part on the reflected vector. -/
theorem lin_J (z : Ambient n × Ambient n) (ξ : Fib n N m) :
    lin m z (J hm hmN z ξ) = negV m z (ξ.2 : ZMod N → Ambient n) -
      (lin m z ξ - negV m z (ξ.2 : ZMod N → Ambient n)) := by
  rw [lin_apply, lin_apply, (J_apply hm hmN z ξ).2]
  have h1 : (J hm hmN z ξ).1 = -ξ.1 := (J_apply hm hmN z ξ).1
  rw [h1]
  have hr : regular N m ((-ξ.1).1 • z.1) ((-ξ.1).2.1 • z.1 + (-ξ.1).2.2 • z.2) =
      -regular N m (ξ.1.1 • z.1) (ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2) := by
    rw [← neg_one_smul ℝ (regular N m _ _), ← regular_smul]
    congr 1 <;> simp [neg_smul, smul_add]
  rw [hr, two_smul]
  abel

/-! ### Definiteness on the fibres -/

section Definite

theorem coefPair_onVert (f : Ambient n →L[ℝ] Ambient n) (j : ℕ) (V : ZMod N → Ambient n) :
    coefPair j (onVert f V) = (f (coefPair j V).1, f (coefPair j V).2) := by
  unfold coefPair
  split_ifs
  · simp [coefA_onVert, map_smul]
  · simp [coefA_onVert, coefB_onVert]

/-- A projected sum of modes. -/
theorem onVert_sum_mode (f : Ambient n →L[ℝ] Ambient n) (s : Finset ℕ) (V : ZMod N → Ambient n) :
    onVert f (∑ j ∈ s, mode j V) =
      ∑ j ∈ s, regular N j (f (coefPair j V).1) (f (coefPair j V).2) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold mode
  rw [onVert_regular]

/-- In-plane vectors in the rotated orthonormal basis of a vertex. -/
theorem plane_rot {x u : Ambient n} (θ : ℝ) (p : Ambient n) (hp : p = ⟪x, p⟫ • x + ⟪u, p⟫ • u) :
    p = ⟪circ x u θ, p⟫ • circ x u θ + ⟪circ x u (θ + π / 2), p⟫ • circ x u (θ + π / 2) := by
  set α := ⟪x, p⟫
  set β := ⟪u, p⟫
  have h1 : ⟪circ x u θ, p⟫ = Real.cos θ * α + Real.sin θ * β := by
    simp only [circ, inner_add_left, real_inner_smul_left, α, β]
  have h2 : ⟪circ x u (θ + π / 2), p⟫ = -Real.sin θ * α + Real.cos θ * β := by
    simp only [circ, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, inner_add_left,
      real_inner_smul_left, α, β]
    try ring
  rw [h1, h2]
  simp only [circ, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  have hcs := Real.cos_sq_add_sin_sq θ
  have e1 : (Real.cos θ * α + Real.sin θ * β) * Real.cos θ +
      (-Real.sin θ * α + Real.cos θ * β) * (-Real.sin θ) = α := by linear_combination α * hcs
  have e2 : (Real.cos θ * α + Real.sin θ * β) * Real.sin θ +
      (-Real.sin θ * α + Real.cos θ * β) * Real.cos θ = β := by linear_combination β * hcs
  calc p = α • x + β • u := hp
    _ = ((Real.cos θ * α + Real.sin θ * β) * Real.cos θ +
          (-Real.sin θ * α + Real.cos θ * β) * (-Real.sin θ)) • x +
        ((Real.cos θ * α + Real.sin θ * β) * Real.sin θ +
          (-Real.sin θ * α + Real.cos θ * β) * Real.cos θ) • u := by rw [e1, e2]
    _ = _ := by
      simp only [smul_add, smul_smul, add_smul, smul_neg, neg_smul, mul_neg]
      abel

theorem tang_eq_regular (x u : Ambient n) : tang N m x u = regular N m u (-x) := by
  funext i
  simp only [tang, regular, circ, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, smul_neg,
    neg_smul]
  abel

section Pair

variable {z : Ambient n × Ambient n} (hz : z ∈ V2)
include hz

theorem projW_fst : projW z z.1 = 0 := by
  obtain ⟨hx, -, hxu⟩ := hz
  have hxx : ⟪z.1, z.1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have hux : ⟪z.2, z.1⟫ = 0 := by rw [real_inner_comm, hxu]
  rw [projW_apply, hxx, hux, one_smul, zero_smul, add_zero, sub_self]

theorem projW_snd : projW z z.2 = 0 := by
  obtain ⟨-, hu, hxu⟩ := hz
  have huu : ⟪z.2, z.2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  rw [projW_apply, huu, hxu, one_smul, zero_smul, zero_add, sub_self]

theorem onVert_projW_idem (W : ZMod N → Ambient n) :
    onVert (projW z) (onVert (projW z) W) = onVert (projW z) W := by
  funext i
  simp only [onVert_apply]
  exact projW_projW hz.1 hz.2.1 hz.2.2 _

/-- The negative part as a sum of normal low modes. -/
theorem negV_eq (V : ZMod N → Ambient n) :
    negV m z V = ∑ j ∈ range m, regular N j (projW z (coefPair j V).1)
      (projW z (coefPair j V).2) := by
  unfold negV low
  exact onVert_sum_mode _ _ _

/-- The normal part of the positive part is a sum of normal high modes. -/
theorem normal_pos_eq {M : ℕ} (hNM : N = 2 * M + 1) (hm : 0 < m) (hmM : m < M) (ξ : Fib n N m) :
    onVert (projW z) (lin m z ξ - negV m z (ξ.2 : ZMod N → Ambient n)) =
      ∑ j ∈ Ico (m + 1) (M + 1), regular N j (projW z (coefPair j (ξ.2 : ZMod N → Ambient n)).1)
        (projW z (coefPair j (ξ.2 : ZMod N → Ambient n)).2) := by
  have hreg : onVert (projW z) (regular N m (ξ.1.1 • z.1) (ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2)) = 0 := by
    rw [onVert_regular, map_smul, map_add, map_smul, map_smul, projW_fst hz, projW_snd hz]
    funext i
    simp [regular, circ]
  have hidem : onVert (projW z) (negV m z (ξ.2 : ZMod N → Ambient n)) =
      negV m z (ξ.2 : ZMod N → Ambient n) := onVert_projW_idem hz _
  have hlh := low_add_high hNM hm hmM.le ξ.2.2
  rw [map_sub, lin_apply, map_add, hreg, zero_add, hidem]
  unfold negV
  rw [← map_sub]
  have : (ξ.2 : ZMod N → Ambient n) - low m (ξ.2 : ZMod N → Ambient n) =
      high m M (ξ.2 : ZMod N → Ambient n) := (eq_sub_of_add_eq' hlh).symm
  rw [this]
  unfold high
  exact onVert_sum_mode _ _ _

/-- Every polygon splits into radial, tangential and normal parts at a regular polygon. -/
theorem split_vertices (B : ZMod N → Ambient n) :
    B = scaleL (fun i => ⟪regular N m z.1 z.2 i, B i⟫) (regular N m z.1 z.2) +
      (fun i => ⟪tang N m z.1 z.2 i, B i⟫ • tang N m z.1 z.2 i) + onVert (projW z) B := by
  obtain ⟨hx, hu, hxu⟩ := hz
  have hxx : ⟪z.1, z.1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪z.2, z.2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪z.2, z.1⟫ = 0 := by rw [real_inner_comm, hxu]
  funext i
  simp only [Pi.add_apply, scaleL_apply, onVert_apply]
  set θ := 2 * π * m / N * i.val
  set p := ⟪z.1, B i⟫ • z.1 + ⟪z.2, B i⟫ • z.2 with hpdef
  have hp : p = ⟪z.1, p⟫ • z.1 + ⟪z.2, p⟫ • z.2 := by
    have e1 : ⟪z.1, p⟫ = ⟪z.1, B i⟫ := by
      rw [hpdef, inner_add_right, real_inner_smul_right, real_inner_smul_right, hxx, hxu]
      ring
    have e2 : ⟪z.2, p⟫ = ⟪z.2, B i⟫ := by
      rw [hpdef, inner_add_right, real_inner_smul_right, real_inner_smul_right, hux, huu]
      ring
    rw [e1, e2]
  have hrot := plane_rot θ p hp
  have hB : B i = projW z (B i) + p := projW_add_plane z (B i)
  have hperp : ∀ c : ℝ, ⟪circ z.1 z.2 c, projW z (B i)⟫ = 0 := by
    intro c
    obtain ⟨h1, h2⟩ := inner_projW hx hu hxu (B i)
    simp only [circ, inner_add_left, real_inner_smul_left, h1, h2]
    ring
  have hreg : regular N m z.1 z.2 i = circ z.1 z.2 θ := rfl
  have htang : tang N m z.1 z.2 i = circ z.1 z.2 (θ + π / 2) := rfl
  have hq1 : ⟪circ z.1 z.2 θ, B i⟫ = ⟪circ z.1 z.2 θ, p⟫ := by
    conv_lhs => rw [hB]
    rw [inner_add_right, hperp, zero_add]
  have hq2 : ⟪circ z.1 z.2 (θ + π / 2), B i⟫ = ⟪circ z.1 z.2 (θ + π / 2), p⟫ := by
    conv_lhs => rw [hB]
    rw [inner_add_right, hperp, zero_add]
  rw [hreg, htang, hq1, hq2, ← hrot]
  conv_lhs => rw [hB]
  abel

end Pair

section Main

variable {M : ℕ} (hNM : N = 2 * M + 1) (hm : 0 < m) (hmM : m < M)
include hNM hmM

theorem two_m_lt_N : 2 * m < N := by omega

variable (m) in
/-- The fibre form: minus the second derivative of pen at the regular polygon, paired with the
reflection. -/
def fibForm (z : Ambient n × Ambient n) (ξ : Fib n N m) : ℝ :=
  -fderiv ℝ (fderiv ℝ (pen (roundMetric n) N 1)) (regular N m z.1 z.2) (lin m z ξ)
    (lin m z (J hm (two_m_lt_N hNM hmM) z ξ))

omit hNM hmM in
theorem pair_eq_zero {w : ZMod N → Ambient n} (h : pair w w = 0) : w = 0 := by
  rw [pair_self] at h
  funext i
  have hle : ‖w i‖ ^ 2 ≤ ∑ j : ZMod N, ‖w j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have : ‖w i‖ ^ 2 = 0 := le_antisymm (h ▸ hle) (sq_nonneg _)
  simpa using this

/-- **Definiteness of the fibre form.** It is nonnegative and vanishes only at ξ = 0. -/
theorem fibForm_pos {z : Ambient n × Ambient n} (hz : z ∈ V2) (ξ : Fib n N m) :
    0 ≤ fibForm m hNM hm hmM z ξ ∧ (fibForm m hNM hm hmM z ξ = 0 → ξ = 0) := by
  have hmN : 2 * m < N := two_m_lt_N hNM hmM
  obtain ⟨hx, hu, hxu⟩ := hz
  set Q := regular N m z.1 z.2 with hQ
  set V : ZMod N → Ambient n := (ξ.2 : ZMod N → Ambient n) with hV
  set A := negV m z V with hA
  set B := lin m z ξ - A with hB
  have hlinJ := lin_J hm hmN z ξ
  rw [← hV, ← hA] at hlinJ
  set H := fderiv ℝ (fderiv ℝ (pen (roundMetric n) N 1)) Q with hH
  have hC2 : ContDiffAt ℝ 2 (pen (roundMetric n) N 1) Q :=
    (pen_contDiffAt (regular_mem_good hm hmN hx hu hxu) 1).of_le (by simp)
  have hsym := hC2.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)
  have hF : fibForm m hNM hm hmM z ξ = H B B - H A A := by
    have hl : lin m z ξ = A + B := by rw [hB]; abel
    have e : fibForm m hNM hm hmM z ξ = -H (A + B) (A - B) := by
      unfold fibForm
      rw [← hl, ← hlinJ]
    rw [e]
    simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    rw [hsym.eq B A]
    ring
  -- the coefficients of the normal parts
  set a : ℕ → Ambient n := fun j => projW z (coefPair j V).1 with ha
  set b : ℕ → Ambient n := fun j => projW z (coefPair j V).2 with hb
  have hab_a : ∀ j, ⟪z.1, a j⟫ = 0 ∧ ⟪z.2, a j⟫ = 0 := fun j => inner_projW hx hu hxu _
  have hab_b : ∀ j, ⟪z.1, b j⟫ = 0 ∧ ⟪z.2, b j⟫ = 0 := fun j => inner_projW hx hu hxu _
  have hE2 := E_contDiffAt hm hmN hx hu hxu
  set c := Real.cos (2 * π * m / N) with hc
  have hcb := cos_ang_bounds (N := N) hm hmN
  have hG : G c < 0 := G_neg hcb.1 hcb.2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  -- the negative part
  have hAeq : A = ∑ j ∈ range m, regular N j (a j) (b j) := negV_eq ⟨hx, hu, hxu⟩ V
  have hAn : ∀ i, ⟪z.1, A i⟫ = 0 ∧ ⟪z.2, A i⟫ = 0 := fun i => by
    rw [hAeq]
    exact modes_normal (range m) a b hab_a hab_b i
  have hAA : H A A = fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) Q A A := by
    have h := pen_hessian_split hm hmN hx hu hxu (fun _ => 0) (fun _ => 0) A
      (fun i => (hAn i).1) (fun i => (hAn i).2)
    have h0 : scaleL (fun _ : ZMod N => (0 : ℝ)) Q + (fun i => (0 : ℝ) • tang N m z.1 z.2 i) + A = A := by
      funext i
      simp [scaleL_apply]
    rw [h0] at h
    rw [hH, h]
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero, add_zero, zero_add]
    rfl
  have hEA := hessian_low_le hm hmN hx hu hxu hE2 a b hab_a hab_b
  rw [← hAeq] at hEA
  set μ := Real.cos (2 * π * (m - 1 : ℕ) / N) - c with hμ
  have hμpos : 0 < μ := by
    have := cos_ang_strict (N := N) (show m - 1 < m by omega) (by omega)
    rw [hμ, hc]
    linarith
  have hk1 : 2 * N * G c * μ < 0 := by
    have e : 2 * (N : ℝ) * G c * μ = (2 * N * μ) * G c := by ring
    rw [e]
    exact mul_neg_of_pos_of_neg (by positivity) hG
  -- the positive part
  set ρ : ZMod N → ℝ := fun i => ⟪Q i, B i⟫ with hρ
  set β : ZMod N → ℝ := fun i => ⟪tang N m z.1 z.2 i, B i⟫ with hβ
  set w := onVert (projW z) B with hw
  have hBdec := split_vertices (m := m) ⟨hx, hu, hxu⟩ B
  rw [← hQ, ← hw] at hBdec
  have hweq : w = ∑ j ∈ Ico (m + 1) (M + 1), regular N j (a j) (b j) :=
    normal_pos_eq ⟨hx, hu, hxu⟩ hNM hm hmM ξ
  have hwn : ∀ i, ⟪z.1, w i⟫ = 0 ∧ ⟪z.2, w i⟫ = 0 := fun i => by
    rw [hweq]
    exact modes_normal _ a b hab_a hab_b i
  have hBB : H B B = 2 * (N * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2) + 2 * ∑ i : ZMod N, ρ i ^ 2 +
      fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) Q w w := by
    have h := pen_hessian_split hm hmN hx hu hxu ρ β w (fun i => (hwn i).1) (fun i => (hwn i).2)
    rw [← hBdec] at h
    exact h
  have hEw := hessian_high_ge hm hmN hx hu hxu hE2 a b hab_a hab_b (Ico (m + 1) (M + 1))
    (fun j hj => by have := Finset.mem_Ico.mp hj; omega)
  rw [← hweq] at hEw
  set ν := Real.cos (2 * π * (m + 1 : ℕ) / N) - c with hν
  have hνneg : ν < 0 := by
    have := cos_ang_strict (N := N) (show m < m + 1 by omega) (by omega)
    rw [hν, hc]
    linarith
  have hk2 : 0 < 2 * N * G c * ν := by
    have e : 2 * (N : ℝ) * G c * ν = (2 * N) * (G c * ν) := by ring
    rw [e]
    exact mul_pos (by positivity) (mul_pos_of_neg_of_neg hG hνneg)
  have hpA := pair_self_nonneg A
  have hpw := pair_self_nonneg w
  have hs1 : 0 ≤ ∑ i : ZMod N, (β (i + 1) - β i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs2 : 0 ≤ ∑ i : ZMod N, ρ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hAneg : H A A ≤ 2 * N * G c * μ * pair A A := by rw [hAA]; exact hEA
  have hwpos : 2 * N * G c * ν * pair w w ≤ fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) Q w w :=
    hEw
  have hHA : H A A ≤ 0 := hAneg.trans (mul_nonpos_of_nonpos_of_nonneg hk1.le hpA)
  have hNs1 : 0 ≤ (N : ℝ) * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2 := mul_nonneg hN0.le hs1
  have hwnn : 0 ≤ 2 * N * G c * ν * pair w w := mul_nonneg hk2.le hpw
  have hEwnn : 0 ≤ fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) Q w w := hwnn.trans hwpos
  have hHB : 0 ≤ H B B := by
    rw [hBB]
    linarith
  refine ⟨by rw [hF]; linarith, fun h0 => ?_⟩
  rw [hF] at h0
  have hA0' : H A A = 0 := by linarith
  have hB0' : H B B = 0 := by linarith
  -- all parts vanish
  have hpA0 : pair A A = 0 := by
    have : 2 * N * G c * μ * pair A A ≥ 0 := by linarith
    have h1 : pair A A ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have := mul_neg_of_neg_of_pos hk1 hcon
      linarith
    linarith
  have hA0 : A = 0 := pair_eq_zero hpA0
  rw [hBB] at hB0'
  have hEw0 : fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) Q w w = 0 := by linarith
  have hpw0 : pair w w = 0 := by
    have : 2 * N * G c * ν * pair w w ≤ 0 := by linarith
    have h1 : pair w w ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have := mul_pos hk2 hcon
      linarith
    linarith
  have hw0 : w = 0 := pair_eq_zero hpw0
  have hρ0 : ∀ i, ρ i = 0 := by
    have h2 : ∑ i : ZMod N, ρ i ^ 2 = 0 := by linarith
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (ρ j)).mp h2 i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have hβ0 : ∀ i, β (i + 1) = β i := by
    have h2 : ∑ i : ZMod N, (β (i + 1) - β i) ^ 2 = 0 := by
      have h3 : (N : ℝ) * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2 = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hN0.ne'
      · exact h4
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (β (j + 1) - β j)).mp h2 i
      (Finset.mem_univ i)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  -- β is constant
  have hβc : ∀ i, β i = β 0 := by
    have hk : ∀ k : ℕ, β (k : ZMod N) = β 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.cast_succ, hβ0, ih]
    intro i
    rw [← ZMod.natCast_zmod_val i]
    exact hk _
  -- B is a multiple of the rotation
  have hBt : B = β 0 • regular N m z.2 (-z.1) := by
    rw [hBdec, hw0, add_zero, ← tang_eq_regular]
    funext i
    simp only [Pi.add_apply, scaleL_apply, Pi.smul_apply]
    have e1 : ⟪Q i, B i⟫ = 0 := hρ0 i
    have e2 : ⟪tang N m z.1 z.2 i, B i⟫ = β 0 := hβc i
    rw [e1, e2, zero_smul, zero_add]
  -- the frequency-m coefficients of B
  have hVk : V ∈ kern (n := n) (N := N) m := ξ.2.2
  have hAk : A ∈ kern (n := n) (N := N) m := negV_mem_kern hm hmN z V
  rw [mem_kern] at hVk hAk
  have hAm : coefA m B = ξ.1.1 • z.1 := by
    rw [hB, lin_apply, sub_eq_add_neg, coefA_add, coefA_add, ← neg_one_smul ℝ A, coefA_smul,
      coefA_regular hm hmN hmN, if_pos rfl, ← hV, hVk.1, hAk.1]
    simp
  have hBm : coefB m B = ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2 := by
    rw [hB, lin_apply, sub_eq_add_neg, coefB_add, coefB_add, ← neg_one_smul ℝ A, coefB_smul,
      coefB_regular hm hmN hmN, if_pos rfl, ← hV, hVk.2, hAk.2]
    simp
  have hAm' : coefA m B = β 0 • z.2 := by
    rw [hBt, coefA_smul, coefA_regular hm hmN hmN, if_pos rfl]
  have hBm' : coefB m B = -(β 0 • z.1) := by
    rw [hBt, coefB_smul, coefB_regular hm hmN hmN, if_pos rfl, smul_neg]
  have hxx : ⟪z.1, z.1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪z.2, z.2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪z.2, z.1⟫ = 0 := by rw [real_inner_comm, hxu]
  have e1 : ξ.1.1 • z.1 = β 0 • z.2 := hAm.symm.trans hAm'
  have hτ1 : ξ.1.1 = 0 := by
    have := congrArg (fun v => ⟪z.1, v⟫) e1
    simp only [real_inner_smul_right, hxx, hxu] at this
    linarith
  have hβ00 : β 0 = 0 := by
    have := congrArg (fun v => ⟪z.2, v⟫) e1
    simp only [real_inner_smul_right, hux, huu] at this
    linarith
  have e2 : ξ.1.2.1 • z.1 + ξ.1.2.2 • z.2 = -(β 0 • z.1) := hBm.symm.trans hBm'
  rw [hβ00, zero_smul, neg_zero] at e2
  have hτ2 : ξ.1.2.1 = 0 := by
    have := congrArg (fun v => ⟪z.1, v⟫) e2
    simp only [inner_add_right, real_inner_smul_right, hxx, hxu, inner_zero_right] at this
    linarith
  have hτ3 : ξ.1.2.2 = 0 := by
    have := congrArg (fun v => ⟪z.2, v⟫) e2
    simp only [inner_add_right, real_inner_smul_right, hux, huu, inner_zero_right] at this
    linarith
  -- B = 0, hence V = A = 0
  have hB00 : B = 0 := by rw [hBt, hβ00, zero_smul]
  have hlin0 : lin m z ξ = 0 := by
    have : lin m z ξ = A + B := by rw [hB]; abel
    rw [this, hA0, hB00, add_zero]
  have hV0 : V = 0 := by
    rw [lin_apply, hτ1, hτ2, hτ3] at hlin0
    simp only [zero_smul, add_zero] at hlin0
    have hr0 : regular N m (0 : Ambient n) 0 = 0 := by
      funext i
      simp [regular, circ]
    rw [hr0, zero_add] at hlin0
    exact hlin0
  refine Prod.ext (Prod.ext hτ1 (Prod.ext hτ2 hτ3)) (Subtype.ext ?_)
  exact hV0

end Main

end Definite

end

end Finsler.RoundChart
