module

public import Finsler.Geometry.RoundLoopFourier
public import Finsler.Topology.EvalFunctionals
public import Finsler.Topology.OrientedCritical
public import Finsler.Topology.BorelLocalK
public import Finsler.Geometry.DiagonalGeometry

/-! The averaged evaluation near the critical loops of an even level of the round sphere.

A tangent critical loop of the round metric with energy (2πm)², m even, takes the same value at
the times 0 and 1/2: fine samples of the loop, with an even number N = 2K of samples, form a
regular m-gon, whose vertices 0 and K agree because m is even. Hence a loop uniformly within 1/4
of such a critical loop is never antipodal to its half rotation at the time 0, and on a set of
such loops the averaged evaluation ẽ(u) = normalize(u(0) + u(1/2)) is defined. It is invariant
under the reversal and the half rotation, and it is never antipodal to the evaluation at 0. -/

@[expose] public section

namespace Finsler.RoundEven

open CategoryTheory Set Topology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction Finsler.BorelK
open Finsler.RoundCoords Finsler.Geometry Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.SobolevCurveVariation Finsler.RoundLoopFourier Finsler.OrientedCritical
open Finsler.MilnorHomotopy Finsler.MilnorEquivariance Finsler.BorelLoop Finsler.BorelPair
open Finsler.AvoidPoint Finsler.BorelLocalK
open scoped RealInnerProductSpace Real

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Critical loops of even order -/

/-- **A tangent critical loop of the round metric of even order m takes the same value at the
times 0 and 1/2.** -/
theorem half_eq_of_critical {m : ℕ} (hm : 0 < m) (he : Even m) {u : SphereLoop n}
    (hu : TangentCritical (roundMetric n) u)
    (hE : SobolevEnergy.energy (roundMetric n) u = (2 * π * m) ^ 2) :
    rep u (1 / 2) = rep u 0 := by
  have hπ : 0 < π := Real.pi_pos
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hEpos : 0 < SobolevEnergy.energy (roundMetric n) u := by rw [hE]; positivity
  obtain ⟨g, rfl⟩ :=
    (SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic _ u hEpos).mp hu
  set v := SmoothSobolev.ofSmooth g.loop with hv
  obtain ⟨S⟩ := PolygonModel.exists_segmentData (roundMetric n)
  obtain ⟨N₀, hN₀⟩ := PolygonModel.sample_closedGeodesic S g
  have huc : UniformContinuousOn (rep v) (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (rep_continuousOn v)
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.mp huc (1 / 16) (by norm_num)
  obtain ⟨K, hK⟩ := exists_nat_gt (max (N₀ : ℝ) (1 / δ))
  have hK1 : (N₀ : ℝ) < K := lt_of_le_of_lt (le_max_left _ _) hK
  have hK2 : 1 / δ < K := lt_of_le_of_lt (le_max_right _ _) hK
  have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK2
  have hKnat : 0 < K := by exact_mod_cast hKpos
  set N := 2 * K with hNdef
  have hNK : (K : ℝ) ≤ N := by
    rw [hNdef]
    push_cast
    linarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hKpos hNK
  have hN1 : (N₀ : ℝ) < N := lt_of_lt_of_le hK1 hNK
  have hN2 : 1 / δ < N := lt_of_lt_of_le hK2 hNK
  have hNnat : 0 < N := by omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨-, hcrit, hpE⟩ := hN₀ N (by exact_mod_cast hN1.le)
  -- oscillation on intervals of length 1/N
  have hosc : ∀ s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖rep v t - rep v s‖ ≤ 1 / 16 := by
    intro s t hs ht hst
    have hlt : dist t s < δ := by
      rw [Real.dist_eq]
      have : 1 / (N : ℝ) < δ := by
        rw [div_lt_iff₀ hNpos]
        rw [div_lt_iff₀ hδ] at hN2
        linarith
      linarith
    have := hδc t ht s hs hlt
    rw [dist_eq_norm] at this
    exact this.le
  -- the samples are a short polygon without antipodal edges
  have hsamp : ∀ i : ZMod N, (samplePoly N v i : Ambient n) = sampleN N v i := fun _ => rfl
  have hna : ∀ i : ZMod N, ⟪(samplePoly N v i : Ambient n), samplePoly N v (i + 1)⟫ ≠ -1 := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < N ∧ (k : ZMod N) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    rw [hsamp, hsamp, sampleN_natCast v hk, sampleN_natCast_succ v hk] at hi
    have hkN : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by
      rw [div_le_one hNpos]; exact_mod_cast hk.le⟩
    have hk1N : ((k : ℝ) + 1) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by
      rw [div_le_one hNpos]; exact_mod_cast hk⟩
    have hd : ‖rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N)‖ ≤ 1 / 16 := by
      apply hosc _ _ hkN hk1N
      rw [show ((k : ℝ) + 1) / N - k / N = 1 / N by field_simp; ring,
        abs_of_pos (by positivity)]
    have h1 := norm_rep v hkN
    have h2 := norm_rep v hk1N
    have hsq : ‖rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N)‖ ^ 2 = 4 := by
      rw [@norm_sub_sq_real, h1, h2, real_inner_comm, hi]
      ring
    nlinarith [norm_nonneg (rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N))]
  have hEN : polyEnergy (roundMetric n) N (fun i => (samplePoly N v i : Ambient n)) =
      (2 * π * m) ^ 2 := by
    rw [samplePoly_coe, hpE, hE]
  obtain ⟨x, y, m', hx, hy, hxy, hm', hm'N, hq⟩ :=
    RoundPolygon.regular_of_polyCritical hna hcrit (by rw [hEN]; positivity)
  have hreg : sampleN N v = RoundPolygon.regular N m' x y := by
    funext i
    obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < N ∧ (k : ZMod N) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    rw [← hsamp, hq k, RoundPolygon.regular_natCast]
    rfl
  have hmm : m' = m := by
    have h1 := RoundPolygon.polyEnergy_regular (N := N) hm'N hx hy hxy
    rw [← hreg, ← samplePoly_coe, hEN] at h1
    have h2 : (m : ℝ) = m' := by
      have h3 : (2 * π * m) = 2 * π * m' := (sq_eq_sq₀ (by positivity) (by positivity)).mp h1
      have h4 : (2 * π) * (m : ℝ) = (2 * π) * m' := by linarith
      exact mul_left_cancel₀ (by positivity) h4
    exact_mod_cast h2.symm
  subst hmm
  -- the samples at the times 1/2 and 0
  have hKN : K < N := by omega
  have e1 : rep v (1 / 2) = (samplePoly N v (K : ZMod N) : Ambient n) := by
    rw [hsamp, sampleN_natCast v hKN]
    congr 1
    rw [hNdef]
    push_cast
    field_simp
  have e0 : rep v 0 = (samplePoly N v ((0 : ℕ) : ZMod N) : Ambient n) := by
    rw [hsamp, sampleN_natCast v hNnat]
    congr 1
    simp
  rw [e1, e0, hq K, hq 0]
  have hang : 2 * π * m' / N * K = π * m' := by
    rw [hNdef]
    push_cast
    field_simp
  obtain ⟨k, hk⟩ := he
  have hc : Real.cos (π * m') = 1 := by
    rw [hk]
    push_cast
    rw [show π * ((k : ℝ) + k) = (k : ℤ) * (2 * π) by push_cast; ring]
    exact Real.cos_int_mul_two_pi k
  have hs : Real.sin (π * m') = 0 := by
    rw [mul_comm]
    exact Real.sin_nat_mul_pi m'
  rw [hang, hc, hs]
  simp

/-! ### The sum of the points at the times 0 and 1/2 -/

/-- The sum of the points of a loop at the times 0 and 1/2. -/
def sumH (u : SphereLoop n) : Ambient n := (pt u 0 : Ambient n) + (pt u (1 / 2) : Ambient n)

theorem sumH_continuous : Continuous (sumH (n := n)) :=
  (EvalFunctionals.pt_coe_continuous 0).add (EvalFunctionals.pt_coe_continuous (1 / 2))

theorem sumH_reverse (u : SphereLoop n) : sumH (reverseSphere u) = sumH u := by
  unfold sumH
  rw [EvalFunctionals.pt_reverse_neg, EvalFunctionals.pt_reverse_neg, neg_zero,
    pt_eq_of_sub_int u (x := -(1 / 2)) (y := 1 / 2) 1 (by norm_num)]

theorem sumH_half (u : SphereLoop n) : sumH (half +ᵥ u) = sumH u := by
  unfold sumH
  rw [pt_vadd, pt_vadd, zero_add, show (1 : ℝ) / 2 + 1 / 2 = 0 + 1 by norm_num, pt_add_one,
    add_comm]

/-- **Near the critical loops of an even level a loop is never antipodal to its half rotation at
the time 0.** -/
theorem tube_sumH_ne {m : ℕ} (hm : 0 < m) (he : Even m) {u : SphereLoop n}
    (hu : (u : Loops n) ∈ tube (roundMetric n) (2 * π * m) (1 / 4)) : sumH u ≠ 0 := by
  obtain ⟨γ, hγ, hE, hd⟩ := hu
  have hγh := half_eq_of_critical hm he hγ hE
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h12 : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have d0 := hd 0 h0
  have d12 := hd (1 / 2) h12
  have hn0 : ‖rep u 0‖ = 1 := norm_rep u h0
  unfold sumH
  rw [pt_coe u h0, pt_coe u h12]
  intro hs
  have hneg : rep u (1 / 2) = -rep u 0 := eq_neg_of_add_eq_zero_right hs
  have key : ‖rep u (1 / 2) - rep u 0‖ ≤ 1 / 2 := by
    calc ‖rep u (1 / 2) - rep u 0‖ = ‖(rep u (1 / 2) - rep γ (1 / 2)) - (rep u 0 - rep γ 0)‖ := by
          rw [hγh]
          congr 1
          abel
      _ ≤ ‖rep u (1 / 2) - rep γ (1 / 2)‖ + ‖rep u 0 - rep γ 0‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add d12 d0
      _ = 1 / 2 := by norm_num
  rw [hneg, show -rep u 0 - rep u 0 = (-2 : ℝ) • rep u 0 by rw [neg_smul, two_smul]; abel,
    norm_smul, hn0] at key
  norm_num at key

/-! ### The averaged evaluation -/

/-- **The averaged evaluation** ẽ(u) = normalize(u(0) + u(1/2)) on a set of loops on which the
sum does not vanish. -/
def evH (t : Set (Loops n)) (ht : ∀ u : SphereLoop n, u ∈ t → sumH u ≠ 0) :
    TopCat.of t ⟶ Finsler.BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun u => Finsler.DiagonalGeometry.normalize (sumH (u : SphereLoop n)) (ht _ u.2), by
    have hc : Continuous fun u : t => sumH (u : SphereLoop n) :=
      sumH_continuous.comp continuous_subtype_val
    have hi : Continuous fun u : t => ‖sumH (u : SphereLoop n)‖⁻¹ :=
      hc.norm.inv₀ fun u => norm_ne_zero_iff.mpr (ht _ u.2)
    exact (hi.smul hc).subtype_mk _⟩

/-- The evaluation at 0 on a set of loops. -/
def evT (t : Set (Loops n)) : TopCat.of t ⟶ Finsler.BorelEvaluation.sphere n :=
  TopCat.ofHom ⟨fun u => Finsler.BorelEvaluation.eval n u.val,
    (Finsler.BorelEvaluation.eval n).continuous.comp continuous_subtype_val⟩

theorem eval_coe (u : SphereLoop n) :
    (Finsler.BorelEvaluation.eval n u : Ambient n) = (pt u 0 : Ambient n) :=
  congrArg Subtype.val (pt_eq_representative u Finsler.BorelEvaluation.zero).symm

/-- A unit vector is never antipodal to the normalized sum of itself with a unit vector. -/
theorem ne_neg_normalize {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hs : p + q ≠ 0) :
    p ≠ -(‖p + q‖⁻¹ • (p + q)) := by
  intro h
  set s := p + q with hsd
  have h1 : ⟪p, s⟫ = -(‖s‖⁻¹ * ‖s‖ ^ 2) := by
    rw [h, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have h2 : 0 ≤ ⟪p, s⟫ := by
    rw [hsd, inner_add_right, real_inner_self_eq_norm_sq, hp]
    have := abs_real_inner_le_norm p q
    rw [hp, hq] at this
    have := neg_abs_le ⟪p, q⟫
    linarith
  have h3 : 0 < ‖s‖⁻¹ * ‖s‖ ^ 2 := by
    have := norm_pos_iff.mpr hs
    positivity
  linarith

/-- **The evaluation at 0 is never antipodal to the averaged evaluation.** -/
theorem evT_ne_neg (t : Set (Loops n)) (ht : ∀ u : SphereLoop n, u ∈ t → sumH u ≠ 0)
    (u : TopCat.of t) : (evT t u : Ambient n) ≠ -(evH t ht u : Ambient n) := by
  change (Finsler.BorelEvaluation.eval n (u : SphereLoop n) : Ambient n) ≠
    -(‖sumH (u : SphereLoop n)‖⁻¹ • sumH (u : SphereLoop n))
  rw [eval_coe]
  exact ne_neg_normalize (Finsler.DiagonalGeometry.sphere_norm _)
    (Finsler.DiagonalGeometry.sphere_norm _) (ht _ u.2)

variable {s t : Set (Loops n)} (hst : s ⊆ t)
  (hs : ∀ u : SphereLoop n, u ∈ s → reverseSphere u ∈ s)
  (ht : ∀ u : SphereLoop n, u ∈ t → reverseSphere u ∈ t)
  (hhs : ∀ u : SphereLoop n, u ∈ s → half +ᵥ u ∈ s)
  (hht : ∀ u : SphereLoop n, u ∈ t → half +ᵥ u ∈ t)
  (hX : ∀ u : SphereLoop n, u ∈ t → sumH u ≠ 0)

/-- The averaged evaluation is invariant under the reversal. -/
theorem evH_rev : TopPair.Hom.fst (revSub hst hs ht) ≫ evH t hX = evH t hX := by
  ext u : 1
  apply Subtype.ext
  change ‖sumH (reverseSphere u.1)‖⁻¹ • sumH (reverseSphere u.1) = ‖sumH u.1‖⁻¹ • sumH u.1
  rw [sumH_reverse]

/-- The averaged evaluation is invariant under the half rotation. -/
theorem evH_half : TopPair.Hom.fst (halfSub hst hhs hht) ≫ evH t hX = evH t hX := by
  ext u : 1
  apply Subtype.ext
  change ‖sumH (half +ᵥ u.1)‖⁻¹ • sumH (half +ᵥ u.1) = ‖sumH u.1‖⁻¹ • sumH u.1
  rw [sumH_half]

end

end Finsler.RoundEven
