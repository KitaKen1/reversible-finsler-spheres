module

public import Finsler.Geometry.SamplePhase
public import Finsler.Geometry.AmbientRotation
public import Finsler.Analysis.FormSemicontinuity
public import Finsler.Analysis.SmallPeriods

/-! The nullities and indices of the samples of a closed geodesic do not depend on the phase.
Along a continuous family of short stationary polygons without zero edges the second derivative
of the penalized energy is continuous, so the nullity is upper semicontinuous, and if the
nullity is constant on a preconnected family the index is constant. The polygon of K samples
of a closed geodesic rotated by the phase a + 1/K is the rotation of the vertices of the polygon
of samples at the phase a, and the nullity is invariant under rotation of the vertices; with
the doubling theorem at all phases, the nullity of the d-fold iterate of the polygon of 2 N
samples has the periods 1 / (2^j 2 N) in the phase, for all j. An upper semicontinuous function
with arbitrarily small periods is constant. Hence, for N large, the nullities and the indices
of all iterates of the polygon of 2 N samples of a closed geodesic are independent of the
phase. -/

@[expose] public section

namespace Finsler.PhaseNullity

open Module Filter Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth Finsler.PolygonIterate
open Finsler.PolygonHessian Finsler.PolygonDescent Finsler.AmbientPenalty Finsler.AmbientDescent
open Finsler.AmbientHessian Finsler.AmbientSymmetry Finsler.AmbientNormalIndex
open Finsler.AmbientNullity Finsler.AmbientNormalNondeg Finsler.PolygonChart
open Finsler.PolygonIterateReduction Finsler.PolygonSampling Finsler.PolygonModel
open Finsler.SmoothSobolev Finsler.PolygonGeodesic Finsler.SamplePhase Finsler.AmbientRotation
open Finsler.FormSemicontinuity Finsler.SmallPeriods
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

/-! ### Continuous families of stationary polygons -/

section Family

variable {n N : ℕ} [NeZero N] (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {Θ : Type*} [TopologicalSpace Θ] {q : Θ → ZMod N → Sphere n}
  (hcont : Continuous fun θ => amb (q θ)) (hq : ∀ θ, ShortPolygon δ (q θ))
  (hne : ∀ θ i, q θ (i + 1) ≠ q θ i)

include hδ hcont hq hne in
/-- The second derivative of the penalized energy along a continuous family of short polygons
without zero edges is continuous. -/
theorem sndDeriv_continuous (lam : ℝ) :
    Continuous fun p : Θ × (ZMod N → Ambient n) × (ZMod N → Ambient n) =>
      fderiv ℝ (fderiv ℝ (pen F N lam)) (amb (q p.1)) p.2.1 p.2.2 := by
  have h1 : Continuous fun θ => fderiv ℝ (fderiv ℝ (pen F N lam)) (amb (q θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hf := pen_contDiffAt_two F hδ (hq θ) (hne θ) lam
    have h2 : ContinuousAt (fderiv ℝ (fderiv ℝ (pen F N lam))) (amb (q θ)) :=
      ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ContinuousAt.comp (g := fderiv ℝ (fderiv ℝ (pen F N lam)))
      (f := fun θ => amb (q θ)) h2 hcont.continuousAt
  exact ((h1.comp continuous_fst).clm_apply (continuous_fst.comp continuous_snd)).clm_apply
    (continuous_snd.comp continuous_snd)

variable (hc : ∀ θ, PolyCritical F N (q θ))

include hδ hcont hq hne hc in
/-- The nullity is upper semicontinuous along a continuous family of short stationary polygons
without zero edges. -/
theorem isOpen_nullity_le (k : ℕ) : IsOpen {θ : Θ | nullity F (q θ) ≤ k} := by
  have hB := sndDeriv_continuous F hδ hcont hq hne 1
  have hsym : ∀ θ (v w : ZMod N → Ambient n),
      (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂ v w =
      (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂ w v := fun θ v w =>
    ((pen_contDiffAt_two F hδ (hq θ) (hne θ) 1).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq v w
  have h := isOpen_finrank_ker_le
    (B := fun θ => (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂) hB hsym k
  have he : ∀ θ, finrank ℝ (LinearMap.ker
      (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂) = nullity F (q θ) :=
    fun θ => finrank_ker_sndDeriv_pen F hδ (hq θ) (hne θ) (hc θ) one_pos
  simpa only [he] using h

include hδ hcont hq hne hc in
/-- If the nullity is constant along a continuous preconnected family of short stationary
polygons without zero edges, the index is constant. -/
theorem index_eq_of_nullity_eq [PreconnectedSpace Θ]
    (hk : ∀ θ θ', nullity F (q θ) = nullity F (q θ')) (θ θ' : Θ)
    (hs : (hessian F (q θ)).toLinearMap.IsSymmetric)
    (hs' : (hessian F (q θ')).toLinearMap.IsSymmetric) :
    index F (q θ) hs = index F (q θ') hs' := by
  have hB := sndDeriv_continuous F hδ hcont hq hne 1
  have hsym : ∀ θ (v w : ZMod N → Ambient n),
      (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂ v w =
      (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂ w v := fun θ v w =>
    ((pen_contDiffAt_two F hδ (hq θ) (hne θ) 1).isSymmSndFDerivAt
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_num)).eq v w
  have he : ∀ θ, finrank ℝ (LinearMap.ker
      (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂) = nullity F (q θ) :=
    fun θ => finrank_ker_sndDeriv_pen F hδ (hq θ) (hne θ) (hc θ) one_pos
  have h := sigNeg_eq_of_finrank_ker_eq
    (B := fun θ => (fderiv ℝ (fderiv ℝ (pen F N 1)) (amb (q θ))).toLinearMap₁₂) hB hsym
    (fun θ θ' => by rw [he, he]; exact hk θ θ') θ θ'
  rw [← sigNeg_sndQuad_pen F hδ (hq θ) (hne θ) (hc θ) zero_le_one hs,
    ← sigNeg_sndQuad_pen F hδ (hq θ') (hne θ') (hc θ') zero_le_one hs']
  exact h

end Family

/-! ### Samples of the rotations of a loop -/

section Samples

variable {n : ℕ}

/-- A rotation only depends on the fractional part of the phase. -/
theorem shift_fract (γ : Finsler.Loops.SmoothLoop n) (a : ℝ) :
    Finsler.Loops.shift γ a = Finsler.Loops.shift γ (Int.fract a) := by
  apply Finsler.Loops.loop_ext
  intro t
  change γ (t + a) = γ (t + Int.fract a)
  have h : t + a = t + Int.fract a + ((⌊a⌋ : ℤ) : ℝ) * 1 := by
    rw [mul_one]
    linarith [Int.floor_add_fract a]
  rw [h]
  exact (γ.periodic.int_mul ⌊a⌋) (t + Int.fract a)

/-- The samples of a rotated loop. -/
theorem samplePoly_shift_apply (γ : Finsler.Loops.SmoothLoop n) (a : ℝ) {K : ℕ} [NeZero K]
    (j : ZMod K) :
    ((samplePoly K (ofSmooth (Finsler.Loops.shift γ a)) j : Sphere n) : Ambient n) =
      γ ((j.val : ℝ) / K + a) := by
  have hk : j.val < K := ZMod.val_lt j
  have h := sampleN_ofSmooth_natCast (Finsler.Loops.shift γ a) hk
  rw [ZMod.natCast_zmod_val] at h
  exact h

/-- The polygon of K samples at the phase a + 1/K is the rotation of the vertices of the polygon
of samples at the phase a. -/
theorem samplePoly_shift_add (γ : Finsler.Loops.SmoothLoop n) (a : ℝ) (K : ℕ) [NeZero K] :
    samplePoly K (ofSmooth (Finsler.Loops.shift γ (a + 1 / (K : ℝ)))) =
      rotP 1 (samplePoly K (ofSmooth (Finsler.Loops.shift γ a))) := by
  funext j
  apply Subtype.ext
  have hk : j.val < K := ZMod.val_lt j
  have h1 := sampleN_ofSmooth_natCast (Finsler.Loops.shift γ (a + 1 / (K : ℝ))) hk
  have h2 := sampleN_ofSmooth_natCast_succ (Finsler.Loops.shift γ a) hk
  rw [ZMod.natCast_zmod_val] at h1 h2
  change sampleN K (ofSmooth (Finsler.Loops.shift γ (a + 1 / (K : ℝ)))) j =
    sampleN K (ofSmooth (Finsler.Loops.shift γ a)) (j + 1)
  rw [h1, h2]
  change ((γ ((j.val : ℝ) / K + (a + 1 / (K : ℝ))) : Sphere n) : Ambient n) =
    γ (((j.val : ℝ) + 1) / K + a)
  congr 2
  ring

/-- The iterates of the polygons of samples of the rotations of a loop depend continuously on
the phase. -/
theorem amb_iterate_sample_continuous (γ : Finsler.Loops.SmoothLoop n) (d K : ℕ) [NeZero d]
    [NeZero K] :
    Continuous fun a : ℝ =>
      amb (iterate d K (samplePoly K (ofSmooth (Finsler.Loops.shift γ a)))) := by
  refine continuous_pi fun i => ?_
  have he : (fun a : ℝ =>
      amb (iterate d K (samplePoly K (ofSmooth (Finsler.Loops.shift γ a)))) i) =
      fun a : ℝ => ((γ (((red d K i).val : ℝ) / K + a) : Sphere n) : Ambient n) := by
    funext a
    exact samplePoly_shift_apply γ a (red d K i)
  rw [he]
  exact continuous_subtype_val.comp
    (γ.smooth.continuous.comp (continuous_const.add continuous_id))

variable {F : ReversibleMetric n}

/-- The sample facts hold for all rotations of a closed geodesic by real phases, uniformly. -/
theorem exists_sample_facts_all (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ K₀ : ℕ, ∀ a : ℝ, ∀ K : ℕ, K₀ ≤ K → ∀ [NeZero K],
      SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) K := by
  obtain ⟨K₀, h⟩ := exists_sample_facts M g
  refine ⟨K₀, fun a K hK _ => ?_⟩
  rw [shift_fract]
  exact h (Int.fract a) ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩ K hK

/-- The nullity of the d-fold iterate of the polygon of 2 N samples has the period
1 / (2^j 2 N) in the phase. -/
theorem nullity_shift_period (M : SegmentData F) (g : Finsler.Geodesics.ClosedGeodesic F)
    {K₀ : ℕ} (hK₀ : ∀ a : ℝ, ∀ K : ℕ, K₀ ≤ K → ∀ [NeZero K],
      SampleFacts M (ofSmooth (Finsler.Loops.shift g.loop a)) K)
    (d : ℕ) [NeZero d] (j : ℕ) : ∀ N : ℕ, K₀ ≤ N → ∀ [NeZero N], ∀ a : ℝ,
      nullity F (iterate d (2 * N) (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop
        (a + 1 / ((2 : ℝ) ^ j * ((2 * N : ℕ) : ℝ))))))) =
      nullity F (iterate d (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) := by
  induction j with
  | zero =>
    intro N hN _ a
    have hK : K₀ ≤ 2 * N := hN.trans (Nat.le_mul_of_pos_left N two_pos)
    obtain ⟨hq, hne, -, -, hc, -, -⟩ := hK₀ a (2 * N) hK
    have h1 := iterate_rotP d 1 (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))
    rw [Nat.cast_one, Nat.cast_one] at h1
    rw [pow_zero, one_mul, samplePoly_shift_add, h1]
    exact nullity_rotP F M.smooth (shortPolygon_iterate d (2 * N) hq) (iterate_ne d (2 * N) hne)
      (polyCritical_iterate d F M.smooth hq hne hc) 1
  | succ j ih =>
    intro N hN _ a
    have hN1 : K₀ ≤ 2 * N := hN.trans (Nat.le_mul_of_pos_left N two_pos)
    have hN2 : K₀ ≤ 2 * (2 * N) := hN1.trans (Nat.le_mul_of_pos_left (2 * N) two_pos)
    have hN4 : K₀ ≤ 4 * N := hN.trans (Nat.le_mul_of_pos_left N (by norm_num))
    have hdbl : ∀ b : ℝ, nullity F (iterate d (2 * (2 * N))
        (samplePoly (2 * (2 * N)) (ofSmooth (Finsler.Loops.shift g.loop b)))) =
        nullity F (iterate d (2 * N)
          (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop b)))) := fun b =>
      nullity_iterate_double_of_facts M _ N (hK₀ b N hN) (hK₀ b (2 * N) hN1)
        (hK₀ b (2 * (2 * N)) hN2) (hK₀ b (4 * N) hN4) d
    have hτ : (1 : ℝ) / ((2 : ℝ) ^ (j + 1) * ((2 * N : ℕ) : ℝ)) =
        1 / ((2 : ℝ) ^ j * ((2 * (2 * N) : ℕ) : ℝ)) := by
      push_cast
      ring
    have e1 := hdbl (a + 1 / ((2 : ℝ) ^ (j + 1) * ((2 * N : ℕ) : ℝ)))
    have e2 := hdbl a
    rw [← e1, ← e2, hτ]
    exact ih (2 * N) hN1 a

/-- **The nullities and the indices of the iterates of the samples of a closed geodesic do not
depend on the phase.** For N large, every d ≥ 1 and all real phases a and a', the d-fold
iterates of the polygons of 2 N samples of the closed geodesic rotated by a and by a' have the
same nullity and the same index. -/
theorem exists_phase_invariance (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (d : ℕ) [NeZero d] (a a' : ℝ),
      nullity F (iterate d (2 * N)
          (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) =
        nullity F (iterate d (2 * N)
          (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a')))) ∧
      ∀ (hs : (hessian F (iterate d (2 * N)
          (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))))).toLinearMap.IsSymmetric)
        (hs' : (hessian F (iterate d (2 * N) (samplePoly (2 * N)
          (ofSmooth (Finsler.Loops.shift g.loop a'))))).toLinearMap.IsSymmetric),
        index F (iterate d (2 * N)
            (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) hs =
          index F (iterate d (2 * N)
            (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a')))) hs' := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts_all M g
  refine ⟨K₀, fun N hN _ d _ => ?_⟩
  have hK : K₀ ≤ 2 * N := hN.trans (Nat.le_mul_of_pos_left N two_pos)
  have hcont := amb_iterate_sample_continuous g.loop d (2 * N)
  have hq : ∀ b : ℝ, ShortPolygon M.δ (iterate d (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop b)))) := fun b =>
    shortPolygon_iterate d (2 * N) (hK₀ b (2 * N) hK).1
  have hne : ∀ (b : ℝ) i, iterate d (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop b))) (i + 1) ≠
      iterate d (2 * N) (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop b))) i :=
    fun b => iterate_ne d (2 * N) (hK₀ b (2 * N) hK).2.1
  have hc : ∀ b : ℝ, PolyCritical F (d * (2 * N)) (iterate d (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop b)))) := fun b =>
    polyCritical_iterate d F M.smooth (hK₀ b (2 * N) hK).1 (hK₀ b (2 * N) hK).2.1
      (hK₀ b (2 * N) hK).2.2.2.2.1
  have hopen : ∀ k, IsOpen {b : ℝ | nullity F (iterate d (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop b)))) ≤ k} := fun k =>
    isOpen_nullity_le F M.smooth hcont hq hne hc k
  have hper : ∀ ε > 0, ∃ τ, 0 < τ ∧ τ < ε ∧ Function.Periodic (fun b : ℝ =>
      nullity F (iterate d (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop b))))) τ := by
    intro ε hε
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / ε) (one_lt_two (α := ℝ))
    have hKpos : (1 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_neZero (2 * N)
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have hprod : (0 : ℝ) < 2 ^ j * ((2 * N : ℕ) : ℝ) := mul_pos h2j (by linarith)
    refine ⟨1 / ((2 : ℝ) ^ j * ((2 * N : ℕ) : ℝ)), div_pos one_pos hprod, ?_,
      fun b => nullity_shift_period M g hK₀ d j N hN b⟩
    rw [div_lt_iff₀ hprod]
    rw [div_lt_iff₀ hε] at hj
    nlinarith
  have hconst : ∀ a a' : ℝ, nullity F (iterate d (2 * N)
      (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) =
      nullity F (iterate d (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a')))) := fun a a' =>
    eq_of_small_periods hopen hper a' a
  intro a a'
  exact ⟨hconst a a', fun hs hs' =>
    index_eq_of_nullity_eq F M.smooth hcont hq hne hc hconst a a' hs hs'⟩

end Samples

end

end Finsler.PhaseNullity
