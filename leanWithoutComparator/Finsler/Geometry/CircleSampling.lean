module

public import Finsler.Geometry.CircleFrameField
public import Finsler.Geometry.LabelPack

/-! Samples of the iterates of a loop. Let the polygons of N samples of all rotations of a loop γ
have the sample facts for a segment datum (short, and the broken geodesic of the samples is the
rotated loop). Then the segment of the datum between γ(x) and γ(x + 1/N) is γ on [x, x + 1/N],
for every real x. Hence for K = k N the polygons of K samples of the rotations of the k-fold
iterate of γ are short, and their broken geodesics are the rotated iterates. The samples of the
rotated iterates are the iterates of the root polygons: for k = s m and K = m (s (2 N)) the
polygon of K samples of the rotation by a of the k-fold iterate of a closed geodesic is the m-fold
iterate of its root polygon at the phase k a. -/

@[expose] public section

namespace Finsler.CircleSampling

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.PolygonLoop Finsler.PolygonSampling Finsler.PolygonModel Finsler.SamplePhase
open Finsler.SmoothSobolev Finsler.Loops Finsler.PhaseNullity Finsler.PolygonIterate
open Finsler.PiecewiseC1 Finsler.GeodesicFrames Finsler.AmbientSymmetry Finsler.PolygonDescent
open Set Filter

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} (M : SegmentData F) (γ : SmoothLoop n)

/-- A loop takes the same value after a whole number of periods. -/
theorem loop_add_nat (x : ℝ) (j : ℕ) : γ (x + j) = γ x := by
  simpa only [mul_one] using γ.periodic.nat_mul j x

/-- **The segments of the samples.** -/
theorem seg_eq {N : ℕ} [NeZero N] (hN : 1 < N)
    (hf : ∀ x : ℝ, SampleFacts M (ofSmooth (shift γ x)) N) (x : ℝ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) :
    M.sc (γ x) (γ (x + 1 / N)) τ = (γ (x + τ / N) : Ambient n) := by
  obtain ⟨hq, -, -, -, -, -, hbr⟩ := hf x
  have hNpos := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have ht : τ / N ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hτ.1 hN'.le, (div_le_one hN').mpr (hτ.2.trans (by exact_mod_cast hNpos))⟩
  have h : continuousRepresentative (polyLoop F M.seg hq) (τ / N) =
      continuousRepresentative (graphData (shift γ x)) (τ / N) := by
    have e := congrArg (fun u : SphereLoop n => (sphereRepresentative u ⟨τ / N, ht⟩ : Ambient n))
      (hbr hq)
    exact e
  rw [representative_polyLoop F M.seg hq ht, representative_graphData (shift γ x) ht] at h
  have hpiece : τ / N ∈ Icc (((0 : ℕ) : ℝ) / N) ((((0 : ℕ) : ℝ) + 1) / N) :=
    ⟨by simpa using ht.1, by
      rw [Nat.cast_zero, zero_add]
      exact div_le_div_of_nonneg_right hτ.2 hN'.le⟩
  unfold polyCurve at h
  rw [glue_eq_of_mem_Icc hNpos (fun j _ => edge_match F M.seg hq j) hpiece] at h
  unfold edgeCurve at h
  have h0 : samplePoly N (ofSmooth (shift γ x)) ((0 : ℕ) : ZMod N) = γ x := by
    apply Subtype.ext
    rw [samplePoly_shift_apply γ x, Nat.cast_zero, ZMod.val_zero, Nat.cast_zero, zero_div,
      zero_add]
  have h1 : samplePoly N (ofSmooth (shift γ x)) (((0 : ℕ) : ZMod N) + 1) = γ (x + 1 / N) := by
    apply Subtype.ext
    have : Fact (1 < N) := ⟨hN⟩
    rw [samplePoly_shift_apply γ x, Nat.cast_zero, zero_add, ZMod.val_one, Nat.cast_one,
      add_comm (1 / (N : ℝ)) x]
  rw [h0, h1, Nat.cast_zero, sub_zero, mul_div_cancel₀ τ hN'.ne'] at h
  rw [h]
  change (γ (τ / N + x) : Ambient n) = _
  rw [add_comm (τ / (N : ℝ)) x]

variable {N : ℕ} [NeZero N] (k : ℕ) {K : ℕ} [NeZero K]

/-- The values of the samples of the rotated iterate. -/
theorem sample_iterate_apply (hK : k * N = K) (a : ℝ) (i : ZMod K) :
    (samplePoly K (ofSmooth (shift (iterate γ k) a)) i : Ambient n) =
      γ ((i.val : ℝ) / N + k * a) := by
  rw [samplePoly_shift_apply (iterate γ k) a i]
  change (γ ((k : ℝ) * ((i.val : ℝ) / K + a)) : Ambient n) = _
  have hk : (k : ℝ) ≠ 0 := by
    have : k ≠ 0 := fun h => NeZero.ne K (by rw [← hK, h, zero_mul])
    exact_mod_cast this
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hKR : (K : ℝ) = k * N := by rw [← hK, Nat.cast_mul]
  congr 2
  rw [hKR]
  field_simp

/-- The values of the samples at the next index. -/
theorem sample_iterate_succ (hN : 1 < N) (hK : k * N = K) (a : ℝ) (i : ZMod K) :
    (samplePoly K (ofSmooth (shift (iterate γ k) a)) (i + 1) : Ambient n) =
      γ ((i.val : ℝ) / N + k * a + 1 / N) := by
  have hK1 : 1 < K := by
    rw [← hK]
    have hk : k ≠ 0 := fun h => NeZero.ne K (by rw [← hK, h, zero_mul])
    nlinarith [Nat.pos_of_ne_zero hk]
  have : Fact (1 < K) := ⟨hK1⟩
  rw [sample_iterate_apply γ k hK a, ZMod.val_add, ZMod.val_one]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hdm := Nat.div_add_mod (i.val + 1) K
  have hKR : (K : ℝ) = k * N := by rw [← hK, Nat.cast_mul]
  have e : ((i.val : ℝ) / N + k * a + 1 / N) =
      (((i.val + 1) % K : ℕ) : ℝ) / N + k * a + (((i.val + 1) / K * k : ℕ) : ℝ) := by
    have h1 : (i.val : ℝ) + 1 = (K : ℝ) * (((i.val + 1) / K : ℕ) : ℝ) +
        (((i.val + 1) % K : ℕ) : ℝ) := by
      exact_mod_cast hdm.symm
    rw [hKR] at h1
    rw [Nat.cast_mul]
    field_simp
    linear_combination h1
  rw [e, loop_add_nat]

/-- **The samples of the rotated iterates are short.** -/
theorem short_iterate (hN : 1 < N) (hf : ∀ x : ℝ, SampleFacts M (ofSmooth (shift γ x)) N)
    (hK : k * N = K) (a : ℝ) :
    ShortPolygon M.δ (samplePoly K (ofSmooth (shift (iterate γ k) a))) := by
  intro i
  rw [sample_iterate_succ γ k hN hK a, sample_iterate_apply γ k hK a]
  set x : ℝ := (i.val : ℝ) / N + k * a
  have h := (hf x).1 ((0 : ℕ) : ZMod N)
  have h0 : (samplePoly N (ofSmooth (shift γ x)) ((0 : ℕ) : ZMod N) : Ambient n) = γ x := by
    rw [samplePoly_shift_apply γ x, Nat.cast_zero, ZMod.val_zero, Nat.cast_zero, zero_div,
      zero_add]
  have h1 : (samplePoly N (ofSmooth (shift γ x)) (((0 : ℕ) : ZMod N) + 1) : Ambient n) =
      γ (x + 1 / N) := by
    have : Fact (1 < N) := ⟨hN⟩
    rw [samplePoly_shift_apply γ x, Nat.cast_zero, zero_add, ZMod.val_one, Nat.cast_one,
      add_comm (1 / (N : ℝ)) x]
  rw [h0, h1] at h
  exact h

/-- **The broken geodesics of the samples of the rotated iterates are the rotated iterates.** -/
theorem broken_iterate (hN : 1 < N) (hf : ∀ x : ℝ, SampleFacts M (ofSmooth (shift γ x)) N)
    (hK : k * N = K) (a : ℝ)
    (hq : ShortPolygon M.δ (samplePoly K (ofSmooth (shift (iterate γ k) a)))) :
    polySphereLoop F M.seg hq = ofSmooth (shift (iterate γ k) a) := by
  have hKpos := Nat.pos_of_neZero K
  have hK' : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hKR : (K : ℝ) = k * N := by rw [← hK, Nat.cast_mul]
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (polyLoop F M.seg hq) t =
    continuousRepresentative (graphData (shift (iterate γ k) a)) t
  rw [representative_polyLoop F M.seg hq t.2, representative_graphData _ t.2]
  have hj := pieceIdx_lt hKpos (t : ℝ)
  have hpiece := mem_piece hKpos t.2
  set j := pieceIdx K (t : ℝ) with hjdef
  unfold polyCurve
  rw [glue_eq_of_mem_Icc hj (fun i _ => edge_match F M.seg hq i) hpiece]
  unfold edgeCurve
  have hval : ((j : ZMod K)).val = j := ZMod.val_natCast_of_lt hj
  have e0 : samplePoly K (ofSmooth (shift (iterate γ k) a)) (j : ZMod K) =
      γ ((j : ℝ) / N + k * a) := by
    apply Subtype.ext
    rw [sample_iterate_apply γ k hK a, hval]
  have e1 : samplePoly K (ofSmooth (shift (iterate γ k) a)) ((j : ZMod K) + 1) =
      γ ((j : ℝ) / N + k * a + 1 / N) := by
    apply Subtype.ext
    rw [sample_iterate_succ γ k hN hK a, hval]
  have hloc : (K : ℝ) * t - j ∈ Icc (0 : ℝ) 1 := by
    have h1 := hpiece.1
    have h2 := hpiece.2
    rw [div_le_iff₀ hK'] at h1
    rw [le_div_iff₀ hK'] at h2
    constructor <;> linarith
  rw [e0, e1, seg_eq M γ hN hf _ hloc]
  change _ = (γ ((k : ℝ) * ((t : ℝ) + a)) : Ambient n)
  congr 2
  rw [hKR]
  field_simp
  ring

/-- **The samples of a rotated iterate are the iterates of a root polygon.** -/
theorem sample_eq_iterate (g : Finsler.Geodesics.ClosedGeodesic F) (s m : ℕ) [NeZero s]
    [NeZero m] (hK : m * (s * (2 * N)) = K) (a : ℝ) :
    amb (samplePoly K (ofSmooth (shift (iterate g.loop (s * m)) a))) =
      Finsler.LabelPack.reidx hK (iterA m (s * (2 * N))
        (amb (rootFamily g s N (((s * m : ℕ) : ℝ) * a)))) := by
  subst hK
  rw [Finsler.LabelPack.reidx_rfl]
  funext j
  have hK2 : (s * m) * (2 * N) = m * (s * (2 * N)) := by ring
  rw [iterA_apply]
  change (samplePoly (m * (s * (2 * N))) (ofSmooth (shift (iterate g.loop (s * m)) a)) j :
    Ambient n) = (iterate m (s * (2 * N)) (amb (rootFamily g s N (((s * m : ℕ) : ℝ) * a))) j)
  rw [sample_iterate_apply g.loop (s * m) hK2 a j]
  conv_rhs => rw [← ZMod.natCast_zmod_val j, iterate_natCast]
  unfold amb rootFamily
  rw [iterate_natCast, samplePoly_shift_apply g.loop, ZMod.val_natCast]
  have hdm := Nat.div_add_mod j.val (2 * N)
  have hN' : ((2 * N : ℕ) : ℝ) ≠ 0 := by
    have : 2 * N ≠ 0 := Nat.mul_ne_zero two_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have e : (j.val : ℝ) / ((2 * N : ℕ) : ℝ) + ((s * m : ℕ) : ℝ) * a =
      ((j.val % (2 * N) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) + ((s * m : ℕ) : ℝ) * a +
        ((j.val / (2 * N) : ℕ) : ℝ) := by
    have h1 : ((j.val : ℕ) : ℝ) = ((2 * N * (j.val / (2 * N)) + j.val % (2 * N) : ℕ) : ℝ) := by
      rw [hdm]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    rw [h1]
    push_cast
    field_simp
    ring
  rw [e, loop_add_nat]

/-- **The samples of a rotated root iterate are the root polygons.** -/
theorem sample_eq_root (g : Finsler.Geodesics.ClosedGeodesic F) (s : ℕ) [NeZero s] (a : ℝ) :
    amb (samplePoly (s * (2 * N)) (ofSmooth (shift (iterate g.loop s) a))) =
      amb (rootFamily g s N ((s : ℝ) * a)) := by
  funext j
  change (samplePoly (s * (2 * N)) (ofSmooth (shift (iterate g.loop s) a)) j : Ambient n) = _
  rw [sample_iterate_apply g.loop s (rfl : s * (2 * N) = s * (2 * N)) a j]
  conv_rhs => rw [← ZMod.natCast_zmod_val j]
  unfold amb rootFamily
  rw [iterate_natCast, samplePoly_shift_apply g.loop, ZMod.val_natCast]
  have hdm := Nat.div_add_mod j.val (2 * N)
  have e : (j.val : ℝ) / ((2 * N : ℕ) : ℝ) + (s : ℝ) * a =
      ((j.val % (2 * N) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) + (s : ℝ) * a +
        ((j.val / (2 * N) : ℕ) : ℝ) := by
    have h1 : ((j.val : ℕ) : ℝ) = ((2 * N * (j.val / (2 * N)) + j.val % (2 * N) : ℕ) : ℝ) := by
      rw [hdm]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
    rw [h1]
    push_cast
    field_simp
    ring
  rw [e, loop_add_nat]

end

end Finsler.CircleSampling
