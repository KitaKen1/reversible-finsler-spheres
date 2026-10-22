module

public import Finsler.Geometry.PolygonRefineGeneral
public import Finsler.Geometry.PolygonRoots

/-! The iteration data of a closed geodesic. For a closed geodesic the polygons of 2 N samples
at all phases are short for any prescribed radius as soon as N is large, uniformly in the
phase. Since the nullities and the indices of the iterates of these polygons do not depend on
the phase nor on the number of samples, the closed geodesic has an index function I, a nullity
function ν on the divisors of a period L ≥ 1, and a mean index Δ ≥ 0 such that
|I(m + k) - I(m) - I(k)| ≤ n, |I(m) - m Δ| ≤ n, ν ≤ 2 n, and such that for every radius δ > 0
and all large N the polygon q of 2 N samples at any phase is δ-short, has no zero edges, is
stationary, and the k-fold iterate of the d-fold iterate of q has nullity ν(gcd(d k, L)) and
index I(d k). In particular, if gcd(d k, L) = gcd(d, L), the k-fold iterate of the d-fold
iterate has the nullity of the d-fold iterate at every phase and for every large number of
samples, with one period L for the whole critical circle. -/

@[expose] public section

namespace Finsler.GeodesicIteration

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PolygonChart Finsler.PolygonModel Finsler.PolygonHessian Finsler.PolygonIterate
open Finsler.PolygonIterateReduction Finsler.PolygonNullity Finsler.PolygonMonodromy
open Finsler.PolygonRefineIterate Finsler.EnergySphereSmooth Finsler.PolygonIndex
open Finsler.PolygonRoots Finsler.SmoothSobolev Finsler.SamplePhase Finsler.PhaseNullity
open Finsler.PolygonRefineGeneral
open Set Filter
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- The rotation by the phase zero is the loop. -/
theorem shift_zero (γ : Finsler.Loops.SmoothLoop n) : Finsler.Loops.shift γ 0 = γ := by
  apply Finsler.Loops.loop_ext
  intro t
  change γ (t + 0) = γ t
  rw [add_zero]

variable {F : ReversibleMetric n}

/-- The polygons of samples of the rotations of a closed geodesic are short for any radius,
uniformly in the phase. -/
theorem exists_short_all (g : Finsler.Geodesics.ClosedGeodesic F) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K₀ : ℕ, ∀ a : ℝ, ∀ K : ℕ, K₀ ≤ K → ∀ [NeZero K],
      ShortPolygon δ (samplePoly K (ofSmooth (Finsler.Loops.shift g.loop a))) := by
  obtain ⟨N₁, hN₁⟩ := exists_sample_spacing F (δ := δ)
    (a := energy F (ofSmooth g.loop) + 1) hδ
  refine ⟨N₁, fun a K hK _ => ?_⟩
  have hE0 : 0 ≤ energy F (ofSmooth g.loop) := energy_nonneg F _
  have hEu : energy F (ofSmooth (Finsler.Loops.shift g.loop a)) <
      (energy F (ofSmooth g.loop) + 1) ^ 2 := by
    rw [energy_ofSmooth_shift]
    nlinarith
  exact shortPolygon_samplePoly F (fun u hu s t hs ht hst =>
    hN₁ K hK (Nat.pos_of_neZero K) u hu s t hs ht hst) hEu

/-- **The iteration data of a closed geodesic.** A closed geodesic has an index function I, a
nullity function ν, a mean index Δ ≥ 0 and a period L ≥ 1 with
|I(m + k) - I(m) - I(k)| ≤ n, |I(m) - m Δ| ≤ n and ν(gcd(m, L)) ≤ 2 n, such that for every
δ > 0 and all large N the polygon of 2 N samples at any phase is δ-short, without zero edges
and stationary, its m-fold iterate has nullity ν(gcd(m, L)) and index I(m), and the k-fold
iterate of its d-fold iterate has nullity ν(gcd(d k, L)) and index I(d k). -/
theorem exists_iteration_data (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ (I ν : ℕ → ℕ) (Δ : ℝ) (L : ℕ), 0 ≤ Δ ∧ 1 ≤ L ∧
      (∀ m k, 1 ≤ m → 1 ≤ k → I (m + k) ≤ I m + I k + n ∧ I m + I k ≤ I (m + k) + n) ∧
      (∀ m, 1 ≤ m → |(I m : ℝ) - m * Δ| ≤ n) ∧
      (∀ m, 1 ≤ m → ν (Nat.gcd m L) ≤ 2 * n) ∧
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (a : ℝ),
        ShortPolygon δ (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))) ∧
        (∀ i, samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)) (i + 1) ≠
          samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)) i) ∧
        PolyCritical F (2 * N) (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))) ∧
        (∀ (m : ℕ) [NeZero m],
          nullity F (iterate m (2 * N)
            (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) =
              ν (Nat.gcd m L) ∧
          ∀ hs : (hessian F (iterate m (2 * N) (samplePoly (2 * N)
              (ofSmooth (Finsler.Loops.shift g.loop a))))).toLinearMap.IsSymmetric,
            index F (iterate m (2 * N)
              (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) hs = I m) ∧
        ∀ (d k : ℕ) [NeZero d] [NeZero k],
          nullity F (iterate k (d * (2 * N)) (iterate d (2 * N)
            (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))))) =
              ν (Nat.gcd (d * k) L) ∧
          ∀ hs : (hessian F (iterate k (d * (2 * N)) (iterate d (2 * N) (samplePoly (2 * N)
              (ofSmooth (Finsler.Loops.shift g.loop a)))))).toLinearMap.IsSymmetric,
            index F (iterate k (d * (2 * N)) (iterate d (2 * N)
              (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))))) hs =
                I (d * k) := by
  obtain ⟨M⟩ := exists_segmentData F
  obtain ⟨K₀, hK₀⟩ := exists_sample_facts_all M g
  obtain ⟨K₁, hK₁⟩ := exists_nullity_sample_invariance g
  obtain ⟨K₂, hK₂⟩ := exists_phase_invariance g
  obtain ⟨K₃, hK₃⟩ := exists_iterIndex_sample_eq g
  obtain ⟨δ₁, hδ₁, hper⟩ := PolygonMonodromy.exists_nullity_period F
  obtain ⟨δ₂, hδ₂, hnul⟩ := PolygonTwist.exists_nullity_le F
  obtain ⟨K₄, hK₄⟩ := exists_short_all g (lt_min hδ₁ hδ₂)
  -- the reference polygon
  obtain ⟨R, hR₀, hR₁, hR₂, hR₃, hR₄, hR1⟩ :
      ∃ R : ℕ, K₀ ≤ R ∧ K₁ ≤ R ∧ K₂ ≤ R ∧ K₃ ≤ R ∧ K₄ ≤ R ∧ 1 ≤ R :=
    ⟨K₀ + K₁ + K₂ + K₃ + K₄ + 1, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hRne : NeZero R := ⟨by omega⟩
  have hR2 : R ≤ 2 * R := Nat.le_mul_of_pos_left R two_pos
  obtain ⟨hqR, hneR, -, htwR, hcR, -, -⟩ := hK₀ 0 (2 * R) (hR₀.trans hR2)
  have hshR := hK₄ 0 (2 * R) (hR₄.trans hR2)
  obtain ⟨L, hL, ⟨ν, hν⟩, -⟩ := hper (2 * R)
    (samplePoly (2 * R) (ofSmooth (Finsler.Loops.shift g.loop 0)))
    (fun i => (hshR i).trans_le (min_le_left _ _)) hneR
  obtain ⟨Δ, hΔ, hmean⟩ := PolygonIndex.exists_mean F
    (samplePoly (2 * R) (ofSmooth (Finsler.Loops.shift g.loop 0)))
  refine ⟨iterIndex F (samplePoly (2 * R) (ofSmooth (Finsler.Loops.shift g.loop 0))), ν, Δ, L,
    hΔ, hL, fun m k hm hk => ⟨iterIndex_add_le F _ hm hk, le_iterIndex_add F _ hm hk⟩, hmean,
    ?_, ?_⟩
  · intro m hm
    have hmne : NeZero m := ⟨by omega⟩
    rw [← hν m]
    exact hnul (m * (2 * R)) _
      (shortPolygon_iterate m (2 * R) fun i => (hshR i).trans_le (min_le_right _ _))
      (iterate_ne m (2 * R) hneR)
  · intro δ hδ
    obtain ⟨K₅, hK₅⟩ := exists_short_all g hδ
    refine ⟨R + K₅, fun N hN _ a => ?_⟩
    have hNR : R ≤ N := by omega
    have hN2 : N ≤ 2 * N := Nat.le_mul_of_pos_left N two_pos
    obtain ⟨hq, hne, -, htw, hc, -, -⟩ := hK₀ a (2 * N) (by omega)
    obtain ⟨hq0, hne0, -, -, -, -, -⟩ := hK₀ 0 (2 * N) (by omega)
    have hnull : ∀ (m : ℕ) [NeZero m], nullity F (iterate m (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) = ν (Nat.gcd m L) := by
      intro m _
      rw [hK₁ N R (by omega) hR₁ m a 0, hν m]
    have hidx : ∀ m : ℕ, 1 ≤ m →
        iterIndex F (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))) m =
          iterIndex F (samplePoly (2 * R) (ofSmooth (Finsler.Loops.shift g.loop 0))) m := by
      intro m hm
      have hmne : NeZero m := ⟨by omega⟩
      have hsa := hessian_isSymmetric F M.smooth (shortPolygon_iterate m (2 * N) hq)
        (iterate_ne m (2 * N) hne)
      have hs0 := hessian_isSymmetric F M.smooth (shortPolygon_iterate m (2 * N) hq0)
        (iterate_ne m (2 * N) hne0)
      have h1 := (hK₂ N (by omega) m a 0).2 hsa hs0
      rw [iterIndex_eq F M.smooth hq hne m hsa, iterIndex_eq F M.smooth hq0 hne0 m hs0] at h1
      have h2 := hK₃ (2 * R) (2 * N) (by omega) (by omega) m hm
      rw [← shift_zero g.loop] at h2
      rw [h1]
      exact h2
    refine ⟨hK₅ a (2 * N) (by omega), hne, hc, fun m _ => ⟨hnull m, fun hs => ?_⟩,
      fun d k _ _ => ⟨?_, fun hs => ?_⟩⟩
    · rw [iterIndex_eq F M.smooth hq hne m hs]
      exact hidx m (Nat.pos_of_neZero m)
    · rw [PolygonMonodromy.nullity_iterate_iterate F M.smooth hq hne htw d k,
        ← PolygonMonodromy.nullity_iterate (d * k) F M.smooth hq hne htw]
      exact hnull (d * k)
    · rw [index_iterate_iterate F M.smooth hq hne d k hs]
      exact hidx (d * k) (Nat.mul_pos (Nat.pos_of_neZero d) (Nat.pos_of_neZero k))

/-- **One period for the whole critical circle.** With the period L of the closed geodesic: if
gcd(d k, L) = gcd(d, L), then for all large N and every phase the k-fold iterate of the d-fold
iterate of the polygon of 2 N samples has the nullity of the d-fold iterate. -/
theorem exists_uniform_period (g : Finsler.Geodesics.ClosedGeodesic F) :
    ∃ (L N₀ : ℕ), 1 ≤ L ∧ ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] (a : ℝ) (d k : ℕ) [NeZero d]
      [NeZero k], Nat.gcd (d * k) L = Nat.gcd d L →
      nullity F (iterate k (d * (2 * N)) (iterate d (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a))))) =
      nullity F (iterate d (2 * N)
        (samplePoly (2 * N) (ofSmooth (Finsler.Loops.shift g.loop a)))) := by
  obtain ⟨I, ν, Δ, L, -, hL, -, -, -, hdata⟩ := exists_iteration_data g
  obtain ⟨N₀, hN₀⟩ := hdata 1 one_pos
  refine ⟨L, N₀, hL, fun N hN _ a d k _ _ hg => ?_⟩
  obtain ⟨-, -, -, h1, h2⟩ := hN₀ N hN a
  rw [(h2 d k).1, (h1 d).1, hg]

end

end Finsler.GeodesicIteration
